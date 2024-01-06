Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Kildall.
Require Import Clight.
Require Import RustlightBase RustIR.
Require Import Errors.

(** The generation from RustIR to Clight contains three steps:
1. translate the rust composite type (e.g., variant) to C composite
(variant is represented by a structure where the first field is tag
and the second is an union); 2. generate drop glue (function) for each
composite type which is movabl; 3. translate the RustIR statement to
Clight statement, while translating the drop to call free and box
construction to call malloc. *)


Local Open Scope error_monad_scope.

(** ** Step 1: Translate composite definitions *)

Parameter first_unused_ident: unit -> ident.

Definition transl_composite_member (m: member) : Ctypes.member :=
  match m with
  | Member_plain fid ty =>
      Ctypes.Member_plain fid (to_ctype ty)
  end.
          
(* Variant {a, b, c} => Struct {tag_fid: int; union_fid: {a,b,c}} *)
Definition transl_composite_def (union_map: PTree.t (ident * attr)) (co: composite_definition) :res Ctypes.composite_definition :=
  match co with
  | Composite id Struct ms attr =>
      OK (Ctypes.Composite id Ctypes.Struct (map transl_composite_member ms) attr)
  | Composite id TaggedUnion ms attr =>
      (* generate a Struct with two fields, one for the tag field and
      the other for the union *)
      let tag_fid := first_unused_ident tt in
      let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
      let union_fid := first_unused_ident tt in
      match union_map ! id with
      | Some (id',attr) =>
          let union_member := Ctypes.Member_plain tag_fid (Tunion id' attr) in
          (** TODO: specify the attribute *)
          OK (Ctypes.Composite id Ctypes.Struct (tag_member :: union_member :: nil) noattr)
      | _ =>
          Error (msg "No corresponded union for the variant: transl_composite_def")
      end
  end.


Definition variant_to_union (co: composite_definition) : option (Ctypes.composite_definition * (ident * (ident * attr))) :=
  match co with
  | Composite id Struct ms attr => None
  | Composite id TaggedUnion ms attr =>
      let union_id := first_unused_ident tt in
      (** TODO: specify the attr  *)
      Some ((Ctypes.Composite union_id Union (map transl_composite_member ms) noattr), (id,(union_id, noattr)))
  end.


Definition transl_composites (l: list composite_definition) : res (list Ctypes.composite_definition) :=
  (* generate an union definition for each variant *)
  let (unions, idpairs) := split (fold_right (fun elt acc => match variant_to_union elt with
                                        | Some co_id => co_id :: acc
                                        | None => acc
                                        end) nil l) in
  let union_map := fold_left (fun acc elt => PTree.set (fst elt) (snd elt) acc) idpairs (PTree.empty (ident * attr)) in
  (* translate rust composite to C composite *)
  do composites <- fold_right (fun elt acc => do acc' <- acc;
                                          do def <- transl_composite_def union_map elt;
                                          OK (def :: acc')) (OK nil) l;
  OK (composites ++ unions).



(** ** Step 2: Generate drop glue for each composite with ownership type *)


Fixpoint makeseq_rec (s: Clight.statement) (l: list Clight.statement) : Clight.statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Clight.Ssequence s s') l'
  end.

Definition makeseq (l: list Clight.statement) : Clight.statement :=
  makeseq_rec Clight.Sskip l.


(* To specify *)
Parameter (malloc_id free_id: ident).

Definition free_fun_expr (ty: Ctypes.type) : Clight.expr :=
  let argty := (Ctypes.Tpointer ty noattr) in
  Evar free_id (Ctypes.Tfunction (Ctypes.Tcons argty Ctypes.Tnil) Ctypes.Tvoid cc_default).

(* return [free(arg)], ty is the type arg points to, i.e. [arg: *ty] *)
Definition call_free (ty: Ctypes.type) (arg: Clight.expr) : Clight.statement :=
  Clight.Scall None (free_fun_expr ty) (arg :: nil).


Section COMPOSITE_ENV.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.


Fixpoint drop_glue_for_type (m: PTree.t ident) (arg: Clight.expr) (ty: type) : list Clight.statement :=
  match ty with
  | Tbox ty' attr =>
      let cty' := (to_ctype ty') in
      (* free(arg) *)
      let stmt := call_free cty' arg in
      (* return [free(arg); free(deref arg); ...] *)
      stmt :: drop_glue_for_type m (Ederef arg cty') ty'
  | Tstruct id attr
  | Tvariant id attr =>
      match m ! id with
      | None => nil
      | Some id' =>
          (* call the drop glue of this struct: what is the type of this drop glue ? *)
          let ref_arg_ty := (Ctypes.Tpointer (to_ctype ty) noattr ) in
          let glue_ty := Ctypes.Tfunction (Ctypes.Tcons ref_arg_ty Ctypes.Tnil) Tvoid cc_default in
          (* drop_in_place_xxx(&arg) *)
          let call_stmt := Clight.Scall None (Evar id' glue_ty) ((Eaddrof arg ref_arg_ty) :: nil) in
          call_stmt :: nil
      end
  | _ => nil
  end.
            
(* Some example: 
drop_in_place_xxx(&Struct{a,b,c} param) {
    drop_in_place_a(&((deref param).a));
    drop_in_place_a(&((deref param).b));
    drop_in_place_a(&((deref param).c));
} *)

(* we assume deref_param is the dereference of the parameter *)
Definition drop_glue_for_member (m: PTree.t ident) (deref_param: Clight.expr) (memb: member) : list Clight.statement :=
  match memb with
  | Member_plain fid ty =>      
      if own_type own_fuel ce ty then
        let cty := (to_ctype ty) in
        let arg := Efield deref_param fid cty in
        drop_glue_for_type m arg ty
      else
        nil
  end.
        
Definition make_labelled_stmts (drops_list: list (list Clight.statement)) :=
  let branch idx elt ls := LScons (Some idx) (Clight.Ssequence (makeseq elt) Clight.Sbreak) ls in
  fold_right
    (fun elt acc => let '(idx, ls) := acc in (idx-1, branch idx elt ls))
    ((list_length_z drops_list) - 1, LSnil) drops_list.

(* m: maps composite id to drop function id *)
Definition drop_glue_for_composite (m: PTree.t ident) (co: composite_definition) : res (option Clight.function) :=
  (* The only function parameter *)
  let param := first_unused_ident tt in
  match co with
  | Composite co_id Struct ms attr =>
      let co_ty := (Ctypes.Tstruct co_id attr) in
      let param_ty := Tpointer co_ty noattr in
      let deref_param := Ederef (Evar param param_ty) co_ty in
      let stmt_list := fold_right (fun elt acc => drop_glue_for_member m deref_param elt ++ acc) nil ms in
      match stmt_list with
      | nil => OK None
      | _ =>
          (* generate function *)
          let stmt := (Clight.Ssequence (makeseq stmt_list) (Clight.Sreturn None)) in
          OK (Some (Clight.mkfunction Tvoid cc_default ((param, param_ty)::nil) nil nil stmt))
      end
  | Composite co_id TaggedUnion ms attr =>
      let co_ty := (Ctypes.Tstruct co_id attr) in
      let param_ty := Tpointer co_ty noattr in
      let deref_param := Ederef (Evar param param_ty) co_ty in
      (* check tag and then call corresponded drop glue *)
      match tce ! co_id with
      | Some tco =>
          match tco.(co_su), tco.(Ctypes.co_members) with
          | Ctypes.Struct, Ctypes.Member_plain tag_id tag_ty :: Ctypes.Member_plain union_id _ :: nil =>
              (* get tag expr *)
              let get_tag := Efield deref_param tag_id tag_ty in
              (* use switch statements to model the pattern match? *)
              (* drops_list is [[case 0: drop(m1)];[case 1: drop(m2)]]*)
              let drops_list := fold_right (fun elt acc => (drop_glue_for_member m deref_param elt) :: acc) (@nil (list Clight.statement)) ms in
              let (_, switch_branches) := make_labelled_stmts drops_list in
              (* generate function *)
              let stmt := (Clight.Sswitch get_tag switch_branches) in
              OK (Some (Clight.mkfunction Tvoid cc_default ((param, param_ty)::nil) nil nil stmt))
          | _, _ => Error (msg "Variant is not correctly converted to C struct: drop_glue_for_composite")
          end
      | _ => Error (msg "The conversion of variant does not exist in the C composite environment")
      end
  end.
                

(* take the ident of a composite and return the ident of the drop glue function *)
Parameter create_dropglue_ident : ident -> ident.

Definition drop_glue_globdef (f: Clight.function) : globdef (Ctypes.fundef Clight.function) Ctypes.type :=
  Gfun (Ctypes.Internal f).

(** Generate drop glue for each composite that is movable *)

(* also return the map from composite id to drop glue id *)
Definition generate_drops (l: list composite_definition) : res ((list (ident * globdef (Ctypes.fundef Clight.function) Ctypes.type)) * PTree.t ident) :=
  (* first build the mapping from composite id to function id *)
  let ids := map (fun elt => match elt with | Composite id _ _ _ => (id, create_dropglue_ident id) end) l in
  let m := fold_left (fun acc elt => PTree.set (fst elt) (snd elt) acc) ids (PTree.empty ident) in   
  (* how to construct the string of this fuction  *)        
  do globs <- fold_right (fun elt acc => do acc' <- acc;
                                     do glue <- drop_glue_for_composite m elt;
                                     match glue with
                                     | Some glue' => OK (drop_glue_globdef glue' :: acc')
                                     | _ => OK acc'
                                     end) (OK nil) l;
  OK ((combine (snd (split ids)) globs), m).
                          
End COMPOSITE_ENV.


(** ** Step 3: Translate the Rust statement to Clight statement  *)

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * Ctypes.type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.


Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.


Local Open Scope gensym_monad_scope.

Definition initial_generator (x: ident) : generator :=
  mkgenerator x nil.

Definition gensym (ty: Ctypes.type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).
  

Fixpoint place_to_cexpr (p: place) : Clight.expr :=
  match p with
  | Plocal id ty =>      
      Evar id (to_ctype ty)
  | Pfield p' fid ty =>
      Efield (place_to_cexpr p') fid (to_ctype ty)
  | Pderef p' ty =>
      Ederef (place_to_cexpr p') (to_ctype ty)
  end.

Definition get_variant_tag (ce: Ctypes.composite_env) (id:ident) : option ident :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some tag
      | _, _ => None
      end
  | _ => None
  end.

Definition get_variant_body (ce: Ctypes.composite_env) (id:ident) : option ident :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some body
      | _, _ => None
      end
  | _ => None
  end.


Section TRANSL.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.

Variable dropm: PTree.t ident.  (* map from composite id to its drop glue id *)

Fixpoint pexpr_to_cexpr (e: pexpr) : mon Clight.expr :=
  match e with
  | Econst_int i ty => ret (Clight.Econst_int i (to_ctype ty))
  | Econst_float f ty => ret (Clight.Econst_float f (to_ctype ty))
  | Econst_single f ty => ret (Clight.Econst_single f (to_ctype ty))
  | Econst_long l ty => ret (Clight.Econst_long l (to_ctype ty))
  | Eplace p _ => ret (place_to_cexpr p)
  | Eget p fid ty =>
      (** FIXME: how to translate the get expression? *)
      match typeof_place p with
      | Tvariant id _ =>
          match get_variant_body tce id with
          | Some id' =>
              (* p.id'.fid *)
              ret (Efield (Efield (place_to_cexpr p) id' (Ctypes.Tunion id noattr)) fid (to_ctype ty))
          | _ => error (msg "Cannot find the body of variant in C composite environment: expr_to_cexpr")
          end
      | _ => error (msg "Type error in Eget: expr_to_cexpr ")
      end
  | Ecktag p fid ty =>
      (** TODO: how to get the tagz from ctypes composite env? or still use Rust composite env? *)
      match typeof_place p with
      | Tvariant id _ =>
          match ce!id with
          | Some co =>
              match field_tag fid co.(co_members), get_variant_tag tce id with
              | Some tagz, Some tagid =>
                  ret (Clight.Ebinop Oeq (Clight.Efield (place_to_cexpr p) tagid Ctypes.type_int32s) (Clight.Econst_int (Int.repr tagz) Ctypes.type_int32s) Ctypes.type_bool)
              | _, _ => error (msg "Error in Ecktag 1: expr_to_cexpr")
              end
          | _ => error (msg "Error in Ecktag 2: expr_to_cexpr")
          end
      | _ => error (msg "Error in Ecktag 3, type error: expr_to_cexpr")
      end
  | Eunop uop e ty =>
      do e' <- pexpr_to_cexpr e;
      ret (Clight.Eunop uop e' (to_ctype ty))
  | Ebinop binop e1 e2 ty =>
      do e1' <- pexpr_to_cexpr e1;
      do e2' <- pexpr_to_cexpr e2;
      ret (Clight.Ebinop binop e1' e2' (to_ctype ty))
  end.

Definition expr_to_cexpr (e: expr) : mon Clight.expr :=
  match e with
  | Emoveplace p ty =>
      pexpr_to_cexpr (Eplace p ty)
  | Emoveget p fid ty =>
      pexpr_to_cexpr (Eget p fid ty)
  | Epure pe =>
      pexpr_to_cexpr pe
end.

(** Unused  *)
(* Fixpoint transl_boxexpr (be: boxexpr) : mon (list Clight.statement * Clight.expr) := *)
(*   match be with *)
(*   | Box be' => *)
(*       (* transl(be') -> (stmts, e); *)
(*          temp = malloc(sz); *)
(*          *temp = e; *)
(*          temp *) *)
(*       do (stmts, e) <- transl_boxexpr be'; *)
(*       let ty := to_ctype (typeof_boxexpr be) in *)
(*       let ty' := Clight.typeof e in *)
(*       do temp <- gensym ty; *)
(*       let sz := Ctypes.sizeof tce ty' in *)
(*       let tempvar := Clight.Etempvar temp ty in *)
(*       let malloc := (Evar malloc_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer ty' noattr) Ctypes.Tnil) (Tpointer ty' noattr) cc_default)) in *)
(*       let sz_expr := Clight.Econst_int (Int.repr sz) Ctypes.type_int32s in *)
(*       let call_malloc:= (Clight.Scall (Some temp) malloc (sz_expr :: nil)) in *)
(*       let assign_deref_temp := Clight.Sassign (Ederef tempvar ty') e in *)
(*       ret (stmts ++ (call_malloc :: assign_deref_temp :: nil), tempvar) *)
(*   | Bexpr e => *)
(*       do e' <- expr_to_cexpr e; *)
(*       ret (nil, e')      *)
(*   end. *)

Definition transl_Sbox (e: expr) : mon (list Clight.statement * Clight.expr) :=
  (* temp = malloc(sz);
     *temp = e;
     temp *)
  do e' <- expr_to_cexpr e;
  let e_ty := Clight.typeof e' in
  let temp_ty := Tpointer e_ty noattr in
  do temp <- gensym temp_ty;
  let sz := Ctypes.sizeof tce e_ty in
  let tempvar := Clight.Etempvar temp temp_ty in
  let malloc := (Evar malloc_id (Ctypes.Tfunction (Ctypes.Tcons Ctypes.type_int32s Ctypes.Tnil) temp_ty cc_default)) in
  let sz_expr := Clight.Econst_int (Int.repr sz) Ctypes.type_int32s in
  let call_malloc:= (Clight.Scall (Some temp) malloc (sz_expr :: nil)) in
  let assign_deref_temp := Clight.Sassign (Ederef tempvar e_ty) e' in
  ret ((call_malloc :: assign_deref_temp :: nil), tempvar).



(* expand drop_in_place(temp), temp is a reference, ty is the type of
[*temp]. It is different from drop_glue_for_type because the expansion
is in the caller side. We need to use the reference to build the call
statement *)
Definition expand_drop (temp: ident) (ty: type) : option Clight.statement :=
  match ty with
  (* drop a box only drop the memory it points to, we do not care
  about the point-to type *)
  | Tbox ty' attr =>
      (* free(cty (deref temp)), deref temp has type [cty] and [deref
      temp] points to type [cty'] *)      
      let cty := to_ctype ty in
      let cty' := to_ctype ty' in
      let deref_temp := Ederef (Clight.Etempvar temp (Tpointer cty noattr)) cty in
      Some (call_free cty' deref_temp)
  | Tstruct id attr
  | Tvariant id attr =>
      match dropm ! id with
      | None => None
      | Some id' =>
          (* temp has type [ref_cty] *)
          let ref_cty := Tpointer (to_ctype ty) noattr in
          let glue_ty := Ctypes.Tfunction (Ctypes.Tcons ref_cty Ctypes.Tnil) Tvoid cc_default in
          (* drop_in_place_xxx(temp) *)
          let call_stmt := Clight.Scall None (Evar id' glue_ty) ((Clight.Etempvar temp ref_cty) :: nil) in
          Some call_stmt
      end
  | _ => None
  end.


Fixpoint transl_stmt (stmt: statement) : mon Clight.statement :=
  match stmt with
  | Sskip => ret Clight.Sskip
  | Sassign p e =>      
      do e' <- expr_to_cexpr e;
      let assign := Clight.Sassign (place_to_cexpr p) e' in
      ret assign
  | Sbox p e =>
      (* temp = malloc(sizeof(e));
       *temp = e;
       p = temp *)       
      do (stmt, e') <- transl_Sbox e;
      ret (Clight.Ssequence (makeseq stmt) (Clight.Sassign (place_to_cexpr p) e'))
  | Sstoragelive _
  | Sstoragedead _ =>
      ret Clight.Sskip
  | Scall p e el =>
      do el' <- fold_right (fun elt acc =>
                             do acc' <- acc;
                             do e' <- expr_to_cexpr elt;
                             ret (e' :: acc')) (ret nil) el;
      do e' <- expr_to_cexpr e;
      (* temp = f();
         p = temp *)
      match p with
      | Some p =>
          let ty := typeof_place p in
          let cty := to_ctype ty in
          do temp <- gensym cty;
          let assign := Clight.Sassign (place_to_cexpr p) (Etempvar temp cty) in
          ret (Clight.Ssequence (Clight.Scall (Some temp) e' el') assign)
      | None =>
          ret (Clight.Scall None e' el')
      end
  | Ssequence s1 s2 =>
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Clight.Ssequence s1' s2')
  | Sifthenelse e s1 s2 =>
      do e' <- expr_to_cexpr e;
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Clight.Sifthenelse e' s1' s2')
  | Sloop s =>
      do s' <- transl_stmt s;
      ret (Clight.Sloop s' Clight.Sskip)
  | Sbreak =>
      ret Clight.Sbreak
  | Scontinue =>
      ret Clight.Scontinue
  | Sreturn e =>
      match e with
      | Some e =>
          do e' <- expr_to_cexpr e;
          ret (Clight.Sreturn (Some e'))
      | None =>
          ret (Clight.Sreturn None)
      end
  | Sdrop p =>
      (* drop(p) is expanded to
         temp = &p;
         drop_in_place(&temp)
       *)
      let ty := (typeof_place p) in
      let cty := (to_ctype ty) in
      let ref_cty := Tpointer cty noattr in
      do temp <- gensym ref_cty;
      (* [temp=&p] *)
      let set_stmt := Clight.Sset temp (Eaddrof (place_to_cexpr p) ref_cty) in
      match expand_drop temp ty with
      | Some drop_stmt =>
          ret (Clight.Ssequence set_stmt drop_stmt)          
      | None =>
          error (msg "Cannot find drop glue when expanding drop: build_stmt_until_extended_block")
      end
end.


(* step 3: translate a single function *)
Definition transl_function (f: function) : Errors.res Clight.function :=
  (** FIXME: we can use first_unused_ident from CamlCoq.ml to get a fresh identifier  *)
  let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
  let next_temp := Pos.succ (fold_left Pos.max vars 1%positive) in
  let gen := initial_generator next_temp in
  match transl_stmt f.(fn_body) gen with
  | Err msg => Errors.Error msg
  | Res stmt' g _ =>
      let params := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) in
      let vars := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) in
      Errors.OK (Clight.mkfunction
            (to_ctype f.(fn_return))
            f.(fn_callconv)
            params
            vars
            g.(gen_trail)
            stmt')
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef (_: ident) (fd: fundef) : Errors.res Clight.fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f;
      Errors.OK (Ctypes.Internal tf)
  | External _ ef targs tres cconv =>
      Errors.OK (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv)
  end.

End TRANSL.


(* Translation of a whole program *)

Definition transl_globvar (id: ident) (ty: type) := OK (to_ctype ty).

Local Open Scope error_monad_scope.

Definition transl_program (p: program) : res Clight.program :=
  (* step 1: rust composite to c composite: generate union for each variant *)
  do co_defs <- transl_composites p.(prog_types);  
  let tce := Ctypes.build_composite_env co_defs in
  (match tce as m return (tce = m) -> res Clight.program with
   | OK tce =>            
       fun Hyp =>
         let ce := p.(prog_comp_env) in
         (* step 2: generate drop glue *)
         do (drops, dropm) <- generate_drops ce tce p.(prog_types);
         (* step 3: translate the statement *)
         do p1 <- transform_partial_program2 (transl_fundef ce tce dropm) transl_globvar p;
         OK {| Ctypes.prog_defs := AST.prog_defs p1 ++ drops;
              Ctypes.prog_public := AST.prog_public p1;
              Ctypes.prog_main := AST.prog_main p1;
              Ctypes.prog_types := co_defs;
              Ctypes.prog_comp_env := tce;
              Ctypes.prog_comp_env_eq := Hyp |}
   | Error msg => fun _ => Error msg
   end) (eq_refl tce).

