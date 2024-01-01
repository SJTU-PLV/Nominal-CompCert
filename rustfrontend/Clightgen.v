Require Import Coqlib.
Require Import Errors.
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

Parameter first_unused_ident: unit -> ident.

Local Open Scope gensym_monad_scope.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

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

Definition get_variant_tag (ce: Ctypes.composite_env) (id:ident) :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some tag
      | _, _ => None
      end
  | _ => None
  end.

Definition get_variant_body (ce: Ctypes.composite_env) (id:ident) :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some body
      | _, _ => None
      end
  | _ => None
  end.

          

Fixpoint expr_to_cexpr (ce: Ctypes.composite_env) (e: expr) : option Clight.expr :=
  match e with
  | Econst_int i ty => Some (Clight.Econst_int i (to_ctype ty))
  | Econst_float f ty => Some (Clight.Econst_float f (to_ctype ty))
  | Econst_single f ty => Some (Clight.Econst_single f (to_ctype ty))
  | Econst_long l ty => Some (Clight.Econst_long l (to_ctype ty))
  | Eplace _ p _ => Some (place_to_cexpr p)
  | Eget _ p fid ty =>
      (** FIXME: how to translate the get expression? *)
      match typeof_place p with
      | Tvariant id _ =>
          match get_variant_body ce id with
          | Some id' =>
              Some (Efield (Efield (place_to_cexpr p) id' (Ctypes.Tstruct id noattr)) fid (to_ctype ty))
          | _ => None
          end
      | _ => None
      end
  | Ecktag p fid ty =>
      (** TODO: how to get the tagz from ctypes composite env? or still use Rust composite env? *)      
      (* match typeof_place p with *)
      (* | Tvariant id _ => *)
      (*     match get_variant_body ce id,  with *)
      (*     | Some tagid => *)
      (*         Some (Ebinop Oeq (Efield (place_to_cexpr p) tagid type_int32s)  *)
      (* Ebinop Oeq (Efield (place_to_cexpr) *)
      None
  | Etempvar id ty =>
      Some (Clight.Etempvar id (to_ctype ty))
  | Eunop uop e ty =>
      match expr_to_cexpr ce e with
      | Some e' =>                          
          Some (Clight.Eunop uop e' (to_ctype ty))
      | None => None
      end
  | Ebinop binop e1 e2 ty =>
      match expr_to_cexpr ce e1, expr_to_cexpr ce e2 with
      | Some e1', Some e2' =>
          Some (Clight.Ebinop binop e1' e2' (to_ctype ty))
      | _, _ => None
      end
  end.

Section MALLOC_FREE.
  
Variable (malloc_id free_id: ident).

Fixpoint transl_boxexpr (ce: Ctypes.composite_env) (be: boxexpr) : mon (list Clight.statement * Clight.expr) :=
  match be with
  | Box be' =>
      (* transl(be') -> (stmts, e);
         temp = malloc(sz);
         *temp = e;
         temp *)
      do (stmts, e) <- transl_boxexpr ce be';
      let ty := to_ctype (typeof_boxexpr be) in
      let ty' := Clight.typeof e in
      do temp <- gensym ty;
      let sz := Ctypes.sizeof ce ty' in
      let tempvar := Clight.Etempvar temp ty in
      let malloc := (Evar malloc_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer ty' noattr) Ctypes.Tnil) (Tpointer ty' noattr) cc_default)) in
      let sz_expr := Clight.Econst_int (Int.repr sz) Ctypes.type_int32s in
      let call_malloc:= (Clight.Scall (Some temp) malloc (sz_expr :: nil)) in
      let assign_deref_temp := Clight.Sassign (Ederef tempvar ty') e in
      ret (stmts ++ (call_malloc :: assign_deref_temp :: nil), tempvar)
  | Bexpr e =>
      match expr_to_cexpr ce e with
      | Some e' =>
          ret (nil, e')
      | None =>
          error (msg "Error in transl_boxexpr")
      end
  end.

Fixpoint makeseq_rec (s: Clight.statement) (l: list Clight.statement) : Clight.statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Clight.Ssequence s s') l'
  end.

Definition makeseq (l: list Clight.statement) : Clight.statement :=
  makeseq_rec Clight.Sskip l.

Section STMT_FROM_EB.

Variable ce: Ctypes.composite_env.
  
Variable extended: PMap.t bool.

Variable unvisited: PMap.t bool.

Variable label_of_node : positive -> label.

Variable dropm: PTree.t ident.  (* map from composite id to its drop glue id *)

Definition encounter_extended_block (n: node) (stmt: Clight.statement) (f: node -> mon (option node * Clight.statement)) :=
  if extended!!n then
    if unvisited!!n then
      ret (Some n, stmt)
    else
      ret (None, (Clight.Ssequence stmt (Clight.Sgoto (label_of_node n))))
  else
    do (r, s) <- f n;
    ret (r, Clight.Ssequence stmt s).


(* return the next extened basic block (TODO: Is there always no more
than one extended basic block) and the constructed statement *)

Fixpoint build_stmt_until_extended_block (fuel: nat) (code: PTree.t statement) (pc: node) : mon (option node * Clight.statement) :=
  match fuel with
  | O => error (msg "Running out of fuel in: build_stmt_until_extended_block")
  | S fuel' =>
  let build_rec := build_stmt_until_extended_block fuel' code in
  match code!pc with
  | None => error (msg "Invalid control flow graph: build_stmt_until_extened_block")
  | Some stmt =>
      match stmt with
      | Sifthenelse e n1 n2 =>
          (* check if n1 and n2 are extened blocks *)
          do (r1, s1) <-
               (if extended!!n1 then
                  if unvisited!!n1 then
                    error (msg "Body entry of if statement has extened block: build_stmt_until_extened_block")                                       
                  else
                    ret (None, Sgoto (label_of_node n1))
                else
                  build_stmt_until_extended_block fuel' code n1);
          do (r2, s2) <-
               (if extended!!n2 then
                  if unvisited!!n2 then
                    error (msg "Body entry of if statement has extened block: build_stmt_until_extened_block")
                  else
                    ret (None, Sgoto (label_of_node n2))
                else
                  build_stmt_until_extended_block fuel' code n2);
          match expr_to_cexpr ce e with
          | None => error (msg "Translate expr in Sifthenelse incurs errors: build_stmt_until_extended_block")
          | Some e' =>              
          match r1,r2 with
          | Some r1, Some r2 =>              
              (* pc - n1 -* r2 
                    - n2 -* r1 *)  
              if Pos.eqb r1 r2 then
                ret (Some r1, Clight.Sifthenelse e' s1 s2)
              else 
                error (msg "Two case of if statement renach two different blocks: build_stmt_until_extened_block")
          | Some r1, None =>
              ret (Some r1, Clight.Sifthenelse e' s1 s2)
          | None, Some r2 =>
              ret (Some r2, Clight.Sifthenelse e' s1 s2)
          | None, None =>
              ret (None, Clight.Sifthenelse e' s1 s2)
          end
          end
      | Sskip n =>
          encounter_extended_block n Clight.Sskip build_rec
      | Sassign p be n =>
          (* a = Box(Box(12)) would be translated to:
             temp1 = malloc(sizeof(int));
             *temp1 = 12;
             temp2 = malloc(sizeof(Box));
             *temp2 = temp1;
             a = temp2 *)
          do (ls, e') <- transl_boxexpr ce be;
          let stmt' := (Clight.Ssequence (makeseq ls) (Clight.Sassign (place_to_cexpr p) e')) in
          encounter_extended_block n stmt' build_rec
      | Sset id e n =>
          do e' <-
               match expr_to_cexpr ce e with
               | None => error (msg "Translate expr in Sset incurs errors: build_stmt_until_extended_block")
               | Some e' => ret e'
               end;
          let stmt' := Clight.Sset id e' in
          encounter_extended_block n stmt' build_rec
      | Scall optp e el n =>
          (* temp = call(el');
             p = temp *)
          do el' <- fold_right (fun elt acc =>
                                  do acc' <- acc;
                                  match expr_to_cexpr ce elt with
                                  | None => error (msg "Translate expr list in Sset incurs errors: build_stmt_until_extended_block")
                                  | Some e' => ret (e' :: acc')
                                  end) (ret nil) el;
          do stmt' <-
               match optp, expr_to_cexpr ce e with
               | Some p, Some e' =>
                   let pe := place_to_cexpr p in
                   let ty := (Clight.typeof pe) in
                   do temp <- gensym ty;
                   let stmt' := Clight.Scall (Some temp) e' el' in
                   ret (Clight.Ssequence stmt' (Clight.Sassign pe (Clight.Etempvar temp ty)))
               | None, Some e' =>
                   let stmt' := Clight.Scall None e' el' in
                   ret stmt'
               | _, _ =>
                   error (msg "Translate function expr in Sset incurs errors: build_stmt_until_extended_block")
               end;
          encounter_extended_block n stmt' build_rec                
      | Sreturn opte =>
          match opte with
          | Some e =>
              match expr_to_cexpr ce e with
              | Some e' => ret (None, Clight.Sreturn (Some e'))
              | None => error (msg "Translate return expr in Sset incurs errors: build_stmt_until_extended_block")
              end
          | None =>
              ret (None, Clight.Sreturn None)
          end
      | Sstoragelive _ n
      | Sstoragedead _ n =>
          encounter_extended_block n Clight.Sskip build_rec
      | Sdrop p n =>  error (msg "Unsupported")
      end
  end
  end.


(* Fixpoint expand_drop (temp: ident) (ty: type) := *)
(*   match ty with *)
(*   | Tbox ty' attr => *)
      

Fixpoint transl_extened_block (fuel: nat) (code: PTree.t statement) (pc: node)  : mon Clight.statement :=
  match fuel with
  | O => error (msg "Running out of fuel in transl_extended_block")
  | S fuel' =>
      let unvisited' := PMap.set pc false unvisited in
      do (optnext, stmt) <- build_stmt_until_extended_block (PTree_Properties.cardinal code) code pc;
      let label_stmt := Slabel (label_of_node pc) in
      match optnext with
      | Some next =>
          do stmt' <- transl_extened_block fuel' code next;
          ret (label_stmt (Clight.Ssequence stmt stmt'))
      | None =>
          ret (label_stmt stmt)
      end
  end.
              
          
End STMT_FROM_EB.


Definition make_extened_basic_block (entry: node) (preds: PTree.t (list positive)) : PTree.t bool :=
  PTree.fold (fun acc pc elt =>
                if peq pc entry then PTree.set pc true acc else
                  match preds!!!pc with
                  | nil => PTree.set pc false acc
                  | s :: nil =>
                      if peq s pc then PTree.set pc true acc else PTree.set pc false acc
                  | _ :: _ :: _ =>
                      PTree.set pc true acc
                  end) preds (PTree.empty bool).

Local Open Scope error_monad_scope.

(* top level translation *)
Fixpoint transl_function (ce: Ctypes.composite_env) (f: function) : res Clight.function :=
  (** FIXME: we use first_unused_ident from CamlCoq.ml to get a fresh identifier  *)
  (* let vars := var_names (f.(fn_vars) ++ f.(fn_params) ++ f.(fn_temps)) in *)
  (* let next_temp := Pos.succ (fold_left Pos.max vars 1%positive) in *)
  let gen := initial_generator tt in
  (* compute the extended blocks *)
  let preds := make_predecessors f.(fn_body) successors in
  let extended := make_extened_basic_block f.(fn_entryblock) preds in
  let unvisited := extended in
  (** FIXME: for now we just use identity function as the label_of_node *)
  match transl_extened_block ce (false, extended) (false, unvisited) id (PTree_Properties.cardinal f.(fn_body)) f.(fn_body) f.(fn_entryblock) gen with
  | Err msg => Error msg
  | Res tbody g _ =>
      let params := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) in
      let vars := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) in
      OK (Clight.mkfunction
              (to_ctype f.(fn_return))
              f.(fn_callconv)
              params
              vars
              g.(gen_trail)
              tbody)
  end.


Definition transl_fundef (ce: Ctypes.composite_env) (id: ident) (fd: fundef) : res Clight.fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function ce f;
      OK (Ctypes.Internal tf)
  | External _ ef targs tres cconv =>
      OK (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv)
  end.


(** ** Translate the composite definitions *)

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
      let tag_member := Ctypes.Member_plain tag_fid type_int32s in
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



(** ** Generate drop glue for each composite with ownership type *)

Section COMPOSITE_ENV.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.

Definition free_fun_expr (ty: Ctypes.type) : Clight.expr :=
  let argty := (Ctypes.Tpointer ty noattr) in
  Evar free_id (Ctypes.Tfunction (Ctypes.Tcons argty Ctypes.Tnil) Ctypes.Tvoid cc_default).

(* return [free(arg)], ty is the type arg points to, i.e. [arg: *ty] *)
Definition call_free (ty: Ctypes.type) (arg: Clight.expr) : Clight.statement :=
  Clight.Scall None (free_fun_expr ty) (arg :: nil).

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
          let call_stmt := Clight.Scall None (Evar free_id glue_ty) ((Eaddrof arg ref_arg_ty) :: nil) in
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
                          

(* Translation of a whole program *)

Definition transl_globvar (id: ident) (ty: type) := OK (to_ctype ty).

 Definition transl_program (p: program) : res Clight.program :=
  do co_defs <- transl_composites p.(prog_types);
  (* generate drop glue for ownership type *)
  do (drops, m) <- generate_drops p.(prog_types);
  (** TODO: need a drop glue map in transl_fundef *)
  let ce := Ctypes.build_composite_env co_defs in
  (match ce as m return (ce = m) -> res Clight.program with
   | OK ce =>            
       fun Hyp =>
         do p1 <- transform_partial_program2 (transl_fundef ce) transl_globvar p;
         OK {| Ctypes.prog_defs := AST.prog_defs p1 ++ drops;
              Ctypes.prog_public := AST.prog_public p1;
              Ctypes.prog_main := AST.prog_main p1;
              Ctypes.prog_types := co_defs;
              Ctypes.prog_comp_env := ce;
              Ctypes.prog_comp_env_eq := Hyp |}
   | Error msg => fun _ => Error msg
   end) (eq_refl ce).
 
