Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Rustlight RustIR.
Require Import InitDomain InitAnalysis.

Import ListNotations.

Local Open Scope error_monad_scope.

(** Use the analysis from InitAnalysis.v to elaborate the drop
statements. After this pass, the ownership semantics is removed. The
memory deallocation would be explicit and deterministic *)

(** The drop elaboration has three steps: 1. Iterate the CFG to
collect drop flags for each drops; 2. During the iteration, update the
drops statement (from conditonally drop to deterministic drop) in
RustIR (AST); 3. Insert the update of the drop flag before the
occurence of ownership transfer *)

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  (* gen_next: ident; *)
  gen_trail: list (ident * type);
  gen_map: PMap.t (list (place * ident));
  gen_stmt: statement (* It is used for elaborating the drops when collecting drop flags *)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), (* Ple (gen_next g) (gen_next g') -> *) result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (* (Ple_refl (gen_next g)) *).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' => Res b g''
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


Parameter fresh_atom: unit -> ident.

(* for now we just use the maximum ident of parameters and variables
as the initial ident *)
Definition initial_generator (stmt: statement) : generator :=
  mkgenerator nil (nil, PTree.empty (list (place * ident))) stmt.

(* generate a new drop flag with type ty (always bool) and map [p] to this flag *)
Definition gensym (ty: type) (p: place) : mon ident :=
  let id := local_of_place p in
  let fresh_id := fresh_atom tt in
  fun (g: generator) =>
    Res fresh_id
      (mkgenerator
         ((fresh_id, ty) :: gen_trail g)
         (PMap.set id ((p, fresh_id) :: (gen_map g) !! id) (gen_map g))
         (gen_stmt g)).

Definition set_stmt (sel: selector) (stmt: statement) : mon unit :=
  fun (g: generator) =>
    match (update_stmt (gen_stmt g) sel stmt) with
    | Some stmt' =>
        Res tt
          (mkgenerator
             (gen_trail g)
             (gen_map g)
             stmt')
    | None => Err (msg "Set statement errors.")
    end.


Local Open Scope gensym_monad_scope.

(* For each drop(p) statement, return list of places, their optional
drop flag, and whether it is fully own. Each place is used to generate
a deterministic drop statement. For now, we do not distinguish fully
owned or partial moved Box types, i.e., we do not use a single
drop_in_place function to recursively drop the fully owned box *)
(** The following definition is replaced by an implementation based on
split_drop_place which does not require the fuel parameter *)
Fixpoint elaborate_drop_for_unused (pc: node) (mayinit mayuninit universe: Paths.t) (fuel: nat) (ce: composite_env) (p: place) : mon (list (place * option ident * bool)) :=
  match fuel with
  | O => error (msg "Running out of fuel in elaborate_drop_for")
  | S fuel' =>
      let elaborate_drop_for := elaborate_drop_for_unused pc mayinit mayuninit universe fuel' ce in
      if Paths.mem p universe then
        match typeof_place p with        
        | Tstruct _ _
        | Tvariant _ _ => (* use drop function of this Tstruct (Tvariant) to drop p *)
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                do drop_flag <- gensym type_bool p;
                ret ((p, Some drop_flag, true) :: nil)
              else                         (* must initialized *)
                ret ((p, None, true) :: nil)
            else                (* must uninitialized *)
              ret nil
        | Tbox ty =>
            (** TODO: we need to check if p is fully owned, in order
            to just use one function to drop all its successor *)
            (* first drop *p if necessary *)
            if Paths.is_empty (Paths.filter (fun elt => is_prefix (Pderef p ty) elt) universe) then (* p fully owns because there are no p's children in universe *)
              if Paths.mem p mayinit then
                if Paths.mem p mayuninit then (* need drop flag *)
                  do drop_flag <- gensym type_bool p;
                  ret ((p, Some drop_flag, true) :: nil)
                else                         (* must initialized *)
                  ret ((p, None, true) :: nil)
              else                (* must uninitialized *)
                ret nil
            else (* It is partially owns *)
              (* first we elaborate drops for its children *)
              do drops <- elaborate_drop_for (Pderef p ty);
              if Paths.mem p mayinit then
                if Paths.mem p mayuninit then (* need drop flag *)
                  do drop_flag <- gensym type_bool p;
                  ret (drops ++ [(p, Some drop_flag, false)])
                else                         (* must initialized *)
                  ret (drops ++ [(p, None, false)])
              else                (* must uninitialized *)
                ret drops              
        | _ => error [CTX pc; MSG ": Normal types do not need drop: elaborate_drop_for"]
        end
      else (* split p into its children and drop them *)
        (** p may be partially initialized *)
        match typeof_place p with
        | Tstruct _ id  =>
            match ce!id with
            | Some co =>
                let children := map (fun elt => match elt with
                                             | Member_plain fid fty =>
                                                 Pfield p fid fty end)
                                  co.(co_members) in
                let rec elt acc :=
                  do drops <- acc;
                  do drops' <- elaborate_drop_for elt;
                  ret (drops' ++ drops) in
                fold_right rec (ret nil) children
            | None => error [CTX pc; MSG ": Unfound struct id in composite_env: elaborate_drop_for"]
            end
        | Tbox _ => error ([CTX pc ; MSG ": place is "; CTX (local_of_place p); MSG ": Box does not exist in the universe set: elaborate_drop_for"])
        | Tvariant _ _ => error ([CTX pc ; MSG ": place is "; CTX (local_of_place p); MSG ": Variant cannot be split: elaborate_drop_for"])
        | _ => ret nil
        end
  end.

Fixpoint generate_drop_flags_for (mayinit mayuninit: Paths.t) (l: list (place * bool)) : mon (list (place * option ident * bool)) :=
  match l with
  | nil => ret nil
  | (p, full) :: l' =>
      do flags <- generate_drop_flags_for mayinit mayuninit l';
      if Paths.mem p mayinit then
        if Paths.mem p mayuninit then
        (* need drop flag *)
        do drop_flag <- gensym type_bool p;
        ret ((p, Some drop_flag, full) :: flags)
        else
          (* this place must be init, no need for drop flag *)
          do flags <- generate_drop_flags_for mayinit mayuninit l';
          ret ((p, None, full) :: flags)
      else
        (* this place must be uninit, no need to drop *)
        ret flags
  end.

Definition elaborate_drop_for (pc: node) (mayinit mayuninit universe: Paths.t) (ce: composite_env) (p: place) : mon (list (place * option ident * bool)) :=
  match split_drop_place ce universe p (typeof_place p) with
  | OK drop_places =>      
      (** may be we should check the disjointness of drop flags *)
      generate_drop_flags_for mayinit mayuninit drop_places     
  | Error msg =>
      error msg
  end.


Section INIT_UNINIT.

Variable (maybeInit maybeUninit: PTree.t PathsMap.t).

Definition drop_fully_own (p: place) :=
  makeseq (map (fun p => Sdrop p) (split_fully_own_place p (typeof_place p))).


(* create a drop statement using drop flag optionally *)
Definition generate_drop (p: place) (flag: option ident) (full: bool) : statement :=
  let drop := if full then
                drop_fully_own p
              else Sdrop p in
  match flag with
  | Some id =>
      Sifthenelse (Epure (Eplace (Plocal id type_bool) type_bool)) drop Sskip
  | None => drop
  end.

(* Collect the to-drop places and its drop flag from a statement, meanwhile updating the statement *)
Definition elaborate_drop_at (ce: composite_env) (f: function) (instr: instruction) (pc: node) : mon unit :=
  match instr with
  | Isel sel _ =>
      let mayinit := maybeInit!pc in
      let mayuninit := maybeUninit!pc in
      match mayinit, mayuninit with
      | Some mayinit, Some mayuninit =>
          match select_stmt f.(fn_body) sel with
          | Some (Sdrop p) =>
              let id := local_of_place p in
              let init := PathsMap.get id mayinit in
              let uninit := PathsMap.get id mayuninit in
              let universe := Paths.union init uninit in
              (* drops are the list of to-drop places and their drop flags *)
              do drops <- elaborate_drop_for pc init uninit universe ce p;
              let drop_stmts := map (fun (elt: place * option ident * bool) => generate_drop (fst (fst elt)) (snd (fst elt)) (snd elt)) drops in
              set_stmt sel (makeseq drop_stmts)
          | _ => ret tt
          end
      | _, _ =>
          (** FIXME: this pc has no information of initialized
              variables (it may be unreachable), so we do not
              elaborate it and set it to Sskip (may be wrong?) *)
          set_stmt sel Sskip
      end
  | _ => ret tt
  end.

Definition elaborate_drop (ce: composite_env) (f: function) (cfg: rustcfg) : mon unit :=
  PTree.fold (fun acc pc elt => do _ <- acc; elaborate_drop_at ce f elt pc) cfg (ret tt).

End INIT_UNINIT.

(** Insert update of drop flags  *)

Section DROP_FLAGS.

(* map from place to its drop flag *)
Variable m: PTree.t (list (place * ident)).

Definition get_dropflag_temp (p: place) : option ident :=
  let id := local_of_place p in
  match m!id with
  | Some l =>
      match find (fun elt => place_eq p (fst elt)) l with
      | Some (_, fid) => Some fid
      | _ => None
      end
  | _ => None
  end.

Definition Ibool (b: bool) := Epure (Econst_int (if b then Int.one else Int.zero) type_bool).

Definition set_dropflag (id: ident) (flag: bool) : statement :=
  Sassign (Plocal id type_bool) (Ibool flag).

Definition set_dropflag_option (id: option ident) (flag: bool) : statement :=
  match id with
  | Some id =>
      set_dropflag id flag
  | None => Sskip
  end.

Definition add_dropflag (p: place) (flag: bool) : statement :=
  set_dropflag_option (get_dropflag_temp p) flag.


Definition add_dropflag_option (p: option place) (flag: bool) : statement :=
  match p with
  | Some p => add_dropflag p flag
  | _ => Sskip
  end.

Definition add_dropflag_list (l: list place) (flag: bool) : statement :=
  let stmts := fold_right (fun elt acc => add_dropflag elt flag :: acc) nil l in
  makeseq stmts.

(** FIXME: It may generate lots of Sskip *)
Fixpoint transl_stmt (stmt: statement) : statement :=
  match stmt with
  | Sassign p e
  | Sassign_variant p _ _ e
  | Sbox p e =>
      let deinit := moved_place e in
      let stmt1 := add_dropflag_option deinit false in
      let stmt2 := add_dropflag p true in
      makeseq (stmt1 :: stmt2 :: stmt :: nil)  
  | Scall p e el =>
      let mvpaths := moved_place_list el in
      let stmt1 := add_dropflag_list mvpaths false in
      let stmt2 := add_dropflag p true in
      makeseq (stmt1 :: stmt :: stmt2 :: nil)
  | Ssequence s1 s2 =>
      Ssequence (transl_stmt s1) (transl_stmt s2)
  | Sifthenelse e s1 s2 =>
      Sifthenelse e (transl_stmt s1) (transl_stmt s2)
  | Sloop s =>
      Sloop (transl_stmt s)
  | _ => stmt
  end.

End DROP_FLAGS.
  
Local Open Scope error_monad_scope.

Definition init_drop_flag (mayinit: PathsMap.t) (mayuninit: PathsMap.t) (elt: place * ident) : statement :=
  let (p, flag) := elt in
  let id := local_of_place p in
  match mayinit!id, mayuninit!id with
  | Some init, Some uninit =>
      if Paths.mem p init then
        set_dropflag flag true
      else
        if Paths.mem p uninit then
          set_dropflag flag false
        else Sskip
  | _, _ => Sskip
  end.                          
  
Definition transf_function (ce: composite_env) (f: function) : Errors.res function :=
  do (mayinit, mayuninit) <- analyze ce f;
  let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
  (* let next_flag := Pos.succ (fold_left Pos.max vars 1%positive) in *)
  let init_state := initial_generator f.(fn_body) in
  (** FIXME: we generate cfg twice *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (* step 1 and step 2 *)
  match elaborate_drop mayinit mayuninit ce f cfg init_state with
  | Res _ st =>
      (* step 3: initialize and update drop flag *)
      let flags := concat (snd (split (PTree.elements (snd st.(gen_map))))) in
      match mayinit!entry, mayuninit!entry with
      | Some entry_init, Some entry_uninit =>
          (* init drop flags: if no flags, it would be a Sskip *)
          let init_stmt := makeseq (map (init_drop_flag entry_init entry_uninit) flags) in
          (* update drop flags when encountering assginment *)
          let stmt' := transl_stmt (snd st.(gen_map)) st.(gen_stmt) in
          Errors.OK (mkfunction f.(fn_generic_origins)
                                f.(fn_origins_relation)
                                f.(fn_drop_glue)
                        f.(fn_return)
                        f.(fn_callconv)                        
                        (f.(fn_vars) ++ st.(gen_trail))
                        f.(fn_params)
                        (Ssequence init_stmt stmt'))      
      | _, _ => Errors.Error (msg "There is no init information in the entry node")
      end
  | Err msg =>
      Errors.Error msg
  end.


Definition transf_fundef (ce: composite_env) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f => do tf <- transf_function ce f; Errors.OK (Internal tf)
  | External orgs org_rels ef targs tres cconv => Errors.OK (External orgs org_rels ef targs tres cconv)
  end.


(** Translation of a whole program. *)

Definition transl_program (p: program) : Errors.res program :=
  do p1 <- transform_partial_program (transf_fundef p.(prog_comp_env)) p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
              prog_public := AST.prog_public p1;
              prog_main := AST.prog_main p1;
              prog_types := prog_types p;
              prog_comp_env := prog_comp_env p;
              prog_comp_env_eq := prog_comp_env_eq p |}.

