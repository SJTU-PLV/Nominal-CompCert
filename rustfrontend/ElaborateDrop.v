Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Rustlight RustIR RustIRcfg.
Require Import InitDomain InitAnalysis.

Import ListNotations.

Local Open Scope error_monad_scope.

(** Use the analysis from InitAnalysis.v to elaborate the drop
statements. After this pass, the ownership semantics is removed. The
memory deallocation would be explicit and deterministic *)

(** The drop elaboration has three steps: 1. Iterate the CFG to
collect drop flags for each drops; 2. Update the drops statement (from
conditonally drop to deterministic drop) in RustIR (AST) and insert
the update of the drop flag before the occurence of ownership transfer
*)


Parameter fresh_atom: unit -> ident.

(** Step 1: generate drop flags for the places whose init information
is flow-sensitive.  *)

Fixpoint generate_drop_flags_for_splits (mayinit mayuninit universe: PathsMap.t) (l: list place) : list (place * ident) :=
  match l with
  | nil => nil
  | p :: l' =>
      let flags := generate_drop_flags_for_splits mayinit mayuninit universe l' in
      if must_owned mayinit mayuninit universe p then
        (* this place must be init, no need for drop flag *)
        flags
      else if may_owned mayinit mayuninit universe p then
        (* need drop flag *)
        let drop_flag := fresh_atom tt in
        (p, drop_flag) :: flags
      else
        (* this place must be uninit, no need to drop *)
        flags
  end.

Definition generate_drop_flags_for (mayinit mayuninit universemap: PathsMap.t) (ce: composite_env) (p: place) : list (place * ident) :=
  let universe := PathsMap.get (local_of_place p) universemap in
  match split_drop_place ce universe p (typeof_place p) with
  | OK drop_places =>      
      (** may be we should check the disjointness of drop flags *)
      generate_drop_flags_for_splits mayinit mayuninit universemap (fst (split drop_places))
  (* The error case is considerer in elaboration step *)
  | Error msg =>
      []
  end.

Definition generate_place_map {A} (l: list (place * A)) : PTree.t (list (place * A)) :=
  fold_left (fun m elt => let id := local_of_place (fst elt) in
                       match PTree.get id m with
                       | Some l =>
                           PTree.set id (elt :: l) m
                       | None =>
                           PTree.set id [elt] m
                       end) l
    (PTree.empty (list (place * A))).

Section INIT_UNINIT.

Variable (maybeInit maybeUninit: PMap.t PathsMap.t).
Variable universe : PathsMap.t.

Definition generate_drop_flags_at (ce: composite_env) (f: function) (pc: node) (instr: instruction) : list (place * ident) :=
  match instr with
  | Isel sel _ =>
      let mayinit := maybeInit!!pc in
      let mayuninit := maybeUninit!!pc in
      match select_stmt f.(fn_body) sel with
      | Some (Sdrop p) =>
          generate_drop_flags_for mayinit mayuninit universe ce p
      | _ => []
      end
  | _ => []
  end.

Definition generate_drop_flags (ce: composite_env) (f: function) (cfg: rustcfg) : Errors.res (list (place * ident)) :=
  let flags := concat (snd (split (PTree.elements (PTree.map (generate_drop_flags_at ce f) cfg)))) in
  if list_norepet_dec place_eq (fst (split flags)) then
    if list_norepet_dec ident_eq (snd (split flags)) then
      OK flags
    else
      Error (msg "Repeated drop flags in generate_drop_flags")
  else
    Error (msg "Repeated drop places in generate_drop_flags")
.

End INIT_UNINIT.


(** Step 2: elaborate the statement in the AST by iterating the CFG *)

Definition drop_fully_own (p: place) :=
  makeseq (map (fun p => Sdrop p) (Rustlightown.split_fully_own_place p (typeof_place p))).

(* create a drop statement using drop flag optionally *)
Definition generate_drop (p: place) (full: bool) (flag: option ident) : statement :=
  let drop := if full then
                drop_fully_own p
              else Sdrop p in
  match flag with
  | Some id =>
      Sifthenelse (Epure (Eplace (Plocal id type_bool) type_bool)) drop Sskip
  | None => drop
  end.

Definition get_dropflag_temp (m: PTree.t (list (place * ident))) (p: place) : option ident :=
  let id := local_of_place p in
  match m!id with
  | Some l =>
      match find (fun elt => place_eq p (fst elt)) l with
      | Some (_, fid) => Some fid
      | _ => None
      end
  | _ => None
  end.


Fixpoint elaborate_drop_for_splits (mayinit mayuninit universe: PathsMap.t) (flagm: PTree.t (list (place * ident))) (l: list (place * bool)) : statement :=
  match l with
  | nil => Sskip
  | (p, full) :: l' =>
      let stmt := elaborate_drop_for_splits mayinit mayuninit universe flagm l' in
      if must_owned mayinit mayuninit universe p then
        (Ssequence (generate_drop p full None) stmt)
      else if may_owned mayinit mayuninit universe p then
        (* need drop flag *)
        (Ssequence (generate_drop p full (get_dropflag_temp flagm p)) stmt)
      else
        (* this place must be uninit, no need to drop *)
        stmt
  end.

Definition elaborate_drop_for (mayinit mayuninit universemap: PathsMap.t) (ce: composite_env) (flagm: PTree.t (list (place * ident))) (p: place) : Errors.res statement :=
  let universe := PathsMap.get (local_of_place p) universemap in
  match split_drop_place ce universe p (typeof_place p) with
  | OK drop_places =>      
      (** may be we should check the disjointness of drop flags *)
      OK (elaborate_drop_for_splits mayinit mayuninit universemap flagm drop_places)
  (* The error case is considerer in elaboration step *)
  | Error msg =>
      Error msg
  end.


Section ELABORATE.

Variable (maybeInit maybeUninit: PMap.t PathsMap.t).
Variable universe : PathsMap.t.

(* map from place to its drop flag *)
Variable m: PTree.t (list (place * ident)).

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
  set_dropflag_option (get_dropflag_temp m p) flag.


Definition add_dropflag_option (p: option place) (flag: bool) : statement :=
  match p with
  | Some p => add_dropflag p flag
  | _ => Sskip
  end.

Definition add_dropflag_list (l: list place) (flag: bool) : statement :=
  let stmts := fold_right (fun elt acc => add_dropflag elt flag :: acc) nil l in
  makeseq stmts.

Definition set_stmt (pc: node) (body: statement) (sel: selector) (s: statement) : Errors.res statement :=
  match update_stmt body sel s with
  | Some body1 => OK body1
  | None =>
      Error [CTX pc; MSG " update_stmt error in elaborate_stmt"]
  end.

(* elaborate the leaf statement in [body] *)
Definition elaborate_leaf_stmt (ce: composite_env) (f: function) (body: Errors.res statement) (pc: node) (instr: instruction) : Errors.res statement :=
  do body <- body;
  match instr with
  | Isel sel _ =>
      let mayinit := maybeInit!!pc in
      let mayuninit := maybeUninit!!pc in
      match select_stmt f.(fn_body) sel with
      | Some stmt =>
          match stmt with
          | Sdrop p =>
              do drop <- elaborate_drop_for mayinit mayuninit universe ce m p;
              set_stmt pc body sel drop
          | Sassign p e
          | Sassign_variant p _ _ e
          | Sbox p e =>
              let deinit := moved_place e in
              let stmt1 := add_dropflag_option deinit false in
              let stmt2 := add_dropflag p true in
              set_stmt pc body sel (makeseq (stmt1 :: stmt2 :: stmt :: nil))
          | Scall p e el =>
              let mvpaths := moved_place_list el in
              let stmt1 := add_dropflag_list mvpaths false in
              let stmt2 := add_dropflag p true in
              set_stmt pc body sel (makeseq (stmt1 :: stmt :: stmt2 :: nil))
          | _ => OK body
          end
      | None => Error [CTX pc; MSG " select_stmt error in elaborate_stmt"]
      end
  | _ => OK body
  end.


(* Collect the to-drop places and its drop flag from a statement, meanwhile updating the statement *)

Definition elaborate_stmt (ce: composite_env) (f: function) (cfg: rustcfg) : Errors.res statement :=
  PTree.fold (elaborate_leaf_stmt ce f) cfg (OK f.(fn_body)).

End ELABORATE.

  
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
  do analysis_res <- analyze ce f;
  let '(mayinit, mayuninit, universe) := analysis_res in
  let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** step 1: generate drop flags *)
  do flags <- generate_drop_flags mayinit mayuninit universe ce f cfg;
  let flagm := generate_place_map flags in
  (** step 2: elaborate the statements *)
  do stmt <- elaborate_stmt mayinit mayuninit universe flagm ce f cfg;
  (** step 3: initialize drop flags *)
  let entry_init := mayinit!!entry in
  let entry_uninit := mayuninit!!entry in
  (* init drop flags: if no flags, it would be a Sskip *)
  let init_stmt := makeseq (map (init_drop_flag entry_init entry_uninit) flags) in
  let flag_vars := combine (snd (split flags)) (repeat type_bool (length flags)) in
  Errors.OK (mkfunction f.(fn_generic_origins)
                        f.(fn_origins_relation)
                        f.(fn_drop_glue)
                        f.(fn_return)
                        f.(fn_callconv)                        
                        (f.(fn_vars) ++ flag_vars)
                        f.(fn_params)
                        (Ssequence init_stmt stmt))
. 


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
