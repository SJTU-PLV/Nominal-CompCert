Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustIR RustIRown.
Require Import InitDomain.


Local Open Scope list_scope.

Definition moved_place (e: expr) : option place :=
  match e with
  | Emoveplace p _ => Some p
  | _ => None
  end.

Fixpoint moved_place_list (al: list expr) : list place :=
  match al with
  | e :: l =>
      match moved_place e with
      | Some p => p :: moved_place_list l
      | None => moved_place_list l
      end
  | nil => nil
  end.

(* S is the whole set, flag = true indicates that it computes the MaybeInit set *)
Definition transfer (S: PathsMap.t) (flag: bool) (f: function) (cfg: rustcfg) (pc: node) (before: PathsMap.t) : PathsMap.t :=
  if PathsMap.beq before PathsMap.bot then PathsMap.bot
  else
    match cfg ! pc with
    | None => PathsMap.bot
    | Some (Inop _) => before
    | Some (Icond _ _ _) => before
    | Some Iend => before
    | Some (Isel sel _) =>
        match select_stmt f.(fn_body) sel with
        | None => PathsMap.bot
        | Some s =>
        match s with
        | Sassign p e
        | Sassign_variant p _ _ e
        | Sbox p e =>
            let p' := moved_place e in
            if flag then
              add_place S p (remove_option p' before)
            else
              remove_place p (add_option S p' before)
        | Scall p _ al =>
            let pl := moved_place_list al in
            if flag then
              add_place S p (fold_right remove_place before pl)
            else
              remove_place p (fold_right (add_place S) before pl)
        | Sreturn (Some e) =>
            let p' := moved_place e in
            if flag then
              remove_option p' before
            else
              add_option S p' before
        | _ => before
        end
        end
    end.

Module DS := Dataflow_Solver(PathsMap)(NodeSetForward).

Local Open Scope error_monad_scope.

(* The analyze returns the MaybeInit and MaybeUninit sets along with
the universe set *)
Definition analyze (ce: composite_env) (f: function) : Errors.res (PTree.t PathsMap.t * PTree.t PathsMap.t * PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let maybeInit := fold_right (add_place whole) empty_pathmap pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := fold_right (add_place whole) empty_pathmap vl in
  (* generate selector-based CFG for analysis *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry maybeInit in
let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry maybeUninit in
  match initMap, uninitMap with
  (* we only want the PTree because [None] represent the unreachable
  node *)
  | Some (_, initMap), Some (_, uninitMap) => Errors.OK (initMap, uninitMap, whole)
  | _, _ => Errors.Error (msg "Error in initialize analysis")
  end.
  
(** Definitions of must_owned and may_owned used in Drop elaboration *)

Definition must_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mustinit := Paths.diff init uninit in
  (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mustinit *)
  Paths.for_all (fun p' => Paths.mem p' mustinit)
    (Paths.filter (fun p' => is_prefix p' p) universe).

(* place that needs drop flag *)
Definition may_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mayinit := Paths.inter init uninit in
  (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mayinit *)
  Paths.for_all (fun p' => Paths.mem p' mayinit)
    (Paths.filter (fun p' => is_prefix p' p) universe).

(* Used in static move checking *)
Definition must_movable (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mustinit := Paths.diff init uninit in
  (* ∀ p' ∈ universe, is_prefix p p' → must_owned p' *)
  Paths.for_all (must_owned initmap uninitmap universemap)
    (Paths.filter (is_prefix p) universe).


(** * Soundness of Initialized Analysis *)


(* relation between the selector and the (stmt, cont) pair *)
Inductive match_instr_stmt (body: statement) : instruction -> statement -> cont -> Prop :=
| sel_stmt_base: forall sel n s k,
    select_stmt body sel = Some s ->
    match_instr_stmt body (Isel sel n) s k
| sel_stmt_seq: forall sel n s1 s2 k,
    match_instr_stmt body (Isel sel n) s1 (Kseq s2 k) ->
    match_instr_stmt body (Isel sel n) (Ssequence s1 s2) k
| sel_stmt_kseq: forall sel n s k,
    match_instr_stmt body (Isel sel n) s k ->
    match_instr_stmt body (Isel sel n) Sskip (Kseq s k)
| sel_stmt_ifthenelse: forall e n1 n2 s1 s2 k,
    match_instr_stmt body (Icond e n1 n2) (Sifthenelse e s1 s2) k
| sel_stmt_loop: forall n s k,    
    match_instr_stmt body (Inop n) (Sloop s) k
| sel_stmt_break: forall n k,    
    match_instr_stmt body (Inop n) Sbreak k
| sel_stmt_continue: forall n k,
    match_instr_stmt body (Inop n) Scontinue k
.

(* Record sound_own (own: own_env) (init uninit: PathsMap.t) : Type := *)
(*   PathsMap.t *)
(*     Paths.diff *)

(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.
Variable se: Genv.symtbl.

Let ge := RustIR.globalenv se prog.
Let ce := ge.(genv_cenv).

(* Inductive sound_state: state -> Prop := *)
(* | sound_regular_state: forall *)
(*     (AN: analyze ce f = OK (initMap, uninitMap)) *)
(*     (INIT: initMap ! pc = Some mayinit) *)
(*     (UNINIT: uninitMap ! pc = Some mayuninit) *)
(*     (CFG: generate_cfg f.(fn_body) = OK (entry, cfg)) *)
(*     (SEL: cfg ! pc = Some instr) *)
(*     (IS: match_instr_stmt f.(fn_body) instr s k) *)
(*     (OWN: sound_own own mayinit mayuninit) *)
(*     sound_state (State f s k le own m) *)

End SOUNDNESS.
