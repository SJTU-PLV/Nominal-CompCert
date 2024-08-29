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
  | Emoveplace p _ => Some (valid_owner p)
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
  (* This condition complicates the proof. Maybe we can prove that
  transfer bot = bot *)
  (* if PathsMap.beq before PathsMap.bot then PathsMap.bot *)
  (* else *)
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
Definition analyze (ce: composite_env) (f: function) : Errors.res (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t) :=
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
  (* we only want the PTree because [None] represent the unreachable node *)
  | Some initMap, Some uninitMap => Errors.OK (initMap, uninitMap, whole)
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


(** * Soundness of Initial Analysis *)


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

Record sound_own (own: own_env) (init uninit universe: PathsMap.t) : Type :=
  { sound_own_init: PathsMap.ge init own.(own_init);
    
    sound_own_uninit: PathsMap.ge uninit own.(own_uninit);

    sound_own_universe: PathsMap.eq universe own.(own_universe) }.

    
(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.
Variable se: Genv.symtbl.

Let ge := RustIR.globalenv se prog.
Let ce := ge.(genv_cenv).

Inductive sound_cont: cont -> Prop :=
| sound_cont_stop: sound_cont Kstop
| sound_cont_seq: forall s k,
    sound_cont k ->
    sound_cont (Kseq s k)
| sound_cont_loop: forall s k,
    sound_cont k ->
    sound_cont (Kloop s k)
| sound_cont_call: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg instr k own le p
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc =  mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc = Some instr)
    (IS: match_instr_stmt f.(fn_body) instr Sskip k)
    (OWN: sound_own own mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_cont (Kcall p f le own k)
| sound_cont_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg instr k own le st l
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc =  mayinit)
    (UNINIT: uninitMap !! pc =  mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc = Some instr)
    (IS: match_instr_stmt f.(fn_body) instr Sskip k)
    (OWN: sound_own own mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_cont (Kdropplace f st l le own k)
| sound_cont_dropcall: forall id b ofs st membs k,
    sound_cont k ->
    sound_cont (Kdropcall id (Vptr b ofs) st membs k)
  .
    
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg instr s k own le m
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc = Some instr)
    (IS: match_instr_stmt f.(fn_body) instr s k)
    (OWN: sound_own own mayinit mayuninit universe),
    sound_state (State f s k le own m)
| sound_callstate: forall vf args k m
    (CONT: sound_cont k),
    sound_state (Callstate vf args k m) 
| sound_returnstate: forall v k m
    (CONT: sound_cont k),
    sound_state (Returnstate v k m)
| sound_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg instr k own le st l m
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc = Some instr)
    (IS: match_instr_stmt f.(fn_body) instr Sskip k)
    (OWN: sound_own own mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_state (Dropplace f st l k le own m)
| sound_dropstate: forall id b ofs st membs k m,
    sound_cont k ->
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
.

(* use fixpoint_soulution to prove that the final abstract env
approximates more than the abstract env computed by transfer
function *)
Lemma analyze_successor: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr pc1 pc2
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2),
    PathsMap.ge (initMap !! pc2) mayinit1
    /\ PathsMap.ge (uninitMap !! pc2) mayuninit1
.
  (* use fixpoint_solution *)
Admitted.

         
(* use transfer to act as the bridge to construct the succ abstract
env *)
Lemma analyze_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr own2 pc1 pc2
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2)
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
  exists mayinit3 mayuninit3,
    initMap !! pc2 = mayinit3
    /\ uninitMap !! pc2 = mayuninit3
    /\ sound_own own2 mayinit3 mayuninit3 universe.
  (* show that PathsMap.ge ae1 ae2 and sound_own ae1 implies sound_own
  ae2 *)
Admitted.

Lemma sound_state_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr1 instr2 own2 pc1 pc2 s k m le
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL1: cfg ! pc1 = Some instr1)
    (PC: In pc2 (successors_instr instr1))
    (* how to prove it? *)
    (SEL2: cfg ! pc2 = Some instr2)
    (IS: match_instr_stmt f.(fn_body) instr2 s k)
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2)
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
    sound_state (State f s k le own2 m).
Admitted.


Theorem sound_step: forall s t s',
    step ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  (* step_assign *)
  - inv IS.
    eapply sound_state_succ with (pc2:= n); eauto.
    simpl. auto.
    (* TODO: properties of generated cfg *)
    admit.
    admit.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite H3.
    (* maybe easy *)
    unfold own_check_expr, own_check_assign in *.
    admit.
Admitted.      
    
End SOUNDNESS.
