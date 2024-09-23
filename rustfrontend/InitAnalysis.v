Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustIR RustIRcfg RustIRown.
Require Import InitDomain.

Import ListNotations.
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
        | Sdrop p =>
            if flag then
              remove_place p before
            else
              add_place S p before
        | _ => before
        end
        end
    end.

Module DS := Dataflow_Solver(PathsMap)(NodeSetForward).

Local Open Scope error_monad_scope.

(* The analyze returns the MaybeInit and MaybeUninit sets along with
the universe set *)
Definition analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t) :=
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
  (* do (entry, cfg) <- generate_cfg f.(fn_body); *)
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

(* static version of is_init *)
Definition must_init (initmap uninitmap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let mustinit := Paths.diff init uninit in
  Paths.mem p mustinit.

(* place that needs drop flag *)
Definition may_init (initmap uninitmap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let mayinit := Paths.inter init uninit in
  Paths.mem p mayinit.

(* move it to a new file *)


(** * Soundness of Initial Analysis *)

Inductive tr_cont : statement -> rustcfg -> cont -> node -> option node -> option node -> node -> Prop :=
| tr_Kseq: forall body cfg s pc next cont brk nret k
    (STMT: tr_stmt body cfg s pc next cont brk nret)
    (CONT: tr_cont body cfg k next cont brk nret),
    tr_cont body cfg (Kseq s k) pc cont brk nret
| tr_Kstop: forall body cfg nret
    (RET: cfg ! nret = Some Iend),
    tr_cont body cfg Kstop nret None None nret
| tr_Kloop: forall body cfg s body_start loop_jump_node exit_loop nret cont brk k
    (STMT: tr_stmt body cfg s body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (SEL: cfg ! loop_jump_node = Some (Inop body_start))
    (CONT: tr_cont body cfg k exit_loop cont brk nret),
    tr_cont body cfg (Kloop s k) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret
| tr_Kdropplace: forall body cfg k pc cont brk nret f st l le own entry
    (CONT: tr_cont body cfg k pc cont brk nret)
    (TRFUN: tr_fun f nret entry cfg),
    tr_cont body cfg (Kdropplace f st l le own k) pc cont brk nret
| tr_Kdropcall: forall body cfg k pc cont brk nret st membs b ofs id
    (CONT: tr_cont body cfg k pc cont brk nret),
    tr_cont body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret
| tr_Kcall: forall body cfg k nret f le own p
    (STK: tr_stacks (Kcall p f le own k))
    (RET: cfg ! nret = Some Iend),
    tr_cont body cfg (Kcall p f le own k) nret None None nret

(* Used to restore tr_cont in function calls *)
with tr_stacks: cont -> Prop :=
| tr_stacks_stop:
  tr_stacks Kstop
| tr_stacks_call: forall f nret cfg pc cont brk k own p le entry
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret),
    tr_stacks (Kcall p f le own k).


Record sound_own (own: own_env) (init uninit universe: PathsMap.t) : Type :=
  { sound_own_init: PathsMap.ge init own.(own_init);
    
    sound_own_uninit: PathsMap.ge uninit own.(own_uninit);

    sound_own_universe: PathsMap.eq universe own.(own_universe) }.

(* Properties of sound_own *)

Lemma must_init_sound (own: own_env) (init uninit universe: PathsMap.t) p:
    sound_own own init uninit universe ->
    must_init init uninit p = true ->
    is_init own p = true.
Admitted.

Lemma must_not_init_sound (own: own_env) (init uninit universe: PathsMap.t) p:
    sound_own own init uninit universe ->
    must_init init uninit p = false ->
    may_init init uninit p = false ->
    is_init own p = false.
Admitted.


(** ** Semantic invariant *)

(* relation of moveing split places *)
Fixpoint move_split_places (own :own_env) (l: list (place * bool)) : own_env :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      move_split_places (if is_init own p then move_place own p else own) l'
  end.
  

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
| sound_cont_call: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg k own1 own2 le p cont brk nret
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)                   
    (OWN: sound_own own2 mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_cont (Kcall p f le own1 k)
| sound_cont_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe  cfg k own1 own2 le st l cont brk nret entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc =  mayinit)
    (UNINIT: uninitMap !! pc =  mayuninit)
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (MOVESPLIT: move_split_places own1 l = own2)
    (CONT: sound_cont k),
    sound_cont (Kdropplace f st l le own1 k)
| sound_cont_dropcall: forall id b ofs st membs k,
    sound_cont k ->
    sound_cont (Kdropcall id (Vptr b ofs) st membs k)
.

  
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f initMap uninitMap pc mayinit mayuninit universe cfg s k own le m nret next cont brk entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret entry cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc next cont brk nret)
    (* k may be contain some statement not located in [next], e.g.,
    statements after continue and break *)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (OWN: sound_own own mayinit mayuninit universe),
    sound_state (State f s k le own m)
| sound_callstate: forall vf args k m
    (CONT: sound_cont k)
    (TRSTK: tr_stacks k),
    sound_state (Callstate vf args k m) 
| sound_returnstate: forall v k m
    (CONT: sound_cont k)
    (TRSTK: tr_stacks k),
    sound_state (Returnstate v k m)
| sound_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe cfg k own1 own2 le st l m nret cont brk entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (* small-step move_place to simulate big-step move_place in
    transfer. maybe difficult to prove *)
    (MOVESPLIT: move_split_places own1 l = own2)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_state (Dropplace f st l k le own1 m)
| sound_dropstate: forall id b ofs st membs k m
    (CONT: sound_cont k),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
.
    
(* soundness of function entry: use fixpoint_entry to prove it *)
Lemma sound_function_entry: forall f initMap uninitMap universe entry cfg own
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (FENTRY: init_own_env ce f = OK own),
    sound_own own initMap!!entry uninitMap!!entry universe.
Proof.
  intros. unfold analyze in AN. unfold init_own_env in FENTRY.
  Errors.monadInv FENTRY.
  rewrite EQ in AN. simpl in AN.
  set (initParams := fold_right (add_place x)
                  (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
                  (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f))) in *.  
  set (uninitVars := fold_right (add_place x)
                    (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
                    (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_vars f))) in *.
  destruct (DS.fixpoint cfg successors_instr (transfer x true f cfg) entry initParams) eqn: initAN; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer x false f cfg) entry uninitVars) eqn: uninitAN; try congruence.
  inv AN.
  eapply DS.fixpoint_entry in initAN.
  eapply DS.fixpoint_entry in uninitAN.
  constructor; auto.
  simpl. eapply PathsMap.eq_refl.
Qed.


(* Some properties of call_cont *)
Lemma sound_call_cont: forall k,
    sound_cont k -> sound_cont (call_cont k).
Proof.
  intros k SOUND.
  induction k; inv SOUND; simpl; try econstructor; eauto.
Qed.

Lemma tr_stacks_call_cont: forall k body cfg pc cont brk nret
    (SOUND: tr_cont body cfg k pc cont brk nret),
  tr_stacks (call_cont k).
Proof.
  induction k; intros; inv SOUND; simpl; try (econstructor; eauto; fail).
  - eapply IHk. eauto.
  - eapply IHk. eauto.
  - inv STK. econstructor; eauto.
  - eapply IHk. eauto.
  - eapply IHk. eauto.
Qed.

(* use fixpoint_soulution to prove that the final abstract env
approximates more than the abstract env computed by transfer
function *)
Lemma analyze_successor: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe cfg entry instr pc1 pc2
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2),
    PathsMap.ge (initMap !! pc2) mayinit2
    /\ PathsMap.ge (uninitMap !! pc2) mayuninit2
.
Proof.  (* use fixpoint_solution *)
  unfold analyze; intros. 
  Errors.monadInv AN.
  set (params_init := (fold_right (add_place x)
               (PTree.map
                  (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
               (map
                  (fun elt : ident * type =>
                   Plocal (fst elt) (snd elt)) (fn_params f)))) in *.
  set (vars_uninit := (fold_right (add_place x)
                   (PTree.map
                      (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
                   (map
                      (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_vars f)))) in *.
  destruct (DS.fixpoint cfg successors_instr (transfer x true f cfg) entry
              params_init) eqn: INITMAP; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer x false f cfg) entry
              vars_uninit) eqn: UNINITMAP; try congruence.
  inv EQ0.
  split.
  - eapply DS.fixpoint_solution; eauto.
    (** TODO: transfer bot to bot *)
    admit.
  - eapply DS.fixpoint_solution; eauto.
    admit.
Admitted.
    
         
(* use transfer to act as the bridge to construct the succ abstract
env *)
Lemma analyze_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr own2 pc1 pc2
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
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
Proof.
  intros. exploit analyze_successor; eauto.
  intros (A & B).
  exists (initMap !! pc2), (uninitMap !! pc2).
  split; auto. split; auto.
  destruct OWN.
  constructor.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.eq_trans; eauto.
    apply PathsMap.eq_refl.
Qed.


Lemma sound_state_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr1 own2 pc1 pc2 s k m le nret next cont brk
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (SEL1: cfg ! pc1 = Some instr1)
    (PC: In pc2 (successors_instr instr1))
    (TRFUN: tr_fun f nret entry cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc2 next cont brk nret)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2)
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
    sound_state (State f s k le own2 m).
Proof.
  intros. exploit analyze_succ; eauto.
  intros (mayinit3 & mayuninit3 & (A & B & C)).
  econstructor; eauto.
Qed.  


(* Key point: match the small step ownership transfer and the big step
analysis in transfer function of Sdrop *)
Lemma sound_step_dropplace: forall s t s',
    step_dropplace ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  - econstructor; eauto.
    simpl in OWN.
    rewrite NOTOWN in OWN. auto.
  - simpl in OWN0.
    econstructor; eauto.
    rewrite OWN in OWN0. auto.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor. 
Qed.

Lemma sound_step_dropstate: forall s t s',
    step_drop ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
  - inv CONT.
    econstructor; eauto.
  - econstructor; eauto.
    inv CONT. auto.
Qed.

(** TODO: where to put it *)
(* We can generate cfg for all analyzed functions. This property is
guaranteed by the compilation pass which actually uses the analyze
function *)
Hypothesis function_analyzed: forall (v : val) (f: function),
    Genv.find_funct ge v = Some (Internal f) ->
    exists entry cfg nret initMap uninitMap universe,
      tr_fun f nret entry cfg /\
      analyze ce f cfg entry = OK (initMap, uninitMap, universe).


Theorem sound_step: forall s t s',
    step ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  (* step_assign *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc1:= pc); eauto.
    simpl. eauto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    (* maybe easy *)
    unfold own_check_expr, own_check_assign in *.
    admit.
  (* step_assign_variant *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc1:= pc); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    admit.
  (* step_box *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc1:= pc); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    admit.
  (* step_to_dropplace *)
  - eapply sound_dropplace; eauto.
  (** Difficult part: prove split_drop_place small-step simulates the
  analysis *)
    admit.
  (* step_in_dropplace *)
  - eapply sound_step_dropplace; eauto.
    econstructor; eauto.
  (* step_dropstate *)
  - eapply sound_step_dropstate; eauto.
    econstructor; eauto.
  (* step_storagelive *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc1:= pc); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    unfold transfer. rewrite SEL. rewrite STMT.
    auto.
  (* step_storagedead *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc1:= pc); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    unfold transfer. rewrite SEL. rewrite STMT.
    auto.
  (* step_call *)
  - inv TRSTMT. econstructor.
    inv TRFUN.
    econstructor; eauto.
    exploit analyze_succ. 1-3: eauto. eapply SEL.
    instantiate (1 :=next). simpl. auto. eauto. eauto.
    (* prove sound_own *)
    instantiate (1 := (init_place (own_transfer_exprlist own1 al) p)). admit.
    intros (mayinit3 & mayuninit3 & A & B & C). subst. auto.
    econstructor; eauto.
  (* step_internal_function *)
  - exploit function_analyzed; eauto.
    intros (entry & cfg & nret & initMap & uninitMap & universe & TRFUN & AN).
    inv TRFUN.
    inv ENTRY.
    exploit sound_function_entry; eauto.
    intros SOUND_INIT.
    econstructor; eauto.
    econstructor; eauto.
    (* intros (nret & TRFUN). *)
    (* tr_cont *)
    inv TRSTK.
    econstructor. auto.
    econstructor; eauto.
    econstructor; eauto.
  (* step_external_function *)    
  - econstructor; eauto.
  (* step_return_0 *)
  - econstructor.
    apply sound_call_cont; auto.
    eapply tr_stacks_call_cont; eauto.
  (* step_return_1 *)
  - econstructor.
    apply sound_call_cont; auto.
    eapply tr_stacks_call_cont; eauto.
  (* step_skip_call *)
  - econstructor.
    apply sound_call_cont; auto.
    eapply tr_stacks_call_cont; eauto.
  (* step_returnstate *)
  - (** TODO: problem between the nodes in tr_stacks and sound_cont *)
    (* inv TRSTK. inv CONT. *)
    (* inv TRFUN. *)
    (* rewrite CFG in CFG0. inv CFG0. *)
    (* clear TRCONT. *)
    (* econstructor; eauto. *)
    (* econstructor; eauto. *)
    (* econstructor. *)
    (* prove sound_own *)
    admit.
  (* step_seq *)
  - inv TRSTMT. simpl in TRCONT.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_seq *)
  - inv TRSTMT. inv TRCONT.
    econstructor; eauto.
    inv CONT. auto.
  (* step_continue_seq *)
  - inv TRSTMT. inv TRCONT.
    econstructor; eauto.
    econstructor; eauto.
    inv CONT. auto.
  (* step_break_seq *)
  - inv TRSTMT. inv TRCONT.
    econstructor; eauto.
    econstructor; eauto.
    inv CONT. auto.
  (* step_ifthenelse *)
  - inv TRSTMT.
    econstructor; eauto.
    destruct b; auto.
    (** TODO: ifthenelse must use pure expression *)
    admit. admit.
  (* step_loop *)
  - inv TRSTMT.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    inv TRFUN.
    exploit analyze_succ. 1-3: eauto. eapply SEL.
    simpl. eauto.
    unfold transfer. rewrite SEL. eauto.
    unfold transfer. rewrite SEL. eauto.
    eauto.
    intros (mayinit3 & mayuninit3 & A & B & C).
    subst. auto.
  (* step_skip_or_continue_loop *)
  - inv TRCONT.
    econstructor; eauto.    
    econstructor; eauto.
    inv TRFUN.
    destruct H; inv H.
    + inv TRSTMT.
      exploit analyze_succ. 1-3: eauto. eapply SEL.
      simpl. eauto.
      unfold transfer. rewrite SEL. eauto.
      unfold transfer. rewrite SEL. eauto.
      eauto.
      intros (mayinit3 & mayuninit3 & A & B & C).
      subst. auto.
    + inv TRSTMT.
      exploit analyze_succ. 1-3: eauto. eapply SEL.
      simpl. eauto.
      unfold transfer. rewrite SEL. eauto.
      unfold transfer. rewrite SEL. eauto.
      eauto.
      intros (mayinit3 & mayuninit3 & A & B & C).
      subst. auto.
  (* step_break_loop *)
  - inv TRSTMT. inv TRCONT. inv CONT.
    econstructor; eauto.
    econstructor.
Admitted.

End SOUNDNESS.

