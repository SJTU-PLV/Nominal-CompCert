Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import InitDomain InitAnalysis ElaborateDrop.
Require Import Rustlight Rustlightown RustIR RustOp.
Require Import RustIRsem RustIRown RustIRcfg.
Require Import Errors.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(* analysis result and flag map types *)
Definition AN : Type := (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t).
Definition FM : Type := PTree.t (list (place * ident)).


Record match_prog (p tp: RustIR.program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_skel:
    erase_program tp = erase_program p;
  match_prog_defs:
    list_norepet (prog_defs_names p)
}.

Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  intros. unfold transl_program in H. monadInv H. unfold transform_partial_program in EQ.
  destruct p. simpl in *. unfold transform_partial_program2 in EQ. 
Admitted. 


Section MATCH_PROGRAMS.
Variable p: program.
Variable tp: program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Theorem is_internal_match:
  forall v tv (f tf: RustIR.fundef),
  fundef_is_internal tf = fundef_is_internal f ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.is_internal (globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
Admitted. 
   
  
End INJECT.
End MATCH_PROGRAMS.


Inductive match_drop_place_state : option drop_place_state -> statement -> Prop :=
| match_dps_none:
  match_drop_place_state None Sskip
| match_dps_comp: forall p l,
    (* step_dropplace_init2 has simulated the drop flag condition
    checking *)
    match_drop_place_state (Some (drop_fully_owned_comp p l)) (Ssequence (Sdrop p) (makeseq (map (fun p => Sdrop p) l)))
| match_dps_box: forall l,
    match_drop_place_state (Some (drop_fully_owned_box l)) (makeseq (map (fun p => Sdrop p) l))
.

(* Because in dropplace state we do not know the pc, so we use own_env
to establish the relation between split drop places and target
statement. This relation should be proved when we enter Dropplace
state *)
Inductive match_split_drop_places flagm : own_env -> list (place * bool) -> statement -> Prop :=
| match_sdp_nil: forall own,
    match_split_drop_places flagm own nil Sskip
| match_sdp_cons_flag: forall p flag own l ts full
    (FLAG: get_dropflag_temp flagm p = Some flag)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full (Some flag)) ts)
| match_sdp_cons_must_init: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_owned own p = true),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full None) ts)
| match_sdp_cons_must_uninit: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_owned own p = false),
    (* how to ensure that p is owned in own_env *)
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
.


(* Invariant of generate_drop_flags *)

Definition sound_flagm (body: statement) (cfg: rustcfg) (flagm: FM) (init uninit: PMap.t PathsMap.t) (universe: PathsMap.t) :=
  forall pc next p sel,
    cfg ! pc = Some (Isel sel next) ->
    select_stmt body sel = Some (Sdrop p) ->
    get_dropflag_temp flagm p = None ->
    (* must owned *)
    (must_owned init!!pc uninit!!pc universe p = true \/
       (* must unowned *)
       may_owned init!!pc uninit!!pc universe p = false).

Lemma generate_drop_flags_inv: forall init uninit universe f cfg ce flags entry
  (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
  (GEN: generate_drop_flags init uninit universe ce f cfg = OK flags),
  sound_flagm f.(fn_body) cfg (generate_place_map flags) init uninit universe.
Admitted.


Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Hypothesis TRANSL: match_prog prog tprog.
Variable w: injp_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := globalenv tse tprog.
Let ce := ge.(genv_cenv).

Let match_stmt (ae: AN) (flagm: FM) := match_stmt get_init_info ae (elaborate_stmt flagm ce).

(* relation between source env and target env including the own_env
and invariant of flags map. [(t)lo] is caller stack blocks and [t(hi)]
is callee stack blocks (including heap blocks), so [(t)lo] ⊆
[(t)[hi]] *)
Record match_envs_flagm (j: meminj) (own: own_env) (e: env) (m: mem) (lo hi: Mem.sup) (te: env) (flagm: FM) (tm: mem) (tlo thi: Mem.sup) : Type :=
  { me_wf_flagm: forall p id,
      get_dropflag_temp flagm p = Some id ->
      exists tb v, te ! id = Some (tb, type_bool)
              /\ e ! id = None    
              /\ Mem.load Mint8unsigned tm tb 0 = Some (Vint v)
              (* TODO: add a rust bool_val *)
              /\ negb (Int.eq v Int.zero) = is_owned own p
              (* protection *)
              /\ (forall ofs, loc_out_of_reach j m tb ofs);

    me_vars: forall id b ty,
      e ! id = Some (b, ty) ->
      exists tb, te ! id = Some (tb, ty)
            /\ j b = Some (tb, 0);

    me_range: forall id b ty,
      e ! id = Some (b, ty) ->
      ~ In b lo /\ In b hi;
    
    me_trange: forall id b ty,
      te ! id = Some (b, ty) ->
      ~ In b tlo /\ In b thi;

    me_incr:
      Mem.sup_include lo hi;
    me_tincr:
      Mem.sup_include tlo thi;    
  }.
    

Inductive match_cont (j: meminj) : AN -> FM -> statement -> rustcfg -> cont -> RustIRsem.cont -> node -> option node -> option node -> node -> mem -> mem -> sup -> sup -> Prop :=
| match_Kseq: forall an flagm body cfg s ts k tk pc next cont brk nret m tm bound tbound
    (MSTMT: match_stmt an flagm body cfg s ts pc next cont brk nret)
    (MCONT: match_cont j an flagm body cfg k tk next cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kseq s k) (RustIRsem.Kseq ts tk) pc cont brk nret m tm bound tbound
| match_Kstop: forall an flagm body cfg nret m tm bound tbound
    (RET: cfg ! nret = Some Iend),
    match_cont j an flagm body cfg Kstop RustIRsem.Kstop nret None None nret m tm bound tbound
| match_Kloop: forall an flagm body cfg s ts k tk body_start loop_jump_node exit_loop nret contn brk m tm bound tbound
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an flagm body cfg s ts body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: match_cont j an flagm body cfg k tk exit_loop contn brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kloop s k) (RustIRsem.Kloop ts tk) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret m tm bound tbound
| match_Kcall: forall an flagm body cfg k tk nret f tf le tle own p m tm bound tbound
    (MSTK: match_stacks j (Kcall p f le own k) (RustIRsem.Kcall p tf tle tk) m tm bound tbound)
    (RET: cfg ! nret = Some Iend),
    (* in the end of a function. an and body are not important, those
    in match_stacks are important *)
    match_cont j an flagm body cfg (Kcall p f le own k) (RustIRsem.Kcall p tf tle tk) nret None None nret m tm bound tbound
| match_Kdropcall: forall an flagm body cfg k tk pc cont brk nret st membs b tb ofs tofs id m tm bound tbound
    (INJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (MCONT: match_cont j an flagm body cfg k tk pc cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kdropcall id (Vptr b ofs) st membs k) (RustIRsem.Kdropcall id (Vptr tb tofs) st membs tk) pc cont brk nret m tm bound tbound
| match_Kdropplace: forall f tf st l k tk e te own1 own2 flagm cfg nret cont brk pc ts1 ts2 m tm lo tlo hi thi maybeInit maybeUninit universe
    (** Do we need match_stacks here?  *)
    (TRFUN: tr_fun f nret cfg)
    (AN: analyze ce f = OK (maybeInit, maybeUninit, universe))
    (MSTK: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc cont brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (OWN: sound_own own2 maybeInit!!pc maybeUninit!!pc universe)
    (MOVESPLIT: move_split_places own1 l own2),
    (* source program: from dropplace to droopstate, target: from
    state to dropstate. So Kdropplace matches Kcall *)
    match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg (Kdropplace f st l e own1 k) (RustIRsem.Kcall None tf te (RustIRsem.Kseq (Ssequence ts1 ts2) tk)) pc cont brk nret m tm hi thi

with match_stacks (j: meminj) : cont -> RustIRsem.cont -> mem -> mem -> sup -> sup -> Prop :=
| match_stacks_stop: forall m tm bound tbound,
    match_stacks j Kstop (RustIRsem.Kstop) m tm bound tbound
| match_stacks_call: forall flagm f tf nret cfg pc contn brk k tk own1 own2 p le tle m tm lo tlo hi thi maybeInit maybeUninit universe
    (TRFUN: tr_fun f nret cfg)
    (AN: analyze ce f = OK (maybeInit, maybeUninit, universe))   
    (* callee use stacks hi and thi, so caller f uses lo and tlo*)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc contn brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm tlo thi)
    (SFLAGM: sound_flagm f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* own2 is built after the function call *)
    (AFTER: own2 = match p with
                   | Some p => move_place own1 p
                   | None => own1 end)
    (OWN: sound_own own2 maybeInit!!pc maybeUninit!!pc universe),
    match_stacks j (Kcall p f le own1 k) (RustIRsem.Kcall p tf tle tk) m tm hi thi
.

Inductive match_states : state -> RustIRsem.state -> Prop := 
| match_regular_state:
  forall f s k e own m tf ts tk te tm j flagm maybeInit maybeUninit universe cfg nret cont brk next pc Hm lo tlo hi thi
    (AN: analyze ce f = OK (maybeInit, maybeUninit, universe))
    (TRFUN: tr_fun f nret cfg)
    (MSTMT: match_stmt (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg s ts pc next cont brk nret)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* well-formedness of the flag map *)
    (MENV: match_envs_flagm j own e m lo hi te flagm tm tlo thi)
    (* property of flagm when encounting drop statement *)
    (SFLAGM: sound_flagm f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* Put sound_own here which may be inevitable due to the
    flow-insensitiveness of RustIR semantics.*)
    (SOUNDOWN: sound_own own maybeInit!!pc maybeUninit!!pc universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (State f s k e own m) (RustIRsem.State tf ts tk te tm)
| match_drppplace: forall f tf st l k tk e te own1 own2 m tm j flagm  maybeInit maybeUninit universe cfg nret cont brk next ts1 ts2 Hm lo tlo hi thi
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* maybe difficult: transition of own is small step! *)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* small-step move_place to simulate big-step move_place in
    transfer. maybe difficult to prove *)
    (MOVESPLIT: move_split_places own1 l own2)
    (OWN: sound_own own2 maybeInit!!next maybeUninit!!next universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (Dropplace f st l k e own1 m) (RustIRsem.State tf ts1 (RustIRsem.Kseq ts2 tk) te tm)
| match_dropstate: forall k tk m tm j flagm maybeInit maybeUninit universe body cfg nret cont brk next b ofs tb tofs st membs id lo tlo Hm
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm body cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (* no new stacks block in dropstate *)
    (BOUND: Mem.sup_include lo (Mem.support m))
    (TBOUND: Mem.sup_include tlo (Mem.support tm)),
    match_states (Dropstate id (Vptr b ofs) st membs k m) (RustIRsem.Dropstate id (Vptr tb tofs) st membs tk tm)
| match_callstate: forall j vf tvf m tm vargs tvargs k tk Hm
    (VINJ: Val.inject j vf tvf)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (AINJ: Val.inject_list j vargs tvargs)
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Callstate vf vargs k m) (RustIRsem.Callstate tvf tvargs tk tm)
| match_returnstate: forall j v tv m tm k tk Hm
    (VINJ: Val.inject j v tv)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Returnstate v k m) (RustIRsem.Returnstate tv tk tm)
. 

(** This property is difficult to prove! *)
Inductive wf_split_drop_places flagm (init uninit universe: PathsMap.t) : own_env -> list (place * bool) -> Prop :=
| wf_sdp_nil: forall own,
    wf_split_drop_places flagm init uninit universe own nil
| wf_sdp_flag: forall own b id l p
    (FLAG: get_dropflag_temp flagm p = Some id)
    (WF: wf_split_drop_places flagm init uninit universe (move_place own p) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
| wf_sdp_must: forall own b l p
    (FLAG: get_dropflag_temp flagm p = None)
    (OWN: must_owned init uninit universe p = is_owned own p)
    (WF: wf_split_drop_places flagm init uninit universe (move_place own p) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
.
    
Lemma elaborate_drop_match_drop_places:
  forall drops flagm own init uninit universe
    (** we need some restriction on drops!! *)
    (WFDROPS: wf_split_drop_places flagm init uninit universe own drops),
    match_split_drop_places flagm own drops (elaborate_drop_for_splits init uninit universe flagm drops).
Proof.
  induction drops; intros.
  econstructor.
  simpl. destruct a.
  destruct (get_dropflag_temp flagm p) eqn: FLAG.
  - econstructor. auto.
    eapply IHdrops. inv WFDROPS.
    auto. congruence.
  - inv WFDROPS. congruence.
    destruct (must_owned init uninit universe p) eqn: MUST.
    (* must_owned = true *)
    + econstructor; auto.
    (* must_owned = false *)
    + econstructor; auto.
Qed.    
    
(* difficult part is establish simulation (match_split_drop_places)
when entering dropplace state *)
Lemma step_dropplace_simulation:
  forall S1 t S2, step_dropplace ge S1 t S2 ->
   forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropplace_init1 *)
  - inv MDPS.
    (** Two cases of skipping this drop: one is must uninit and the
    other is drop flag is false *)
    inv MSPLIT.
    (* there is drop flag and the value of drop flag is false *)
    + exploit me_wf_flagm; eauto.
      intros (tb & v & TE & LE & LOAD & ISOWN & OUTREACH).
      simpl.
      eexists. split.
      (* step in target *)
      * 
              
    admit.
Admitted.

(** REMOVE IT: This lemma is impossible to prove: because the
semantics is flow-insensitive so that we do not know whether or not s
in match_stmt locates in the same branch as the s in tr_stmt. So pc1 =
pc2 is impossible. *)
Lemma match_stmt_cont_unique: forall k tk an fm body cfg s ts pc1 next1 cont1 brk1 nret j m tm lo tlo pc2 next2 cont2 brk2,
    match_stmt an fm body cfg s ts pc1 next1 cont1 brk1 nret ->
    match_cont j an fm body cfg k tk next1 cont1 brk1 nret m tm lo tlo ->
    tr_stmt body cfg s pc2 next2 cont2 brk2 nret ->
    tr_cont body cfg k next2 cont2 brk2 nret ->
    pc1 = pc2 /\ next1 = next2 /\ cont1 = cont2 /\ brk1 = brk2.
Proof.
  induction k; intros until brk2; intros MSTMT MCONT TRSTMT TRCONT.
  (* Sskip *)
  - inv MCONT. inv TRCONT.
    (* how to prove pc1 = pc2: match_stmt and tr_stmt with same next
    node have the same pc *)
    admit.
  (* Kseq *)
  - inv MCONT. inv TRCONT.
    assert (MSTMT1: match_stmt an fm body cfg (Ssequence s0 s) (Ssequence ts ts0) pc1 next cont1 brk1 nret).
    { econstructor; eauto. }
    assert (TRSTMT1: tr_stmt body cfg (Ssequence s0 s) pc2 next0 cont2 brk2 nret).
    { econstructor; eauto. }
    exploit IHk.
    eapply MSTMT1. eauto.
    eapply TRSTMT1. eauto. intros (A & B & C & D).
    subst.
    repeat split; eauto.
    (* how to prove pc1 = pc2: match_stmt and tr_stmt with same next
    node have the same pc *)
    admit.
Abort.

    
Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 -> forall S1' (MS: match_states S1 S1'),
    exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof. 
  induction 1; intros; inv MS.
  (* step_assign *)
  - inv MSTMT.
    simpl in TR. 
    admit.
  (* step_assign_variant *)
  - admit.
  (* step_box *)
  - admit.
  (* step_to_dropplace *)
  - inv MSTMT. simpl in TR.
    unfold elaborate_drop_for in TR.
    (** sound_own property *)
    assert (UNIEQ: PathsMap.eq (own_universe own) universe0) by admit.
    erewrite split_drop_place_eq_universe in TR.
    unfold ce in TR. erewrite SPLIT in TR.
    2: { symmetry. eapply UNIEQ. }
    inv TR.
    (* end of getting ts *)
    (* how to prevent stuttering? *)
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. eauto.
    (* match_states *)
    econstructor; eauto.
    econstructor.
    (* match_split_drop_places *)
    eapply elaborate_drop_match_drop_places.
    (** IMPORTANT TODO: wf_split_drop_places *)
    admit.
  (* step_in_dropplace *)
  - admit.


    
Lemma transf_initial_states q:
  forall S1, initial_state ge q S1 ->
  exists S2, RustIRsem.initial_state tge q S2 /\ match_states S1 S2.
Proof.
Admitted. 

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> RustIRsem.final_state S2 r.
Proof.
Admitted. 

Lemma transf_external:
  forall S R q, match_states S R -> at_external ge S q ->
  RustIRsem.at_external tge R q /\
  forall r S', after_external S r S' ->
  exists R', RustIRsem.after_external R r R' /\ match_states S' R'.
Proof.
  intros S R q HSR Hq. destruct Hq; inv HSR.
Qed. 

Lemma transf_fundef_internal: 
forall q se2,
Genv.is_internal (Genv.globalenv se2 tprog) (cq_vf q) =
Genv.is_internal (Genv.globalenv se2 prog) (cq_vf q). 
Admitted. 

End PRESERVATION.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_id) (cc_id) (semantics prog) (RustIRsem.semantics tprog).
Proof.
    fsim eapply forward_simulation_plus; simpl in *. 
    - inv MATCH. simpl. auto. 
    - intros. inv H. eapply transf_fundef_internal; eauto. 
    - intros. inv H. eapply transf_initial_states. eauto.  
    - intros. exploit transf_final_states; eauto. 
    - intros. edestruct transf_external; eauto. exists tt, q1. intuition subst; eauto.
    - eauto using step_simulation.
Admitted. 
