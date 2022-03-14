Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL RTLmach.

Definition transf_program (p: program) : program := p.

Definition match_prog (p :RTL.program) (tp:program):= p = tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. reflexivity.
Qed.

Section PRESERVATION.

Variables fn_stack_requirements : ident -> Z.
Variables prog: RTL.program.
Variables tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma prog_eq : prog = tprog.
Proof. auto. Qed.

Lemma genv_eq : ge = tge.
Proof.
  unfold match_prog in TRANSL. unfold ge.
  unfold tge. congruence.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function ge ros rs' = Some f.
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. auto.
  destruct (Genv.find_symbol ge i); intros. auto.
  discriminate.
Qed.

Lemma find_function_id_preserved:
  forall ros rs rs' id,
  ros_is_ident ros rs id ->
  regs_lessdef rs rs' ->
  ros_is_ident ros rs' id.
Proof.
  unfold ros_is_ident. intros.
  destruct ros.
  specialize (H0 r). rewrite H in H0. inv H0. auto.
  auto.
Qed.

Lemma lessdef_list_refl : forall s,
    Val.lessdef_list s s.
Proof.
  induction s; eauto.
Qed.

Inductive match_stackadt : Memory.stackadt -> Memory.stackadt -> Prop :=
  |match_stackadt_nil : match_stackadt nil nil
  |match_stackadt_cons : forall s1 s2 (t1:Memory.stage) (t1':Memory.stage) (frame:Memory.frame),
     match_stackadt s1 s2 ->
     t1 = frame::t1' ->
     match_stackadt (t1::s1) ((frame::nil)::s2).

Lemma match_stackadt_nonempty : forall s1 s2,
    match_stackadt s1 s2 ->
    s1 = nil <-> s2 = nil.
Proof.
  intros. inv H.
  - reflexivity.
  - split; congruence.
Qed.

Lemma match_stackadt_size : forall s1 s2,
    match_stackadt s1 s2 ->
    Memory.stack_size s2 <= Memory.stack_size s1.
Proof.
  intros. induction H.
  - lia.
  - simpl. rewrite H0. simpl in *.
    generalize (Memory.size_of_all_frames_pos t1').
    lia.
Qed.

Lemma eval_builtin_arg_memiff:
  forall sp rs m m0 args vargs,
    eval_builtin_arg ge (fun r: positive => rs # r) sp m args vargs ->
    Mem.iff m m0 ->
    eval_builtin_arg ge (fun r: positive => rs # r) sp m0 args vargs.
Proof.
  intros. induction H; constructor; eauto.
  erewrite <- Mem.loadv_iff; eauto.
  erewrite <- Mem.loadv_iff; eauto.
Qed.

Lemma eval_builtin_args_memiff:
  forall (sp : val) (rs : Regmap.t val) (m m0 : mem) (args : list (builtin_arg reg))
    (vargs : list val) (H3 : eval_builtin_args ge (fun r : positive => rs # r) sp m args vargs)
    (H7 : Mem.iff m m0),
    eval_builtin_args ge (fun r : positive => rs # r) sp m0 args vargs.
Proof.
  intros sp rs m m0 args vargs H3 H7.
  unfold eval_builtin_args in *.
  induction H3; constructor; auto.
  eapply eval_builtin_arg_memiff; eauto.
Qed.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m m',
        Mem.iff m m' ->
        match_stackadt (Mem.astack(Mem.support m)) (Mem.astack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk f sp pc rs m')
  | match_callstates: forall stk f args m sz m' hd tl,
        Mem.iff m m' ->
        Mem.astack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.astack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk f args m' sz)
  | match_returnstates: forall stk v  m m' hd tl,
        Mem.iff m m' ->
        Mem.astack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.astack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk v m').

Lemma step_simulation:
  forall S1 t S2, RTL.step fn_stack_requirements ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    eapply exec_Iop; eauto. rewrite <- genv_eq.
    eapply eval_operation_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Iload; eauto.
    erewrite <- Mem.loadv_iff; eauto.
    econstructor; eauto.
  - exploit Mem.storev_iff; eauto.
    intros (m2' & H3' & IFF').
    econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H3).
    rewrite <- (Mem.support_storev _ _ _ _ _ H3').
    auto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Icall; eauto.
    econstructor; eauto.
    eapply Mem.push_stage_left_iff; eauto.
    simpl. reflexivity.
  - edestruct Mem.free_parallel_iff as [m1' []]; eauto.
    inv H14. erewrite <- Mem.astack_return_frame in H7; eauto.
    erewrite Mem.support_free in H7; eauto. congruence.
    edestruct Mem.return_frame_iff as [m'2 []]; eauto.
    assert ({m'3:mem|Mem.pop_stage m'2= Some m'3}).
      apply Mem.nonempty_pop_stage.
      erewrite <- Mem.astack_return_frame. 2: eauto.
      erewrite Mem.support_free. 2: eauto. congruence.
    destruct X as [m'3 POP].
    apply Mem.astack_pop_stage in POP as STKm2'.
    destruct STKm2' as [hd STKm2'].
    econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Itailcall; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    erewrite <- Mem.astack_return_frame. 2: eauto.
    erewrite Mem.support_free. 2: eauto. eauto.
    erewrite <- Mem.support_free in H8; eauto.
    erewrite Mem.astack_return_frame in H8; eauto.
    congruence.
  - exploit Mem.push_stage_left_iff; eauto. intro.
    exploit external_call_mem_iff; eauto. intros (m'1 & EXT &IFF').
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    eapply eval_builtin_args_memiff; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ EXT).
    apply Mem.astack_pop_stage in H4. destruct H4.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H3) in H0.
    simpl in H0. inv H0. auto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Icond; eauto.
    erewrite <- eval_condition_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Ijumptable; eauto.
    econstructor; eauto.
  - edestruct Mem.free_parallel_iff as [m'1[]]; eauto.
    edestruct Mem.return_frame_iff as [m'2[]]; eauto.
    apply Mem.support_free in H2 as SFREE.
    apply Mem.support_free in H as SFREE'.
    apply Mem.astack_return_frame in H3 as ARET.
    apply Mem.astack_return_frame in H5 as ARET'.
    inv H12. congruence.
    assert ({m'3:mem|Mem.pop_stage m'2= Some m'3}).
      apply Mem.nonempty_pop_stage. congruence.
    destruct X as [m'3 POP].
    econstructor; eauto. split.
    eapply exec_Ireturn; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    rewrite <- ARET. rewrite SFREE. eauto.
    apply Mem.astack_pop_stage in POP. destruct POP. congruence.
  - edestruct Mem.alloc_frame_iff as [m'1 []]; eauto.
    edestruct Mem.alloc_parallel_iff as [m'2 []]; eauto.
    apply Mem.astack_alloc_frame in H1 as SAF.
    apply Mem.astack_alloc_frame in H as SAF'.
    apply Mem.support_alloc in H2 as SAL.
    apply Mem.support_alloc in H4 as SAL'.
    exploit Mem.push_stage_right_iff. apply H5. intro.
    apply Mem.astack_record_frame in H3 as ASTK.
    apply Mem.record_frame_size1 in H3 as SIZE. simpl in SIZE.
    destruct ASTK as (hd' & tl' & ASTKm' & ASTKm''). rewrite ASTKm' in SIZE.
    rewrite SAL in ASTKm'.
    unfold sup_incr in ASTKm'. destr_in ASTKm'. simpl in ASTKm'.
    rewrite <- SAF in ASTKm'.
    rewrite H10 in ASTKm'. inv ASTKm'.
    assert ({m'3:mem|Mem.record_frame (Mem.push_stage m'2) (Memory.mk_frame (fn_stack_requirements id)) = Some m'3}).
      apply Mem.request_record_frame. simpl. congruence.
      simpl. rewrite SAL'. unfold sup_incr. destr. simpl.
      rewrite <- SAF'.
      apply match_stackadt_size in H11. simpl in *.
      generalize (size_of_all_frames_pos hd'). lia.
    destruct X as [m'3 RECORD].
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.record_frame_safe_iff; eauto.
    apply Mem.astack_record_frame in RECORD as ASTK.
    destruct ASTK as (hd''&tl''&STKm'1&STKm'2).
    rewrite STKm'2. simpl in STKm'1. inv STKm'1.
    rewrite ASTKm''. econstructor. 2:eauto.
    rewrite SAL'. unfold sup_incr. destr. simpl. rewrite <- SAF'. auto.
  - exploit external_call_mem_iff; eauto.
    intros (m2' & H1'& IFF).
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H1). eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H1'). eauto.
  - apply Mem.stack_pop_stage in H1 as H1'. destruct H1'.
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    apply Mem.astack_pop_stage in H1. destruct H1. rewrite H in H6. inv H6.
    auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv TRANSL. inv H.
  exists (Callstate nil f nil m1 (prog_main tprog)).
  split.
  econstructor; eauto.
  econstructor; eauto.
  eapply Mem.push_stage_left_iff. apply Mem.iff_refl.
  simpl. reflexivity. erewrite Mem.astack_alloc; eauto.
  apply Genv.init_mem_astack in H0. rewrite H0.
  constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. constructor.
Qed.


Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog)
                     (RTLmach.semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_step.
  rewrite prog_eq. auto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.

Instance TransfRTLmachLink : TransfLink match_prog.
Proof.
  red; intros. destruct (link_linkorder _ _ _ H) as (LO1 & LO2).
  eexists p. split. inv H0. inv H1. auto. reflexivity.
Qed.
