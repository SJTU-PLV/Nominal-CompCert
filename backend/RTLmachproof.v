Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep CKLR LanguageInterface Inject InjectFootprint.
Require Import Op Registers RTL RTLmach.
Require Tailcallproof.

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
Variable w: world inj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Let ge : RTL.genv := Genv.globalenv se prog.
Let tge: genv := Genv.globalenv tse tprog.

Hypothesis GE: match_stbls inj w se tse.

Lemma prog_eq : prog = tprog.
Proof. auto. Qed.

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

Lemma functions_translated (j: meminj):
  Genv.match_stbls j se tse ->
  forall (v tv: val) (f: RTL.fundef),
  Val.inject j v tv -> Genv.find_funct ge v = Some f ->
  Genv.find_funct tge tv = Some f.
Proof.
  intros.
  exploit Genv.find_funct_inv. eauto. intros [b EQ]. subst v. inv H0. rewrite Ptrofs.add_zero_l.
  rewrite Genv.find_funct_find_funct_ptr in H1. unfold Genv.find_funct_ptr in H1.
  destruct Genv.find_def as [[|]|] eqn:Hf; try congruence. inv H1.
  exploit @Genv.globalenvs_match. red. intuition idtac.
    instantiate (1 := prog). instantiate (2 := fun x y => x = y). instantiate (2 := fun x y z => y = z).
    generalize (prog_defs prog). induction l; constructor; auto.
    red. split. auto. destruct (snd a); econstructor; auto. reflexivity.
    destruct v. constructor. auto. eauto.
  intros MGE.
  unfold Genv.find_def in Hf.
  assert (sup_In b (Genv.genv_sup ge)) by eauto using Genv.genv_defs_range.
  edestruct Genv.mge_dom; eauto. simpl in Hf.
  pose proof (Genv.mge_defs MGE b H1). inv H2. congruence.
  rewrite Hf in H3. inv H3. inv H6.
  unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
  rewrite H1 in H4. inv H4. destr. 2:unfold Ptrofs.zero in n; congruence.
  simpl. rewrite <- TRANSL, <- H5. auto.
  Unshelve. exact tt.
Qed.

Lemma symbols_preserved:
  forall j id ofs,
  Genv.match_stbls j se tse ->
  Val.inject j (Genv.symbol_address se id ofs) (Genv.symbol_address tse id ofs).
Proof.
  intros.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
  edestruct @Genv.find_symbol_match as (b' & Hb' & H'); eauto.
  rewrite H'. econstructor; eauto. rewrite Ptrofs.add_zero. auto.
Qed.


Lemma ros_address_translated:
  forall j ros rs rs',
  regset_inject j rs rs' ->
  Genv.match_stbls j se tse ->
  Val.inject j (ros_address se ros rs) (ros_address tse ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
  apply symbols_preserved. auto.
Qed.

Lemma lessdef_list_refl : forall s,
    Val.lessdef_list s s.
Proof.
  induction s; eauto.
Qed.

Inductive match_stackadt : nat -> Memory.stackadt -> Memory.stackadt -> Prop :=
  | match_stackadt_nil: forall
      (IHsize: stack_size (Mem.astack (injw_sup_l w)) >= stack_size (Mem.astack (injw_sup_r w))),
      match_stackadt O (Mem.astack (injw_sup_l w)) (Mem.astack (injw_sup_r w))
  | match_stackadt_cons: forall n s1 s2 t1 t1' frame,
     match_stackadt n s1 s2 ->
     t1 = frame::t1' ->
     match_stackadt (S n) (t1::s1) ((frame::nil)::s2).

Lemma match_stackadt_size : forall n s1 s2,
    match_stackadt n s1 s2 ->
    Memory.stack_size s2 <= Memory.stack_size s1.
Proof.
  intros. induction H.
  - lia.
  - simpl. rewrite H0. simpl in *.
    generalize (Memory.size_of_all_frames_pos t1').
    lia.
Qed.

Inductive match_stackframes (j: meminj):
  nat -> list nat -> list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      meminj_preserves_globals ge j ->
      meminj_global j ->
      match_stackframes j 0 nil nil nil
  | match_stackframes_normal: forall n l stk stk' res sp sp' pc rs rs' f,
      match_stackframes j n l stk stk' ->
      regset_inject j rs rs' ->
      j sp = Some (sp',0) ->
      match_stackframes j 0 ((S n)::l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res f (Vptr sp' Ptrofs.zero) pc rs' :: stk').

Lemma match_stackframes_global : forall j n l stk stk',
    match_stackframes j n l stk stk' ->
    meminj_preserves_globals ge j /\ meminj_global j.
Proof.
  intros. induction H; auto.
Qed.

Lemma match_stackframes_incr : forall j j' stk stk' n l,
    match_stackframes j n l stk stk' ->
    inject_incr j j' ->
    incr_without_glob j j' ->
    match_stackframes j' n l stk stk'.
Proof.
  intros.
  induction H; constructor; auto.
  - inversion H. inv H4.
    split. eauto.
    split. intros.
    apply Genv.find_var_info_iff in H4 as A.
    apply Genv.genv_info_range in A.
    (* apply Genv.genv_defs_range in A. *)
    apply Genv.genv_sup_glob in A. destruct A. subst. eauto.
    intros.
    destruct (j b1) eqn:?.
    + destruct p. apply H0 in Heqo as H8. rewrite H7 in H8.
      inv H8.
      exploit H6. eauto. eauto. auto.
    + exploit H1; eauto.
    apply Genv.find_var_info_iff in H4 as A. apply Genv.genv_info_range in A.
    apply Genv.genv_sup_glob in A. destruct A. subst.
    intros [A B]. inv B.
  - unfold meminj_global in *. intros.
    destruct (j (Global id)) eqn:?. destruct p.
    apply H0 in Heqo as H4. rewrite H3 in H4. inv H4.
    apply H2 in Heqo. inv Heqo. auto.
    exploit H1; eauto. intros [A B]. inv A.
  - eapply regset_inject_incr; eauto.
Qed.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall j f s s' sp sp' pc rs rs' m m' n l
        (STACKS: match_stackframes j n l s s')
        (ASTK: match_stackadt (S (length s)) (Mem.astack (Mem.support m)) (Mem.astack (Mem.support m')))
        (RINJ: regset_inject j rs rs')
        (MINJ: Mem.inject j m m')
        (SP: j sp = Some (sp', 0))
        (INCR: inj_incr_without_astack w (injw j (Mem.support m) (Mem.support m'))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' f (Vptr sp' Ptrofs.zero) pc rs' m')
  | match_callstates: forall j s s' vf vf' args args' m m' id hd tl n l
        (STACKS: match_stackframes j n l s s')
        (FINJ: Val.inject j vf vf')
        (AINJ: Val.inject_list j args args')
        (MINJ: Mem.inject j m m')
        (Heqastk: Mem.astack (Mem.support m) = hd :: tl)
        (ASTK: match_stackadt (length s) tl (Mem.astack (Mem.support m')))
        (INCR: inj_incr_without_astack w (injw j (Mem.support m) (Mem.support m'))),
      match_states (Callstate s vf args m id)
                   (Callstate s' vf' args' m' id)
  | match_returnstates: forall j s s' v v' m m' hd tl n l
        (STACKS: match_stackframes j n l s s')
        (VINJ: Val.inject j v v')
        (MINJ: Mem.inject j m m')
        (Heqastk: Mem.astack (Mem.support m) = hd :: tl)
        (ASTK: match_stackadt (length s) tl (Mem.astack (Mem.support m')))
        (INCR: inj_incr_without_astack w (injw j (Mem.support m) (Mem.support m'))),
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

Lemma step_simulation:
  forall S1 t S2, RTL.step fn_stack_requirements ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.

  - (* nop *)
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.

  - (* op *)
    assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
    exploit eval_operation_inject; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intros [v' [EVAL' VINJ]].
    rewrite eval_shift_stack_operation in EVAL'. eauto.
    econstructor; eauto. split.
    eapply exec_Iop; eauto.
    econstructor; eauto. apply set_reg_inject; auto.

  - (* load *)
    assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
    exploit eval_addressing_inject; eauto. eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intros [a' [ADDR' AINJ]].
    exploit Mem.loadv_inject; eauto.
    intros [v' [LOAD' VINJ]].
    econstructor; eauto. split.
    eapply exec_Iload with (a := a'). eauto.
    rewrite eval_shift_stack_addressing in ADDR'. auto. eauto.
    econstructor; eauto. apply set_reg_inject; auto.

  - (* store *)
    assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
    exploit eval_addressing_inject; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intros [a' [ADDR' AINJ]].
    exploit Mem.storev_mapped_inject. 2: eexact H3. eauto. eauto. apply RINJ.
    intros [m'1 [STORE' MINJ']].
    eexists. split.
    eapply exec_Istore with (a := a'). eauto.
    rewrite eval_shift_stack_addressing in ADDR'. rewrite <- ADDR'. auto. eauto.
    destruct a; simpl in H1; try discriminate.
    apply Mem.support_store in H3 as S.
    apply Mem.support_storev in STORE' as S'.
    econstructor; eauto. congruence.
    rewrite S, <- S'. auto.

  - (* call *)
    apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
    exploit functions_translated.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    2:eauto. apply ros_address_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intro FIND'.
    econstructor; eauto. split.
    eapply exec_Icall; eauto. eapply Tailcallproof.ros_is_ident_translated; eauto.
    econstructor. constructor; eauto.
    apply ros_address_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    apply regs_inject; auto. eapply Mem.push_stage_left_inject; eauto.
    simpl. eauto. auto. destruct w. inv INCR. constructor; auto.

  - (* tailcall *)
    apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
    exploit functions_translated.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    2:eauto. apply ros_address_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intro FIND'.
    exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE INJ]].
    apply Mem.support_free in H5 as SF. apply Mem.support_free in FREE as SF'.
    pose proof Mem.nonempty_pop_stage m'1. destruct X as (m'2 & POP).
    inv ASTK. congruence.
    destruct (Mem.astack (Mem.support m')) eqn:CONS. congruence.
    eexists. split.
    eapply exec_Itailcall; eauto. eapply Tailcallproof.ros_is_ident_translated; eauto.
    rewrite ! Z.add_0_r in FREE. eauto.
    econstructor. eauto.
    apply ros_address_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    apply regs_inject. auto.
    eapply Mem.pop_stage_right_inject; eauto.
    eauto.
    inv ASTK. rewrite <- SF, CONS in H7. inv H7.
    apply Mem.astack_pop_stage in POP as [hd EQ].
    rewrite <- SF', EQ in H8. inv H8. auto.
    rewrite SF. inv INCR. constructor; auto.
    red. intros. rewrite <- Mem.support_pop_stage_1. 2:eauto.
    rewrite SF'. auto.

  - (* builtin *)
    apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
    exploit Tailcallproof.eval_builtin_args_inject; eauto.
      eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intros (vargs' & P & Q).
    exploit Mem.push_stage_inject; eauto. intro.
    exploit external_call_mem_inject'. 2:eauto.
      eapply inj_stbls_subrel' in GE; eauto. apply GE.
      apply Mem.push_stage_left_inject. eauto. eauto. simpl.
    intros [f' [v' [m'1 [A [B [C [D [E [F [G [I [J K]]]]]]]]]]]].
    exploit Mem.pop_stage_left_inject; eauto. intros EXT'.
    eexists. split.
    eapply exec_Ibuiltin; eauto.
    econstructor. 4:eauto. all:eauto.
    eapply match_stackframes_incr; eauto.
    apply Mem.astack_pop_stage in H4 as [hd EQ]. rewrite EQ in F. inv F. congruence.
    apply set_res_inject; eauto. eapply regset_inject_incr; eauto.
    etransitivity. eauto. constructor; auto; red; intros.
    apply Mem.unchanged_on_support in D. apply D in H6.
    rewrite Mem.support_pop_stage_1 in H6; eauto.
    apply Mem.unchanged_on_support in E. apply E in H6. auto.

  - (* cond *)
    econstructor; eauto. split.
    eapply exec_Icond; eauto.
    apply eval_condition_inject with j (rs##args) m; auto. apply regs_inject; auto. eauto.
    econstructor; eauto.

  - (* jumptable *)
    econstructor; eauto. split.
    eapply exec_Ijumptable; eauto.
    generalize (RINJ arg). rewrite H2. intro. inv H. auto.
    econstructor; eauto.

  - (* return *)
    exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE INJ]].
    apply Mem.support_free in H2 as SF. apply Mem.support_free in FREE as SF'.
    pose proof Mem.nonempty_pop_stage m'1 as [m'2 POP].
      rewrite SF'. inv ASTK. congruence.
    eexists. split.
    eapply exec_Ireturn; eauto.
    rewrite ! Z.add_0_r in FREE. eauto.
    destruct (Mem.astack (Mem.support m')) eqn:Heqm'. congruence.
    econstructor. eauto.
    inv ASTK. apply Mem.astack_pop_stage in POP as [hd EQ].
    rewrite SF' in EQ. rewrite EQ in H4. inv H4.
    destruct or; simpl. apply RINJ. constructor.
    exploit Mem.pop_stage_right_inject; eauto.
    eauto.
    inv ASTK. clear H3.
    rewrite SF, <- H0 in Heqm'. inv Heqm'.
    apply Mem.astack_pop_stage in POP as POPRES. destruct POPRES as [hd POP'].
    congruence.
    inv INCR. constructor; auto.
    red. intros. rewrite SF. auto.
    red. intros. rewrite <- Mem.support_pop_stage_1. rewrite SF'. auto. auto.

  - (* internal call *)
    exploit functions_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intro FIND'.
    exploit Mem.alloc_parallel_inject; eauto.
      instantiate (1 := 0). lia.
      instantiate (1 := fn_stacksize f). lia.
    intros (f' & m'1 & b2 & ALLOC & INJ' & INCR' & GLOB' & TSP & INC).
    apply Mem.astack_record_frame in H2 as ASTK1.
    apply Mem.record_frame_size1 in H2 as SIZE.
    destruct ASTK1 as (hd' & tl' & ASTKm' & ASTKm''). rewrite ASTKm' in SIZE.
    erewrite <- Mem.astack_alloc in Heqastk; eauto. rewrite ASTKm' in Heqastk. inv Heqastk.
    exploit Mem.record_frame_parallel_inject. 2:eauto.
      apply Mem.push_stage_right_inject. eauto.
      simpl. congruence.
      simpl. erewrite Mem.astack_alloc; eauto. rewrite ASTKm'.
      apply match_stackadt_size in ASTK.
      simpl. pose proof size_of_all_frames_pos hd. lia.
    intros (m'2 & RECORD & INJ'').
    apply Mem.astack_record_frame in RECORD as ASTK2.
    destruct ASTK2 as (hd' & tl' & ASTKm'1 & ASTKm'2).
    simpl in ASTKm'1. inv ASTKm'1.
    econstructor; split.
    simpl. eapply exec_function_internal; eauto.
    econstructor.
    eapply match_stackframes_incr; eauto.
    rewrite ASTKm'2, ASTKm''. econstructor. erewrite Mem.astack_alloc; eauto. eauto.
    apply Tailcallproof.init_regs_inject.
    eapply val_inject_list_incr; eauto. auto. auto.
    assert (SPS: b2 = fresh_block (Mem.support m'0)) by (eapply Mem.alloc_result; eauto).
    eapply Tailcallproof.mit_incr_invariant. apply INCR'.
    auto.
    instantiate (1 := (Mem.support m'0)).
    inv INCR. simpl.
    intros. destruct (eq_block b1 stk).
      subst b1. rewrite TSP in H0; inv H0.
        apply Mem.alloc_result in H1. subst.
        exfalso. destruct H3; eapply freshness; eauto.
      rewrite INC in H0; auto.
    inv INCR. simpl. auto.
    eauto.
    red. intros. rewrite <- Mem.support_record_frame_1. 2:eauto.
    apply Mem.support_alloc in H1. rewrite H1.
    apply Mem.mem_incr_2. auto.
    red. intros. rewrite <- Mem.support_record_frame_1. 2:eauto.
    erewrite Mem.support_push_stage.
    apply Mem.support_alloc in ALLOC. rewrite ALLOC.
    apply Mem.mem_incr_2. auto. auto.

  - (* external call *)
    exploit functions_translated; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intro FIND'.
    exploit external_call_mem_inject'; eauto.
    eapply inj_stbls_subrel' in GE; eauto. apply GE.
    intros (f' & res' & m2' & A & B & C & D & E & F & G & I & J & K).
    exists (Returnstate s' res' m2'); split.
    simpl. econstructor; eauto.
    econstructor. eapply match_stackframes_incr; eauto.
    auto. auto. rewrite <- F. eauto. rewrite <- G. auto.
    etransitivity; eauto.
    apply Mem.unchanged_on_support in D.
    apply Mem.unchanged_on_support in E.
    constructor; auto.

  - (* returnstate *)
    inv STACKS.
    econstructor; split.
    apply exec_return. econstructor; eauto.
    apply Mem.astack_pop_stage in H1. destruct H1.
    rewrite H in Heqastk. inv Heqastk. simpl in ASTK. auto.
    apply set_reg_inject; auto.
    eapply Mem.pop_stage_left_inject; eauto.
    inv INCR. constructor; auto; red; intros.
    erewrite <- Mem.support_pop_stage_1. 2:eauto. auto.
Qed.

Lemma transf_initial_states:
  forall q1 q2 st1, match_query (cc_c inj) w q1 q2 -> RTL.initial_state ge q1 st1 ->
  exists st2, initial_state tge q2 st2 /\ match_states st1 st2.
Proof.
  intros. destruct H. inv H0.
  exploit functions_translated; eauto. apply GE. intro FIND.
  exists (Callstate nil vf2 vargs2 m2 id); split.
  econstructor; eauto.
  inv H. inv H2. apply INJG in H5 as [ ]. subst. auto using Ptrofs.add_zero_l.
  inv H2. inv ASTK.
  econstructor; eauto. constructor.
  red. split; [|split]; intros; simpl.

  inv GE. inv inj_stbls_match.
  apply Genv.genv_symb_range in H2 as ?.
  apply mge_dom in H4 as [b' ?].
  eapply mge_symb in H4 as ?. destruct H5. specialize (H5 H2). clear H6.
  apply Genv.genv_vars_eq in H2. apply Genv.genv_vars_eq in H5. subst. auto.

  inv GE. inv inj_stbls_match.
  rewrite Genv.find_var_info_iff in H2.
  apply Genv.genv_info_range in H2 as ?.
  apply Genv.genv_sup_glob in H4 as ?. destruct H5 as (id' & ?). subst.
  apply mge_dom in H4 as [b' ?].
  inv H2. apply INJG in H4 as ?. destruct H2. subst. rewrite H4. auto.

  inv GE. inv inj_stbls_match.
  rewrite Genv.find_var_info_iff in H2.
  apply Genv.genv_info_range in H2 as ?.
  apply Genv.genv_sup_glob in H4 as ?. destruct H6 as (id' & ?). subst.
  apply mge_dom in H4 as [b' ?].
  apply INJG in H4 as ?. destruct H6. subst. simpl in *.
  apply mge_separated in H5 as ?.
  setoid_rewrite mge_info in H2. 2:eauto.
  apply Genv.genv_info_range in H2. rewrite <- H6 in H2.
  apply Genv.genv_sup_glob in H2 as [id'' ?]. subst.
  apply INJG in H5 as [ ]. subst. auto.

  subst. auto.

  subst. simpl. apply Mem.push_stage_left_inject. auto.

  simpl. auto.

  replace (Mem.support m1) with (injw_sup_l w). 2: rewrite <- H4; auto.
  replace (Mem.support m2) with (injw_sup_r w). 2: rewrite <- H4; auto.
  constructor. rewrite <- H4. auto.

  subst. constructor; simpl in *; auto.
  all:red; intros. congruence.
  congruence.
  all:
    (erewrite <- Mem.support_push_stage; [|eauto]);
    (rewrite <- Mem.support_push_stage_1; [|eauto]);
    auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r1, match_states st1 st2 -> RTL.final_state st1 r1 ->
  exists r2, final_state st2 r2 /\ match_reply (cc_c inj) w r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS. inv INCR.
  eexists; split.
  - constructor.
  - apply Mem.astack_pop_stage in H1 as H1'. destruct H1' as [hd' POP].
    rewrite POP in Heqastk. inv Heqastk.
    econstructor.
    split; constructor.
    4:red; intros; rewrite <- Mem.support_pop_stage_1; eauto. all:eauto.
    1,2: inv ASTK; auto.
    constructor; auto.
    inv ASTK. constructor. auto.
    eapply Mem.pop_stage_left_inject; eauto.
Qed.

Lemma transf_external_states:
  forall st1 st2 q1, match_states st1 st2 -> RTL.at_external ge st1 q1 ->
  exists wx q2, at_external tge st2 q2 /\ match_query (cc_c injp) wx q1 q2 /\ match_senv (cc_c injp) wx se tse /\
  forall r1 r2 st1', match_reply (cc_c injp) wx r1 r2 -> RTL.after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states st1' st2'.
Proof.
  intros st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst.
  assert (GE0: Genv.match_stbls j se tse). {
    inv GE. inv INCR. eapply Genv.match_stbls_incr; eauto. rewrite <- H0. simpl. auto.
    rewrite <- H0 in *. simpl in *. split; intro; (exploit DISJOINT; eauto); intros [ ].
    apply inj_stbls_next_l in H3. auto.
    apply inj_stbls_next_r in H3. auto.
  }
  assert (VF: vf' = Vptr (Global id) Ptrofs.zero). {
    inv FINJ. rewrite Ptrofs.add_zero_l.
    apply match_stackframes_global in STACKS as [ ]. apply H1 in H2 as [ ]. subst. auto.
  }
  exploit functions_translated; eauto.
  intro FIND'.
  exists (injpw j m m' MINJ). eexists. intuition idtac.
  - econstructor; eauto.
  - constructor; simpl; auto. constructor; auto.
    apply match_stackframes_global in STACKS as [ ]. auto.
    constructor. apply match_stackadt_size in ASTK. rewrite Heqastk. simpl.
    pose proof size_of_all_frames_pos hd. lia.
    congruence.
  - inv GE. inv INCR. rewrite <- H1 in *. simpl in *. constructor; simpl. auto.
    red. red in inj_stbls_next_l. auto.
    red. red in inj_stbls_next_r. auto.
  - inv H2. destruct H1 as (w' & ACC & CR). inv CR.
    destruct w'. simpl in ACC, H3, H5. inv H5.
    (* destruct H0 as ([ ] & [ ] & H0). inv H0. CKLR.uncklr. *)
    exists (Returnstate s' vres2 m2'). split.
    constructor; auto.
    econstructor.
    inv ACC. eapply match_stackframes_incr; eauto.
    auto. auto.
    inv ACC. rewrite <- ASTK1. eauto.
    inv ACC. rewrite <- ASTK2. auto.
    etransitivity. eauto.
    inv ACC. econstructor; eauto.
    inv UNCHANGED1. eauto. inv UNCHANGED2. eauto.
Qed.

End PRESERVATION.

Theorem transf_program_correct prog tprog fn_stack_requirements:
  match_prog prog tprog ->
  forward_simulation (cc_c injp) (cc_c inj) (RTL.semantics fn_stack_requirements prog) (RTLmach.semantics fn_stack_requirements tprog).
Proof.
  fsim eapply forward_simulation_step.
  - inv MATCH. auto.
  - intros q1 q2 Hq. destruct Hq. cbn in *. inv Hse. cbn in *.
    eapply Genv.is_internal_transf; eauto.
    instantiate (1 := id). red. red. inv MATCH. intuition.
    generalize (prog_defs tprog). induction l; constructor; auto.
    red. intuition. simpl. destruct b; econstructor; auto.
    apply linkorder_refl. destruct v. econstructor. auto.
    auto.
  - eapply transf_initial_states; eauto.
  - eapply transf_final_states; eauto.
  - intros. eapply transf_external_states; eauto.
  - eapply step_simulation; eauto.
Qed.

Instance TransfRTLmachLink : TransfLink match_prog.
Proof.
  red; intros. destruct (link_linkorder _ _ _ H) as (LO1 & LO2).
  eexists p. split. inv H0. inv H1. auto. reflexivity.
Qed.
