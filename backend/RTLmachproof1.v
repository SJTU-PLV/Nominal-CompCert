(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL RTLmach RTLmach1.

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

Lemma stage_size_head_le_all : forall s : Mem.stage,
    Mem.size_of_head_frame s <= Mem.size_of_all_frames s.
Proof.
  intros. induction s.
  - simpl. lia.
  - simpl.  generalize (Mem.size_of_all_frames_pos s).
    lia.
Qed.
Lemma stack_size_mach_le_vm : forall stk : Mem.stackadt,
    Mem.stack_size_mach stk <= Mem.stack_size_vm stk.
Proof.
  intros. induction stk.
  - simpl. lia.
  - simpl. generalize (stage_size_head_le_all a).
    lia.
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
  ros_is_function ge ros rs id ->
  regs_lessdef rs rs' ->
  ros_is_function ge ros rs' id.
Proof.
  unfold ros_is_function. intros.
  destruct ros.
  - destruct H as (b & o & RS & FS).
  specialize (H0 r). rewrite RS in H0; inv H0.
  eexists; eexists; split; eauto.
  - auto.
Qed.

Lemma lessdef_list_refl : forall s,
    Val.lessdef_list s s.
Proof.
  induction s; eauto.
Qed.
Inductive match_stackadt : Mem.stackadt -> Mem.stackadt -> Prop :=
  |match_stackadt_nil : match_stackadt nil nil
  |match_stackadt_cons : forall s1 s2 (t1:Mem.stage) (t1':Mem.stage) (frame:Mem.frame),
     match_stackadt s1 s2 ->
     t1 = frame::t1' ->
     match_stackadt (t1::s1) ((frame::nil)::s2).

Lemma match_stackadt_size : forall s1 s2,
    match_stackadt s1 s2 ->
    Mem.stack_size_mach s1 = Mem.stack_size_mach s2.
Proof.
  intros. induction H.
  - auto.
  - simpl. rewrite H0. simpl. congruence.
Qed.
(* need a Mem_iff invariant 

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m m',
        Mem.extends' m' m ->
        match_stackadt (Mem.stack(Mem.support m)) (Mem.stack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk f sp pc rs m')
  | match_callstates: forall stk f args m sz m' hd tl,
        Mem.extends' m' m ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk f args m' sz)
  | match_returnstates: forall stk v  m m' hd tl,
        Mem.extends' m' m ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk v m').
*)
Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      match_stackframes
        (Stackframe res f sp pc rs :: stk)
        (Stackframe res f sp pc rs' :: stk').

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk stk' f sp pc rs rs' m m',
        regs_lessdef rs' rs ->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        match_stackadt (Mem.stack(Mem.support m)) (Mem.stack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk' f sp pc rs' m')
  | match_callstates: forall stk stk' f args args' m sz m' hd tl,
        Val.lessdef_list args' args->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk' f args' m' sz)
  | match_returnstates: forall stk stk' v v' m m' hd tl,
        Val.lessdef v' v ->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m').


Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

Lemma backward_simulation_step:
  forall S1' t S2', step fn_stack_requirements ge S1' t S2' ->
  forall S1, match_states S1 S1' -> safe (RTLmach.semantics fn_stack_requirements prog) S1 ->
  exists S2, plus (RTLmach.step fn_stack_requirements) ge S1 t S2 /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    apply plus_one. econstructor; eauto.
    econstructor; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_operation_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    econstructor; eauto. split.
    apply plus_one. eapply RTLmach.exec_Iop; eauto.
    econstructor; eauto. apply set_reg_lessdef; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_addressing_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    exploit Mem.loadv_extends'; eauto.
    intros [v'' [LOAD VLD']].
    econstructor; eauto. split. apply plus_one.
    eapply RTLmach.exec_Iload; eauto.
    econstructor; eauto. intro.
    apply set_reg_lessdef; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_addressing_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    exploit Mem.storev_extends'; eauto.
    intros [m2' [STORE VLD']].
    econstructor; eauto. split. apply plus_one.
    eapply RTLmach.exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H4).
    rewrite <- (Mem.support_storev _ _ _ _ _ STORE).
    auto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTLmach.exec_Icall; eauto.
    eapply find_function_id_preserved; eauto.
    eapply find_function_translated; eauto.
    eapply match_callstates; eauto. apply regs_lessdef_regs. auto.
    2: constructor; auto.
    2: constructor; auto.
    {
      inv H12. constructor; simpl; eauto. inv mext_inj.
      constructor; eauto.
    }
  - exploit Mem.free_parallel_extends'; eauto.
    intros [m2' [FREE EXT]].
      destruct (Mem.stack(Mem.support m2')) eqn : S2.
        apply Mem.support_free in FREE. rewrite <- FREE in H16.
        rewrite S2 in H16. inv H16.
        apply Mem.pop_stage_nonempty in H7.
        erewrite Mem.support_free in H7; eauto. congruence.
    econstructor; eauto. split. apply plus_one.
    eapply RTLmach.exec_Itailcall; eauto.
    eapply find_function_id_preserved; eauto.
    eapply find_function_translated; eauto.
    eapply match_callstates; eauto. apply regs_lessdef_regs. auto.
    eapply Mem.pop_stage_left_extends'; eauto.
    eapply Mem.stack_pop_stage in H7.
    destruct H7 as [hd H7].
    rewrite <- (Mem.support_free _ _ _ _ _ FREE) in H16.
    rewrite <- (Mem.support_free _ _ _ _ _ H6) in H16.
    rewrite S2 in H16. rewrite H7 in H16. inv H16.
    auto.
  - exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs0#r)); eauto.
    intros (vargs' & P & Q).
    assert (Mem.extends' m (Mem.push_stage m0)).
    {
      inv H12. constructor; simpl; eauto. inv mext_inj.
      constructor; eauto.
    }
    exploit external_call_mem_extends'. 2: apply H. all:eauto.
    intros [v' [m'1 [A [B [C D]]]]].
    apply external_call_mem_stackeq in A as A'.
    assert ({m'2:mem|Mem.pop_stage m'1 = Some m'2}).
      apply Mem.nonempty_pop_stage.
      rewrite <- A'. simpl. congruence.
    destruct X as [m'2 POP].
    econstructor; eauto. split. apply plus_one.
    eapply RTLmach.exec_Ibuiltin; eauto.
    econstructor; eauto. apply set_res_lessdef; auto.
    eapply Mem.pop_stage_right_extends'; eauto.
    erewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ H4).
    apply Mem.stack_pop_stage in POP. destruct POP as [hd POP].
    rewrite <- A' in POP. simpl in POP. inv POP.
    auto.
  - exists (State stk f sp (if b then ifso else ifnot) rs0 m0); split.
    apply plus_one. eapply RTLmach.exec_Icond; eauto.
    apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
    econstructor; eauto.
  - exists (State stk f sp pc' rs0 m0); split.
    apply plus_one. eapply RTLmach.exec_Ijumptable; eauto.
    generalize (H9 arg). rewrite H3. intro. inv H. auto.
    econstructor; eauto.
  - exploit Mem.free_parallel_extends'; eauto.
    intros [m2' [FREE EXT]].
    apply Mem.stack_pop_stage in H4 as H4'.
    destruct H4' as [hd H4'].
    rewrite <- (Mem.support_free _ _ _ _ _ H3) in H14.
    rewrite H4' in H14.
    inv H14.
    exists (Returnstate stk0 (regmap_optget or Vundef rs0) m2'); split.
    apply plus_one. eapply RTLmach.exec_Ireturn; eauto.
    econstructor; eauto.
    destruct or; simpl. apply H9. constructor.
    eapply Mem.pop_stage_left_extends'; eauto.
    rewrite (Mem.support_free _ _ _ _ _ FREE). inv H. reflexivity.
  - exploit Mem.alloc_extends'; eauto.
      instantiate (1 := 0). lia.
      instantiate (1 := fn_stacksize f). lia.
    intros [m1 [ALLOC EXT]].
    assert ({m2:mem|Mem.record_frame m1 (Mem.mk_frame sz)= Some m2}).
      apply Mem.nonempty_record_frame.
      rewrite (Mem.support_alloc _ _ _ _ _ ALLOC). simpl.  congruence.
      destruct X as [m2 RECORD].
    econstructor. split. apply plus_one.
    econstructor; eauto.
    unfold Mem.record_frame_mach. rewrite RECORD.
    apply zle_true.
    apply Mem.record_frame_mach_result in H3 as H3'.
    apply Mem.record_frame_mach_size in H3 as SIZE.
    apply Mem.stack_record_frame in H3'.
    destruct H3' as (hd'&tl'&A&B). simpl in A. inv A.
    rewrite (Mem.support_alloc _ _ _ _ _ H2) in B. simpl in B.
    rewrite B in SIZE.
    apply Mem.stack_record_frame in RECORD.
    destruct RECORD as (hd''&tl''&A'&B').
    rewrite B'.
    rewrite (Mem.support_alloc _ _ _ _ _ ALLOC) in A'.
    simpl in A'. rewrite A' in H12.
    inv H12.
    apply match_stackadt_size in H13. simpl in *. lia.
    econstructor; eauto.
    apply regs_lessdef_init_regs. auto.
    apply Mem.record_frame_mach_result in H3 as H3'.
    eapply Mem.push_stage_left_extends' in EXT. 2:reflexivity.
    eapply Mem.record_frame_extends'; eauto.
    apply Mem.record_frame_mach_result in H3 as H3'.
    apply Mem.stack_record_frame in H3'.
    destruct H3' as (hd'&tl'&A&B). simpl in A. inv A.
    rewrite (Mem.support_alloc _ _ _ _ _ H2) in B. simpl in B.
    rewrite B.
    apply Mem.stack_record_frame in RECORD.
    destruct RECORD as (hd''&tl''&A'&B').
    rewrite B'.
    rewrite (Mem.support_alloc _ _ _ _ _ ALLOC) in A'.
    simpl in A'. rewrite A' in H12.
    inv H12.
    econstructor; eauto.
  -  exploit external_call_mem_extends'; eauto.
    intros [v' [m1 [A [B [C D]]]]].
    econstructor. split.
    apply plus_one. econstructor. eauto.
    econstructor; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
  - assert ({m1:mem|Mem.pop_stage m0 = Some m1}).
      apply Mem.nonempty_pop_stage. congruence.
      destruct X as [m1 POP].
    inv H7.
    econstructor. split. apply plus_one.
    eapply RTLmach.exec_return; eauto.
    econstructor; eauto. apply set_reg_lessdef; auto.
    eapply Mem.pop_stage_right_extends'; eauto.
    destruct (Mem.stack_pop_stage   _ _ POP).
    rewrite H in H8. inv H8. auto.
Qed.

Definition initial_states_exist:
  forall s1, RTL.initial_state fn_stack_requirements prog s1 ->
             exists s2, initial_state fn_stack_requirements prog s2.
Proof.
  intros. inv TRANSL. inv H.
  exists (Callstate nil f nil m0 (fn_stack_requirements (prog_main tprog))).
  econstructor; eauto.
Qed.

Definition match_initial_states:
  forall s1 s2, RTL.initial_state fn_stack_requirements prog s1 ->
                initial_state fn_stack_requirements tprog s2 ->
  exists s1', RTL.initial_state fn_stack_requirements prog s1' /\ match_states s1' s2.
Proof.
  intros. exists s1. split. auto.
  inv H. inv H0.
  rewrite prog_eq in *.    subst ge0. subst ge1.
  rewrite prog_eq in *.
  rewrite H2 in H5. inv H5.
  rewrite H3 in H6. inv H6.
  rewrite H1 in H. inv H.
  eapply match_callstates; eauto.
  eapply Mem.push_stage_right_extends'; eauto. apply Mem.extends'_refl.
  constructor. simpl. reflexivity.
  apply Genv.init_mem_stack in H1. rewrite H1.
  constructor.
Qed.

Definition match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state s2 r -> RTL.final_state s1 r.
Proof.
  intros. inv H0. inv H. inv H6. inv H3. inv H7.
  constructor.
Qed.
Definition progress:
  forall s1 s2,
  match_states s1 s2 -> safe (RTLmach.semantics fn_stack_requirements prog) s1 ->
  (exists r, RTLmach1.final_state s2 r) \/
  (exists t, exists s2', (step fn_stack_requirements) tge s2 t s2').
Proof.
  Admitted.

End PRESERVATION.



