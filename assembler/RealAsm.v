Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import Floats.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import RealAsmArchi.

Section INSTRSIZE.
Variable instr_size : instruction -> Z.

Inductive initial_state (p: Asm.program): state -> Prop :=
  | initial_state_intro: forall m0 m' rs0,
      Genv.init_mem p = Some m0 ->
      initial_stack_regset p m0 m' rs0 ->      
      initial_state p (State rs0 m').

Definition semantics prog :=
  Semantics (RealAsmArchi.step instr_size) (initial_state prog) final_state (Genv.globalenv prog).

Section RECEPTIVEDET.

  Theorem real_asm_single_events p:
    single_events (semantics p).
  Proof.
    red. simpl. intros s t s' STEP.
    inv STEP; simpl. lia.
    eapply external_call_trace_length; eauto.
    (* eapply external_call_trace_length; eauto. *)
  Qed.

  Theorem real_asm_receptive p:
    receptive (semantics p).
  Proof.
    split.
    - simpl. intros s t1 s1 t2 STEP MT.
      inv STEP.
      inv MT. eexists. eapply exec_step_internal; eauto.
      edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      (* eexists. eapply exec_step_builtin; eauto. *)
      (* edestruct external_call_receptive as (vres2 & m2 & EC2); eauto. *)
      eexists. eapply exec_step_external; eauto.
    - eapply real_asm_single_events; eauto.
  Qed.

  Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.

  Theorem real_asm_determinate p :
    determinate (semantics p).
  Proof.
    split.
    - simpl; intros s t1 s1 t2 s2 STEP1 STEP2.
      eapply semantics_determinate_step;eauto.
    - apply real_asm_single_events.
    - simpl. intros s1 s2 IS1 IS2; inv IS1; inv IS2. rewrite_hyps.
      inv H0; inv H2. rewrite_hyps. unfold rs0, rs2, ge, ge0 in *. rewrite_hyps. congruence.
    - simpl. intros s r FS.
      red. intros t s' STEP.
      inv FS.
      unfold Vnullptr in *. destruct Archi.ptr64;inv STEP;rewrite_hyps. 
    - simpl. intros s r1 r2 FS1 FS2.
      inv FS1; inv FS2. congruence.
  Qed.

End RECEPTIVEDET.

End INSTRSIZE.
