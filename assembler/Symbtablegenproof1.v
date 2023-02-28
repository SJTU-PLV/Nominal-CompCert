Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen SymbtablegenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics.
Require Import RelocProgSemanticsArchi.
Require Import LocalLib AsmInject.
Require Import  RelocProgGlobalenvs MemoryAgree.
Require Import Symbtablegenproof SymbtablegenproofArchi.
Import ListNotations.

Open Scope Z_scope.
Local Open Scope list_scope.
Close Scope asm.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Section PRESERVATION.
  
(** Transformation *)
Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv instr_size tprog.

Hypothesis TRANSF: match_prog instr_size prog tprog.


Let match_states := match_states instr_size prog tprog.
Let init_mem_pres_inject := init_mem_pres_inject instr_size instr_size_bound prog tprog TRANSF.
Let initial_state_gen_pres_match := initial_state_gen_pres_match instr_size instr_size_bound prog tprog TRANSF.
  
(* set hypothesis *)
Lemma transf_initial_states : forall rs st1,
    RealAsm.initial_state prog st1 ->
    exists st2, initial_state instr_size tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs st1 INIT.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF. 2: congruence. destr_in TRANSF'. 
  inv INIT.
  exploit (init_mem_pres_inject m0);eauto.
  intros (m0' & INITM' & MINJ).

  (* initial state gen preserves injection *)
  exploit (initial_state_gen_pres_match m0 m0' m' rs0 rs);eauto.
  intros (st & INITGEN & MATCH).
  exists st. econstructor. econstructor;eauto.
  unfold match_states. auto.
Qed.



(** ** Matching of the Final States*)
Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.

(** ** The Main Correctness Theorem *)
Lemma transf_program_correct:
  forward_simulation (RealAsm.semantics instr_size prog) 
                     (semantics instr_size tprog (Pregmap.init Vundef)).
Proof.
  intros. apply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    clear init_mem_pres_inject initial_state_gen_pres_match.
    repeat destr_in TRANSF. cbn.
    auto.
    (* rewrite add_external_globals_pres_senv. cbn. auto. *)
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    (* intros. *)
    (* rewrite Pregmap.gi. auto. *)
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.

Instance symbtablegen_transflink:
  TransfLink (match_prog instr_size).
Admitted.

End WITH_INSTR_SIZE.
