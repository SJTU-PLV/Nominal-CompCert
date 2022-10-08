Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler.

Require Import CKLRAlgebra Inject InjectFootprint.

(** * Step1 : self_simulation of Bspec *)

Section SELF_INJP.

Section ms.
Variable w : world injp.

Inductive match_states' : state -> state -> Prop :=
  |match_callstate_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Callstate i m1) (Callstate i m2)
  |match_Interstate_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Interstate i m1) (Interstate i m2)
  |match_Returnstate_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstate i m1) (Returnstate i m2).
End ms.

Theorem self_simulation_C :
  forward_simulation (cc_c injp) (cc_c injp) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => match_states' w s1 s2).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H0. inv H. inv H4. inv H6. inv H2. inv H4. cbn in *.
    inv Hse. inv H7.
    eapply Genv.find_symbol_match in H; eauto. destruct H as [tb [A B]].
    exists (Callstate i m2). split.
    econstructor; eauto. simpl in H1. rewrite H1 in A. inv A.
    rewrite Ptrofs.add_zero. reflexivity.
    econstructor; eauto. reflexivity.
  - intros. inv H; inv H0.
    exists (cr (Vint i) m2). split; econstructor; eauto.
    split. eauto. constructor. simpl. eauto.
    constructor.
  - intros. inv H; inv H0. inversion Hse. subst. eapply Genv.find_symbol_match in H as H'; eauto.
    destruct H' as [tb [A B]]. inv H1.
    exists (injpw f m1 m2 Hm),(cq (Vptr tb Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m2).
    apply Mem.unchanged_on_support in H11 as SUP1.
    apply Mem.unchanged_on_support in H12 as SUP2.
    repeat apply conj; eauto.
    + constructor. eauto.
    + constructor. simpl.
    replace (Vptr tb Ptrofs.zero) with (Vptr tb (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))).
    econstructor; eauto. rewrite Ptrofs.add_zero. reflexivity.
    simpl. constructor. constructor. constructor. constructor. congruence.
    + constructor.
      eapply Genv.match_stbls_incr; eauto.
      intros. exploit H14; eauto. intros [C D].
      unfold Mem.valid_block in *. split; eauto.
      eauto. eauto.
    + intros r1 r2 s1' [w'[ Hw Hr]] F.
      destruct w'. inv F. inv Hr. cbn in *. inv H4.
      inv H6.
      exists (Returnstate (sum i) m2'). split.
      constructor. auto.
      econstructor; eauto.
      etransitivity; eauto. constructor; eauto.
  - intros. inv H0; inv H.
    + exists (Returnstate (sum i) m2). split.
      constructor. econstructor; eauto.
    + exists (Interstate i m2). split.
      constructor; auto. econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End SELF_INJP.

Section WT_C.
  
Theorem self_simulation_wt :
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec Bspec.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [[se1' [se2' sg]] ?]. destruct Hse as [Hse Hse2].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd (snd (fst w)) = int_int_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. inv H. inv H1. cbn in *. inv H. inv H1. exists s1. exists s1.
    split. inv H2. inv H0. simpl. simpl in *.
    inv H. inv H2. inv H5.
    econstructor; eauto. split. reflexivity.
    inv H0. reflexivity.
  - intros. inv H. exists r1.
    split. auto. exists r1. inv H0.
    split; simpl; auto.
    econstructor; simpl. eauto.
    econstructor. constructor.
  - intros. subst.
    exists (se2 , (se2, int_int_sg), tt).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + exists q1. split; inv H0; simpl;  constructor; simpl; eauto.
    + constructor; eauto. simpl. constructor. eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      destruct H as [r3 [A B]].
      inv A. inv B. inv H1. inv H2. constructor. auto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

End WT_C.


Variable BspecL : Smallstep.semantics li_locset li_locset.
Variable BspecM : Smallstep.semantics li_mach li_mach.
Variable BspecA : Smallstep.semantics li_asm li_asm.

Section CL.

Theorem c_locset :
  forward_simulation (cc_c_locset) (cc_c_locset) Bspec BspecL.
Admitted.
End CL.

Section LM.

Theorem locset_mach :
  forward_simulation (cc_locset_mach) (cc_locset_mach) BspecL BspecM.
Admitted.
End LM.

Section MA.

Theorem mach_asm :
  forward_simulation (cc_mach_asm) (cc_mach_asm) BspecM BspecA.
Admitted.
End MA.


Section Ainj.

Theorem asm_simulation_inj:
  forward_simulation (cc_asm inj) (cc_asm inj) BspecA (Asm.semantics DemoB.prog).
Admitted.

End Ainj.

Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply self_simulation_C.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  repeat eapply compose_forward_simulations.
  eapply c_locset. eapply locset_mach. eapply mach_asm.
  eapply asm_simulation_inj.
Qed.

