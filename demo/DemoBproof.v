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

Theorem self_simulation_C :
  forward_simulation (cc_c injp) (cc_c injp) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  
Admitted.

End SELF_INJP.

Section WT_C.

Theorem self_simulation_wt :
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [[se1' [se2' sg]] ?]. destruct Hse as [Hse Hse2].
  subst. inv Hse.
  eapply forward_simulation_step with (match_states:= eq).
  - intros. inv H. inv H0. cbn in *.
    inv H1. inv H. reflexivity.
  - intros. inv H. inv H1. cbn in *. inv H. inv H1. exists s1.
    split. inv H2. inv H0. simpl. simpl in *.
    inv H. inv H2. inv H5.
    econstructor; eauto. reflexivity.
  - intros. subst.
    inv H0. eexists.
    split.
    constructor.
    eexists. split.
    econstructor. simpl. admit. (*add WT assumptions in Bspec ?? How did they do for wt_c*)
    econstructor. constructor.
  - intros. subst.
    exists (se2 , (se2, int_int_sg), tt).
    exists q1. repeat apply conj; simpl; auto.
    + exists q1. split; inv H0; simpl;  constructor; simpl; eauto.
    + constructor; eauto. simpl. constructor. eauto.
    + intros. exists s1'. split; eauto.
      destruct H as [r3 [A B]].
      inv A. inv B. inv H1. inv H2. constructor. auto.
  - intros. subst. exists s1'. eauto.
  - constructor. intros.
    constructor. inv H.
Admitted.

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

