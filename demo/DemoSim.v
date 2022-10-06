Require Import Coqlib Errors.
Require Import Integers.
Require Import AST.
Require Import LanguageInterface CallconvAlgebra.
Require Import Linking Smallstep SmallstepLinking.
Require Import Compiler.

Require Import SymbolTable DemoA DemoB DemoBspec DemoBproof.

Section Preservation.

Lemma compose_transf_Clight_Asm_correct:
  forall Atprog tp spec,
  compose (Clight.semantics1 DemoA.prog) Bspec = Some spec -> (*can be proofed for the demo*)
  transf_clight_program DemoA.prog = OK Atprog ->
  link Atprog DemoB.prog = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply Bproof.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

End Preservation.

Theorem compile_A_success :
  exists tprog,
  transf_clight_program DemoA.prog = OK tprog.
Proof.
  Admitted.
(*
Section Preservation2.

Variable Bspec : Smallstep.semantics li_c li_c.
Hypothesis Bproof : forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Variable ABspec: Smallstep.semantics li_c li_c.

Hypothesis ABproof : forward_simulation (cc_c injp) (cc_c injp) ABspec 
*)
