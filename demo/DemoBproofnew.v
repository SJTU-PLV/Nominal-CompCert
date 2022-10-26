Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler CA.

Require Import CKLRAlgebra Extends Inject InjectFootprint.

(* forget it for now
Search wt_c.
*)

Section injp_CA.

Lemma injp_CA: forward_simulation
                 (cc_c injp @ cc_c_asm)
                 (cc_c injp @ cc_c_asm)
                 Bspec (Asm.semantics prog).
Proof.
 Admitted.

(*
Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply injp_protection.
  eapply compose_forward_simulations.
  eapply self_wt.
  rewrite <- !(cc_compose_assoc) at 1.
  eapply compose_forward_simulations.
  rewrite cc_compose_assoc at 1.
  rewrite cc_compose_assoc at 1.
  rewrite <- cc_ca_cllmma at 1.
  rewrite cc_cllmma_ca.
  eapply CA.
  eapply semantics_asm_rel; eauto.
Qed.
*)
