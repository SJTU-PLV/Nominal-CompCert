Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.

Require Import Conventions Mach.
Require Import Locations.
Require Import LanguageInterface.

Require Import Integers.
Require Import Values Memory.

Require Import CallconvBig InjectFootprint Injp.
Require Import CAnew.
Require Import Asm Asmrel.
Require Import Asmgenproof0 Asmgenproof1.
Require Import Encrypt EncryptSpec Encryptproof.
Require Import Client Server.

Require Import SmallstepLinking.
Require Import Composition ThreadLinking Compiler.

Import GS.

(** 1st step : module linking *)

Lemma compose_transf_Clight_Asm_correct:
  forall client_s server_s tp spec,
  compose (Clight.semantics1 client) (Clight.semantics1 server) = Some spec ->
  transf_clight_program client = OK client_s ->
  transf_clight_program server = OK server_s ->
  link client_s server_s = Some tp ->
  forward_simulation cc_compcert spec (Asm.semantics tp).
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
  eapply M_A_semantics_preservation.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

(** 2nd step : thread linking *)
