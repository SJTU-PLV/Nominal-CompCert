Require Import Coqlib Errors.

Require Import AST Linking Smallstep.
Require Import Compiler.

Require Import CallconvAlgebra.

Require Import Client.
Require Import Server Serverspec Serverproof.

Require Import Linking SmallstepLinking.

(** part1 *)

(*
client ⊕ L1 ≤ client_asm ⊕ b1
client ⊕ L2 ≤ client_asm ⊕ b2
 *)

(* Compute compose (Clight.semantics1 client) L1. 
Can terminate ~10min in at laptop
*)

Compute transf_clight_program client.
Require Import Ctypes Ctypesdefs Cshmgen.

Compute signature_of_type (Tcons tint (Tcons (Tpointer (Tfunction (Tcons tint Tnil) Tvoid cc_default) noattr)  Tnil)) tint cc_default.
           
Lemma transf_client :
  transf_clight_program client = Error
         (MSG "In function "
            :: CTX 1 :: MSG ": " :: MSG "Cshmgen.transl_fundef: wrong external signature" :: nil).
Proof.
  unfold client.
  unfold transf_clight_program.
  simpl. cbn.
  unfold Cshmgen.transl_program.
  cbn.
  reflexivity.
*)
Lemma compose_Client_Server_correct1:
  forall client_asm tp spec,
  compose (Clight.semantics1 client) L1 = Some spec ->
  transf_clight_program client = OK client_asm ->
  link client_asm b1 = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel. 2: discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply semantics_preservation_L1.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

Lemma compose_Client_Server_correct2:
  forall client_asm tp spec,
  compose (Clight.semantics1 client) L2 = Some spec ->
  transf_clight_program client = OK client_asm ->
  link client_asm b2 = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel. 2: discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply semantics_preservation_L2.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.


