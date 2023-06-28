Require Import Coqlib Errors.

Require Import AST Linking Smallstep.
Require Import Compiler.

Require Import CallconvAlgebra InjectFootprint CKLRAlgebra CA CallConv.
Require Import Invariant ValueAnalysis.

Require Import Client.
Require Import Server Serverspec Serverproof ClientServerCspec ClientServerCspec2.
Require Import Linking SmallstepLinking.

(** part1 *)

(*
client ⊕ L1 ≤ client_asm ⊕ b1
client ⊕ L2 ≤ client_asm ⊕ b2
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

(* Top level theorem for Non-MutRec Client and Server *)

Section SPEC.

Variable client_asm tp1 tp2 : Asm.program.
Axiom compile: transf_clight_program client = OK client_asm.
Axiom link1 : link client_asm b1 = Some tp1.
Axiom link2 : link client_asm b2 = Some tp2.

Lemma ro_injp_cc_compcert:
  cceqv cc_compcert (wt_c @ ro @ cc_c injp @ cc_compcert).
Proof.
  split; unfold cc_compcert.
  - (*incoming side*)
  etransitivity.
  rewrite (inv_dup wt_c), cc_compose_assoc.
  rewrite cc_cainjp__injp_ca, cc_compose_assoc.
  rewrite <- lessdef_c_cklr,cc_compose_assoc.
  (* rewrite injp_injp at 1. rewrite cc_c_compose, cc_compose_assoc. *)
  rewrite <- (cc_compose_assoc ro).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (commute_around (_@_) (R2 := injp)).
  rewrite inv_commute_ref.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc ro).
  rewrite trans_injp_inv_incoming, ! cc_compose_assoc.
  reflexivity.
  repeat (rstep; [rauto | ]).  
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc injp).
  rewrite wt_c_R_refinement, !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
  repeat (rstep; [rauto|]).
  rewrite <- (cc_compose_assoc injp).
  rewrite cc_injpca_cainjp. reflexivity.
  - (*outgoing side*)
    etransitivity.
    rewrite cc_cainjp__injp_ca, cc_compose_assoc.
    rewrite injp_injp at 2. rewrite cc_c_compose, cc_compose_assoc.
    rewrite <- lessdef_c_cklr at 2. rewrite cc_compose_assoc.
    rewrite <- ! (cc_compose_assoc wt_c).
    rewrite (commute_around (wt_c@ lessdef_c) (R2:=injp)), !cc_compose_assoc.
    rewrite <- !(cc_compose_assoc ro).
    rewrite <- (cc_compose_assoc (ro @ injp)).
    rewrite trans_injp_ro_outgoing, cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c), inv_commute_ref, cc_compose_assoc.
    rewrite <- (cc_compose_assoc injp).
    rewrite <- (cc_compose_assoc wt_c).
    rewrite (inv_drop _ wt_c), cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c).
    reflexivity.
    rstep; [rauto |].
    rewrite <- (cc_compose_assoc injp).
    rewrite wt_c_R_refinement, !cc_compose_assoc.
    rstep; [rauto|].
    rewrite <- (cc_compose_assoc). rewrite lessdef_c_cklr.
    rewrite <- cc_compose_assoc. rewrite <- cc_c_compose.
    rewrite injp_injp2.
    rewrite <- (cc_compose_assoc injp).
  rewrite cc_injpca_cainjp. reflexivity.
Qed.
  
Theorem spec_sim_1 : forward_simulation cc_compcert cc_compcert top_spec1 (Asm.semantics tp1).
Proof.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply top1_wt.
  eapply compose_forward_simulations.
  eapply top1_ro.
  eapply compose_forward_simulations.
  eapply top_simulation_L1.
  eapply compose_Client_Server_correct1; eauto.
  eapply compile.
  eapply link1.
Qed.

(*To be moved to ClightServerCspec2.v *)

Theorem spec_sim_2 : forward_simulation cc_compcert cc_compcert top_spec2 (Asm.semantics tp2).
Proof.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply top2_wt.
  eapply compose_forward_simulations.
  eapply top2_ro.
  eapply compose_forward_simulations.
  eapply top_simulation_L2.
  eapply compose_Client_Server_correct2; eauto.
  eapply compile.
  eapply link2.
Qed.

End SPEC.

Require Import ClientMR ClientServerMRCSpec.

Definition N := 10%Z.

Lemma compose_ClientMR_Server_correct1:
  forall client_asm tp spec,
  compose (Clight.semantics1 (client N)) L1 = Some spec ->
  transf_clight_program (client N) = OK client_asm ->
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

(* Top level theorem for MutRec Client and Server *)


Section SPEC_MR.

Variable client_asm tp1 tp2 : Asm.program.

Axiom compile_mr : transf_clight_program (client N) = OK client_asm.
Axiom link2_mr : link client_asm b1 = Some tp1.

Theorem spec_sim_mr : forward_simulation cc_compcert cc_compcert (top_spec1 N) (Asm.semantics tp1).
Proof.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply top1_wt.
  eapply compose_forward_simulations.
  eapply top1_ro.
  eapply compose_forward_simulations.
  eapply top_simulation_L1.
  unfold Int.max_signed. unfold N. cbn. lia.
  eapply compose_ClientMR_Server_correct1; eauto.
  eapply compile_mr.
  eapply link2_mr.
Qed.

End SPEC_MR.
