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

(* Compute transf_clight_program client. 
Coq process killed
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



Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Section SPEC.

(*items need to define and prove *)
Variable spec1 : Smallstep.semantics li_c li_c.
Variable compose_spec1 : Smallstep.semantics li_c li_c.

Axiom compose : compose (Clight.semantics1 client) L1 = Some compose_spec1.
Axiom top_sim: forward_simulation (cc_c injp) (cc_c injp) spec1 compose_spec1.
Axiom top_ro : forward_simulation ro ro spec1 spec1.
Axiom top_wt : forward_simulation wt_c wt_c spec1 spec1.

Variable client_asm tp : Asm.program.
Axiom compile: transf_clight_program client = OK client_asm.
Axiom link : link client_asm b1 = Some tp.

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
  
Theorem spec_sim_1 : forward_simulation cc_compcert cc_compcert spec1 (Asm.semantics tp).
Proof.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply top_wt.
  eapply compose_forward_simulations.
  eapply top_ro.
  eapply compose_forward_simulations.
  eapply top_sim.
  eapply compose_Client_Server_correct1; eauto.
  eapply compose.
  eapply compile.
  eapply link.
Qed.  

End SPEC.
