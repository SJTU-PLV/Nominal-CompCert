Require Import Coqlib.
Require Export LanguageInterface.
Require Export Smallstep.
Require Import CallconvAlgebra Invariant.
Require Import SmallstepLinkingSafe.

(* Refinement of invariants *)

(* [I1] is refined by [I2], meaning that any lts is safe under [I2] is
also safe under [I1] *)
Definition inv_ref {li} (I1 I2: invariant li) :=
  forall w1 se q,
    symtbl_inv I1 w1 se ->
    query_inv I1 w1 q ->
    exists w2,
      symtbl_inv I2 w2 se
      /\ query_inv I2 w2 q
      /\ forall r,
        reply_inv I2 w2 r ->
        reply_inv I1 w1 r.

Definition inveqv {li} (I1 I2: invariant li) :=
  inv_ref I1 I2 /\ inv_ref I2 I1.

Global Instance inv_ref_preo li:
  PreOrder (@inv_ref li).
Proof.
  split.
  - intros I w1 se q SINV QINV.
    eauto.
  - intros I1 I2 I3 R1 R2 w1 se q SINV QINV.
    edestruct R1 as (w2' & SINV' & QINV' & RINV'); eauto.
    edestruct R2 as (w3' & SINV'' & QINV'' & RINV''); eauto 10.
Qed.

Global Instance inveqv_equiv li:
  Equivalence (@inveqv li).
Proof.
  split.
  - intros I. split; reflexivity.
  - intros I1 I2. unfold inveqv. tauto.
  - intros I1 I2 I3 [R1 R1'] [R2 R2'].
    split; etransitivity; eauto.
Qed.

Global Instance inv_ref_po li:
  PartialOrder (@inveqv li) (@inv_ref li).
Proof.
  firstorder.
Qed.

Global Instance open_safety_inv_ref:
  Monotonic
    (@module_type_safe)
    (forallr - @ liA, forallr - @ liB, inv_ref ++>
     inv_ref --> 
     forallr - @ L, forallr - @ PS,
     impl
    ).
Proof.
  intros liA liB IA1 IA2 RA IB1 IB2 RB L PS [SAFE].
  red in RB. econstructor.
  inv SAFE.
  set (ms se wB2 s :=
         exists wB1, msafek_invariant se wB1 s
                /\ symtbl_inv IB1 wB1 se
                /\ forall r, reply_inv IB1 wB1 r ->
                       reply_inv IB2 wB2 r).  
  eapply Module_ksafe_components with (msafek_invariant := ms).
  intros se wB2 SINV2 VSE.
  econstructor.
  - intros s t s' (wB1 & INV & SINV1 & RINV) STEP.
    exists wB1. repeat apply conj; auto.
    eapply internal_step_preserves; eauto.
  - intros s (wB1 & INV & SINV1 & RINV).
    eapply internal_state_progress; eauto.
  - intros q VQ QINV2.
    edestruct RB as (wB1 & SINV1 & QINV1 & RINV); eauto.
    edestruct @initial_preserves_progress as (s & INIT & INIT1); eauto.
    exists s. split; auto.
    intros s' INIT'.
    exists wB1. repeat apply conj; auto.
  - intros s q (wB1 & INV & SINV1 & RINV) ATEXT.
    edestruct @external_preserves_progress as (wA1 & SINV1' & QINV1 & RINV1); eauto.
    edestruct RA as (wA2 & SINV2' & QINV2' & RINV'); eauto.
    exists wA2. repeat apply conj; auto.
    intros r RINV2. specialize (RINV' r RINV2).
    edestruct RINV1 as (s' & AFEXT & AFEXT'); eauto.
    exists s'. split; auto.
    intros. exists wB1.
    repeat apply conj; auto.
  - intros s r (wB1 & SINV1 & QINV1 & RINV) FINAL.
    eapply RINV. eapply final_state_preserves; eauto.
Qed.

Lemma test_rewrite_inv_ref_fail {liA liB} : forall (IA: invariant liA) (IB1 IB2: invariant liB) L PS,
    inv_ref IB2 IB1 ->
    module_type_safe IA IB1 L PS ->
    module_type_safe IA IB2 L PS.
Proof.
  intros.
  (* why we cannot rewrite H? *)
  (* rewrite H. *)
  eapply open_safety_inv_ref. reflexivity. eauto. auto.
Qed.



