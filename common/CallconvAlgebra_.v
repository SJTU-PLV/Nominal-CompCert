Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface_.
Require Export Smallstep_.

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.

Definition ccref {li1 li2} (cc cc': callconv li1 li2) :=
  forall w se1 se2 q1 q2,
    match_senv cc w se1 se2 ->
    match_query cc w q1 q2 ->
    exists w',
      match_senv cc' w' se1 se2 /\
      match_query cc' w' q1 q2 /\
      forall r1 r2,
        match_reply cc' w' r1 r2 ->
        match_reply cc w r1 r2.

Definition cceqv {li1 li2} (cc cc': callconv li1 li2) :=
  ccref cc cc' /\ ccref cc' cc.

Global Instance ccref_preo li1 li2:
  PreOrder (@ccref li1 li2).
Proof.
  split.
  - intros cc w q1 q2 Hq.
    eauto.
  - intros cc cc' cc'' H' H'' w se1 se2 q1 q2 Hse Hq.
    edestruct H' as (w' & Hse' & Hq' & Hr'); eauto.
    edestruct H'' as (w'' & Hse'' & Hq'' & Hr''); eauto 10.
Qed.

Global Instance cceqv_equiv li1 li2:
  Equivalence (@cceqv li1 li2).
Proof.
  split.
  - intros cc.
    split; reflexivity.
  - intros cc1 cc2. unfold cceqv.
    tauto.
  - intros cc1 cc2 cc3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance ccref_po li1 li2:
  PartialOrder (@cceqv li1 li2) (@ccref li1 li2).
Proof.
  firstorder.
Qed.

(** ** Relation to forward simulations *)

Global Instance open_fsim_ccref:
  Monotonic
    (@forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, ccref ++>
     forallr - @ liB1, forallr - @ liB2, ccref -->
     subrel).
Proof.
  intros liA1 liA2 ccA ccA' HA liB1 liB2 ccB ccB' HB sem1 sem2 [FS].
  destruct FS as [index order match_states SKEL FP PROP WF].
  constructor.
  set (ms se1 se2 w' idx s1 s2 :=
         exists w : ccworld ccB,
           match_states se1 se2 w idx s1 s2 /\
           match_senv ccB w se1 se2 /\
           forall r1 r2, match_reply ccB w r1 r2 -> match_reply ccB' w' r1 r2).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  (* - intros q1 q2 Hq'. *)
  (*   destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto. *)
  (*   eapply fsim_match_valid_query; eauto. *)
  - intros q1 q2 s1 Hq' Hs1.
    destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. exists wB; auto.
  - intros i s1 s2 r1 (wB & Hs & Hse & Hr') Hr1.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
  - intros i s1 s2 qA1 (wB & Hs & Hse & Hr') HqA1.
    edestruct @fsim_match_external as (wA & qA2 & HqA2 & HqA & HseA & ?); eauto.
    edestruct HA as (wA' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB; eauto.
  - intros s1 t s1' Hs1' i s2 (wB & Hs & Hse & Hr').
    edestruct @fsim_simulation as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB; eauto.
Qed.

(** * Properties of [cc_compose] *)

(** Language interfaces and calling conventions form a category, with
  [cc_id] as the identity arrow and [cc_compose] as the composition. *)

Lemma cc_compose_id_left {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc_id cc) cc.
Proof.
  split.
  - intros [[se2 [ ]] w] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    simpl in *. subst.
    exists w; intuition eauto.
  - intros w se1 se2 q1 q2 Hse Hq.
    exists (se1, tt, w); repeat apply conj.
    + cbn. eauto.
    + cbn. eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_id_right {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc cc_id) cc.
Proof.
  split.
  - intros [[se2 w] [ ]] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    simpl in *. subst.
    exists w; intuition eauto.
  - intros w se1 se2 q1 q2 Hse Hq.
    exists (se2, w, tt); repeat apply conj.
    + cbn. eauto.
    + cbn. eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_assoc {A B C D} cc1 cc2 cc3:
  cceqv
    (@cc_compose A C D (cc_compose cc1 cc2) cc3)
    (@cc_compose A B D cc1 (cc_compose cc2 cc3)).
Proof.
  split.
  - intros [[sec [[seb w1] w2]] w3] sea sed qa qd.
    intros ((Hseab & Hsebc) & Hsecd) (qc & (qb & Hqab & Hqbc) & Hqcd).
    exists (seb, w1, (sec, w2, w3)). simpl in *.
    repeat apply conj; eauto.
    intros ra rd (rb & Hrab & rc & Hrbc & Hrcd); eauto.
  - intros [[seb w1] [[sec w2] w3]] sea sed qa qd.
    intros (Hseab & Hsebc & Hsecd) (qb & Hqab & qc & Hqbc & Hqcd).
    exists (sec, (seb, w1, w2), w3). simpl in *.
    repeat apply conj; eauto.
    intros ra rd (rc & (rb & Hrab & Hrbc) & Hrcd); eauto.
Qed.

(** In addition, composition is monotonic under [cc_ref]. *)

Global Instance cc_compose_ref li1 li2 li3:
  Proper (ccref ++> ccref ++> ccref) (@cc_compose li1 li2 li3).
Proof.
  intros cc12 cc12' H12 cc23 cc23' H23 [[se2 w12] w23] se1 se3 q1 q3.
  intros (Hse12 & Hse23) (q2 & Hq12 & Hq23).
  simpl in *.
  edestruct (H12 w12 se1 se2 q1 q2 Hse12 Hq12) as (w12' & Hse12' & Hq12' & H12').
  edestruct (H23 w23 se2 se3 q2 q3 Hse23 Hq23) as (w23' & Hse23' & Hq23' & H23').
  exists (se2, w12', w23').
  repeat apply conj; eauto.
  intros r1 r3 (r2 & Hr12 & Hr23); eauto.
Qed.

Global Instance cc_compose_eqv li1 li2 li3:
  Proper (cceqv ==> cceqv ==> cceqv) (@cc_compose li1 li2 li3) | 10.
Proof.
  intros cc12 cc12' [H12 H21] cc23 cc23' [H23 H32].
  split; eapply cc_compose_ref; eauto.
Qed.

Global Instance cc_compose_ref_params:
  Params (@cc_compose) 2.


(* Some handy typeclasses and notations *)

Global Instance fsim_transitive {li1 li2: language_interface}:
  Transitive (forward_simulation (@cc_id li1) (@cc_id li2)).
Proof.
  intros L1 L2 L3 HL1 HL2.
  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations; eauto.
Qed.

Notation "L1 ≤ L2" :=  (forward_simulation 1 1 L1 L2)(at level 70): lts_scope.
Open Scope lts_scope.
Delimit Scope lts_scope with lts.

Definition equiv_simulation {liA liB} (L1 L2: semantics liA liB) :=
  L1 ≤ L2 /\ L2 ≤ L1.

Global Instance fsim_equivalence {li1 li2: language_interface}:
  Equivalence (@equiv_simulation li1 li2).
Proof.
  split.
  - intros L; split; apply identity_forward_simulation.
  - intros L1 L2 [H1 H2]. split; auto.
  - intros L1 L2 L3 [? ?] [? ?]. split; etransitivity; eauto.
Qed.

Notation "L1 ≡ L2" :=  (equiv_simulation L1 L2)(at level 90): lts_scope.
