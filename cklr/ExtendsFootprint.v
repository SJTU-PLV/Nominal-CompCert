Require Import Axioms.
Require Import Events.
Require Import CKLR.
Require Import Inject.
Require Import InjectFootprint.
Require Import Extends.


(** * [Mem.extends] as a CKLR with footprint *)

(** ** Worlds *)

Inductive extp_world :=
  extpw (m1 m2: mem).

Definition extp_max_perm_decrease (m1 m2 m1': mem) :=
  forall b ofs p,
    Mem.valid_block m2 b ->
    Mem.perm m1' b ofs Max p ->
    Mem.perm m1 b ofs Max p.

Inductive extp_acc: relation extp_world :=
  extp_acc_intro m1 m2 m1' m2':
    extp_max_perm_decrease m1 m2 m1' ->
    Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' ->
    extp_acc (extpw m1 m2) (extpw m1' m2').

Global Instance extp_acc_preorder:
  PreOrder extp_acc.
Proof.
  split.
  - intros [m1 m2].
    constructor.
    + red; eauto.
    + eapply Mem.unchanged_on_refl.
  - intros _ _ [m1'' m2''] [m1 m2 m1' m2'] H'. inv H'.
    constructor.
    + unfold extp_max_perm_decrease in *.
      eauto using Mem.valid_block_unchanged_on.
    + eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_bounds, extp_max_perm_decrease in *; eauto.
Qed.

Inductive extp_match_mem: extp_world -> relation mem :=
  extp_match_mem_intro m1 m2:
    RIntro (Mem.extends m1 m2) (extp_match_mem (extpw m1 m2)) m1 m2.

Existing Instance extp_match_mem_intro.

(** ** Definition *)

Program Definition extp: cklr :=
  {|
    world := extp_world;
    wacc := extp_acc;
    mi w := inject_id;
    match_mem := extp_match_mem;
  |}.

Next Obligation.
  rauto.
Qed.

Next Obligation.
  apply inject_id_wf.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:H1.
  edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
  rewrite Hm2'.
  exists (extpw m1' m2'). split.
  - constructor.
    + red. intros b ofs pe Hb Hofs.
      eapply Mem.perm_alloc_4; eauto.
      intro; subst.
      eapply Mem.fresh_block_alloc in Hb; eauto.
    + eapply Mem.alloc_unchanged_on; eauto.
  - rauto.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] [[b lo] hi] r2 Hr.
  apply coreflexivity in Hr; subst. simpl. red.
  destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  exists (extpw m1' m2'). split.
  - constructor.
    + red. eauto using Mem.perm_free_3.
    + eapply Mem.free_unchanged_on; eauto.
      intros i Hi H. eapply H.
      eapply Mem.perm_cur_max.
      eapply Mem.perm_implies with (p1 := Freeable); [ | constructor].
      eapply Mem.free_range_perm; eauto.
  - constructor; eauto.
Qed.

Next Obligation.
  intros _ chunk _ _ [m1 m2 Hm] [b ofs] p2 Hp.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
Qed.

Next Obligation.
  intros _ chunk _ _ [m1 m2 Hm] [b ofs] p2 Hp v1 v2 Hv.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
  apply val_inject_lessdef in Hv.
  edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  exists (extpw m1' m2'). split.
  - constructor.
    + red. eauto using Mem.perm_store_2.
    + eapply Mem.store_unchanged_on; eauto.
      intros i Hi H. apply H. clear H.
      eapply Mem.perm_cur_max.
      eapply Mem.perm_implies with (p1 := Writable); [ | constructor].
      eapply Mem.store_valid_access_3; eauto.
  - constructor; eauto.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] [b ofs] p2 Hp sz.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] [b1 ofs1] p2 Hp vs1 vs2 Hv.
  apply coreflexivity in Hp. subst. simpl. red.
  destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  exists (extpw m1' m2'). split.
  - constructor.
    + red. eauto using Mem.perm_storebytes_2.
    + eapply Mem.storebytes_unchanged_on; eauto.
      intros i Hi H. apply H. clear H.
      eapply Mem.perm_cur_max.
      eapply Mem.perm_implies with (p1 := Writable); [ | constructor].
      eapply Mem.storebytes_range_perm; eauto.
      rewrite Hv. assumption.
  - constructor; eauto.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] [b1 ofs1] p2 Hp p k H.
  apply coreflexivity in Hp. subst. simpl in *.
  eapply Mem.perm_extends; eauto.
Qed.

Next Obligation.
  intros _ _ _ [m1 m2 Hm] b1 b2 Hb.
  apply coreflexivity in Hb. subst.
  apply Mem.valid_block_extends; eauto.
Qed.

Next Obligation.
  intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2.
  inv Hb1'. inv Hb2'. eauto.
Qed.

Next Obligation.
  xomega.
Qed.

Next Obligation.
  rewrite Z.add_0_r.
  assumption.
Qed.

Next Obligation.
  intuition xomega.
Qed.
