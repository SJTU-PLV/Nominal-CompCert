Require Import Axioms.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Inject.


(** * [Mem.extends] as a CKLR *)

(** ** Preliminaries *)

Global Instance block_inject_sameofs_refl:
  Reflexive (block_inject_sameofs inject_id).
Proof.
  intros b.
  constructor.
Qed.

Global Instance ptr_inject_corefl:
  Coreflexive (ptr_inject inject_id).
Proof.
  intros ptr1 ptr2 Hptr.
  destruct Hptr.
  inv H. rewrite Z.add_0_r.
  reflexivity.
Qed.

Global Instance rptr_inject_corefl:
  Coreflexive (rptr_inject inject_id).
Proof.
  intros ptr1 ptr2 [Hptr|Hptr].
  - eapply coreflexivity; eauto.
  - destruct Hptr as [_ _ [b1 ofs1 b2 delta Hb]].
    inv Hb.
    rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Global Instance ptrrange_inject_corefl:
  Coreflexive (ptrrange_inject inject_id).
Proof.
  intros ptr1 ptr2 Hptr.
  destruct Hptr.
  apply coreflexivity in H. inv H.
  reflexivity.
Qed.

Global Instance block_inject_corefl:
  Coreflexive (block_inject inject_id).
Proof.
  intros b1 b2 Hb.
  destruct Hb.
  inv H.
  reflexivity.
Qed.

Lemma val_inject_lessdef_eqrel:
  eqrel (Val.inject inject_id) Val.lessdef.
Proof.
  split; intros x y; apply val_inject_lessdef.
Qed.

Global Instance flat_inject_id thr:
  Related (Mem.flat_inj thr) inject_id inject_incr.
Proof.
  intros b1 b2 delta.
  unfold Mem.flat_inj, inject_id.
  destruct plt; try discriminate.
  auto.
Qed.

(** ** Definition *)

Program Definition ext: cklr :=
  {|
    world := unit;
    wacc := ⊤;
    mi w := inject_id;
    match_mem w := Mem.extends;
    match_stbls w := eq;
  |}.

Next Obligation.
  repeat rstep. apply inject_incr_refl.
Qed.

Next Obligation.
  rauto.
Qed.

Next Obligation.
  repeat intro. subst. apply Genv.match_stbls_id.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:H1.
  edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
  rewrite Hm2'.
  exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr.
  apply coreflexivity in Hr; subst. simpl. red.
  destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
Qed.

Next Obligation.
  intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
  apply val_inject_lessdef in Hv.
  edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor. exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b ofs] p2 Hp sz.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv.
  apply coreflexivity in Hp. subst. simpl. red.
  destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
  eapply list_rel_forall2. apply Hv.
  rewrite Hm2'. constructor. exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p k H.
  apply coreflexivity in Hp. subst. simpl in *.
  eapply Mem.perm_extends; eauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm b1 b2 Hb.
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


(** * Composition theorems *)

Require Import CKLRAlgebra.

Lemma compose_meminj_id_left f:
  compose_meminj inject_id f = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
Qed.

Lemma compose_meminj_id_right f:
  compose_meminj f inject_id = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
  replace (delta + 0) with delta by xomega; eauto.
Qed.

Lemma ext_ext :
   eqcklr (ext @ ext) ext.
Proof.
  split.
  - intros [[ ] [ ]] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists tt. cbn in *. repeat apply conj.
    + congruence.
    + eauto using Mem.extends_extends_compose.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [ ] m1' m3' Hm _.
      exists (tt, tt). intuition auto.
      * exists m1'; eauto using Mem.extends_refl.
      * rauto.
  - intros [ ] se1 se2 m1 m2 Hse Hm.
    exists (tt, tt). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m1; eauto using Mem.extends_refl.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [[ ] [ ]] m1' m3' (m2' & Hm12' & Hm23') _.
      exists tt. intuition auto.
      * eauto using Mem.extends_extends_compose.
      * rauto.
Qed.

Lemma ext_inj :
  eqcklr (ext @ inj) inj.
Proof.
  split.
  - intros [[ ] f] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists f. cbn in *. repeat apply conj; eauto.
    + congruence.
    + destruct Hm23. constructor; eauto.
      * eapply Mem.extends_inject_compose; eauto.
      * erewrite Mem.mext_next; eauto.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros f' m1' m3' Hm' Hincr.
      exists (tt, f'). intuition auto; cbn.
      * exists m1'. eauto using Mem.extends_refl.
      * rauto.
      * rewrite compose_meminj_id_left. apply inject_incr_refl.
  - intros w se1 se2 m1 m2 Hse Hm.
    exists (tt, w). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m1. split; auto. apply Mem.extends_refl.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [[ ] f'] m1' m2' (mi & Hm1i & Hmi2) [_ Hf']. cbn in *.
      exists f'. intuition auto.
      * destruct Hmi2; constructor; auto.
        eapply Mem.extends_inject_compose; eauto.
        erewrite Mem.mext_next; eauto.
      * rewrite compose_meminj_id_left. apply inject_incr_refl.
Qed.

Lemma inj_ext :
  eqcklr (inj @ ext) inj.
Proof.
  split.
  - intros [f [ ]] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists f. cbn in *. repeat apply conj; eauto.
    + congruence.
    + destruct Hm12; constructor; eauto.
      eapply Mem.inject_extends_compose; eauto.
      erewrite <- Mem.mext_next; eauto.
    + rewrite compose_meminj_id_right. apply inject_incr_refl.
    + intros f' m1' m3' Hm' Hincr.
      exists (f', tt). intuition auto; cbn.
      * exists m3'. eauto using Mem.extends_refl.
      * rauto.
      * rewrite compose_meminj_id_right. apply inject_incr_refl.
  - intros w se1 se2 m1 m2 Hse Hm.
    exists (w, tt). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m2. split; auto. apply Mem.extends_refl.
    + rewrite compose_meminj_id_right. apply inject_incr_refl.
    + intros [f' [ ]] m1' m2' (mi & Hm1i & Hmi2) [Hf' _]. cbn in *.
      exists f'. intuition auto.
      * destruct Hm1i; constructor; auto.
        eapply Mem.inject_extends_compose; eauto.
        erewrite <- Mem.mext_next; eauto.
      * rewrite compose_meminj_id_right. apply inject_incr_refl.
Qed.


(** * Connection to [cc_ext] *)

Lemma cc_c_ext:
  cceqv (cc_c ext) cc_ext.
Proof.
  split.
  - red. intros [ ] se1 se2 q1 q2 Hse Hq. cbn in *.
    destruct Hq. cbn in *.
    apply val_inject_id in H. assert (vf1 = vf2) by (destruct H; congruence); subst.
    apply val_inject_list_lessdef in H0.
    exists tt. repeat apply conj; auto.
    + constructor; auto.
    + intros r1 r2 Hr. destruct Hr.
      apply val_inject_id in H3.
      exists tt. split; repeat (constructor; eauto).
  - red. intros [ ] se1 se2 q1 q2 Hse Hq. cbn in *.
    destruct Hq. cbn in *.
    apply val_inject_list_lessdef in H.
    exists tt. repeat apply conj; auto.
    + constructor; eauto. reflexivity.
    + intros r1 r2 ([ ] & _ & Hr). destruct Hr. cbn in *.
      apply val_inject_id in H2.
      eexists; eauto.
Qed.
