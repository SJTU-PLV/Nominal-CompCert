Require Import Axioms.
Require Export CKLR.

(** Algebraic structures on CKLRs *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the CKLR [R] is refined by the
  CKLR [R'], meaning that any [R']-simulation is also a [R]-simulation. *)

Definition subcklr (Q R: cklr) :=
  forall wq m1 m2,
    match_mem Q wq m1 m2 ->
    exists wr,
      match_mem R wr m1 m2 /\
      inject_incr (mi Q wq) (mi R wr) /\
      forall wr' m1' m2',
        match_mem R wr' m1' m2' ->
        wr ~> wr' ->
        exists wq',
          match_mem Q wq' m1' m2' /\
          wq ~> wq' /\
          inject_incr (mi R wr') (mi Q wq').

Definition eqcklr R1 R2 :=
  subcklr R1 R2 /\ subcklr R2 R1.

Global Instance subcklr_preo:
  PreOrder subcklr.
Proof.
  split.
  - intros R w q1 q2 Hq.
    exists w; intuition eauto.
  - intros R1 R2 R3 H12 H23 w1 ma mb Hm1.
    destruct (H12 w1 ma mb Hm1) as (w2 & Hm2 & Hincr12 & H21); clear H12.
    destruct (H23 w2 ma mb Hm2) as (w3 & Hm3 & Hincr23 & H32); clear H23.
    exists w3. repeat apply conj; eauto using inject_incr_trans.
    intros w3' ma' mb' Hm3' Hw3'.
    destruct (H32 w3' ma' mb' Hm3' Hw3') as (w2' & Hm2' & Hw2' & Hincr32).
    destruct (H21 w2' ma' mb' Hm2' Hw2') as (w1' & Hm1' & Hw1' & Hincr21).
    exists w1'; intuition eauto using inject_incr_trans.
Qed.

Global Instance eqcklr_equiv:
  Equivalence eqcklr.
Proof.
  split.
  - intros R.
    split; reflexivity.
  - intros R1 R2. unfold eqcklr.
    tauto.
  - intros R1 R2 R3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance subcklr_po:
  PartialOrder eqcklr subcklr.
Proof.
  unfold eqcklr. red. generalize subcklr.
  firstorder.
Qed.


(** * Composition *)

(** ** Preliminaries *)

Lemma option_le_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (option_le (rel_compose R1 R2))
    (rel_compose (option_le R1) (option_le R2)).
Proof.
  split.
  - intros _ _ [x z (y & Hxy & Hyz) | z];
    eexists; split; constructor; eauto.
  - intros x z (y & Hxy & Hyz).
    destruct Hxy; [inversion Hyz; clear Hyz; subst | ];
    constructor; eexists; split; eauto.
Qed.

Lemma list_rel_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (list_rel (rel_compose R1 R2))
    (rel_compose (list_rel R1) (list_rel R2)).
Proof.
  split.
  - induction 1.
    + exists nil; split; constructor.
    + destruct H as (z & ? & ?).
      destruct IHlist_rel as (z0 & ? & ?).
      exists (z::z0); split; constructor; eauto.
  - intros la lc (lb & H1 & H2).
    revert lc H2.
    induction H1; intros lc H2; inv H2.
    + constructor.
    + constructor; eauto.
Qed.

Global Instance compose_meminj_incr:
  Monotonic compose_meminj (inject_incr ++> inject_incr ++> inject_incr).
Proof.
  intros f1 f2 Hf g1 g2 Hg b xb xdelta.
  unfold compose_meminj.
  destruct (f1 b) as [[b' delta] | ] eqn:Hb'; try discriminate.
  erewrite Hf by eauto.
  destruct (g1 b') as [[b'' delta'] | ] eqn:Hb''; try discriminate.
  erewrite Hg by eauto.
  tauto.
Qed.

Lemma val_inject_compose f g:
  eqrel
    (Val.inject (compose_meminj f g))
    (rel_compose (Val.inject f) (Val.inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try (eexists; split; constructor).
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    exists (Vptr bi (Ptrofs.add ofs1 (Ptrofs.repr di))).
    split; econstructor; eauto.
    rewrite add_repr, Ptrofs.add_assoc.
    reflexivity.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; econstructor.
    unfold compose_meminj.
    + rewrite H, H3.
      reflexivity.
    + rewrite add_repr, Ptrofs.add_assoc.
      reflexivity.
Qed.

Lemma memval_inject_compose f g:
  eqrel
    (memval_inject (compose_meminj f g))
    (rel_compose (memval_inject f) (memval_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try solve [eexists; split; constructor].
    apply val_inject_compose in H.
    destruct H as (vi & Hv1i & Hvi2).
    eexists; split; constructor; eauto.
  - intros v1 v3 Hv.
    destruct Hv as (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; constructor.
    apply val_inject_compose.
    eexists; split; eauto.
Qed.

Lemma ptr_inject_compose f g:
  eqrel
    (ptr_inject (compose_meminj f g))
    (rel_compose (ptr_inject f) (ptr_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv.
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    rewrite Z.add_assoc.
    exists (bi, ofs1 + di); split; econstructor; eauto.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23.
    rewrite <- Z.add_assoc.
    constructor.
    unfold compose_meminj.
    rewrite H, H3.
    reflexivity.
Qed.

Lemma ptrbits_inject_compose f g:
  eqrel
    (ptrbits_inject (compose_meminj f g))
    (rel_compose (ptrbits_inject f) (ptrbits_inject g)).
Proof.
  split.
  - destruct 1.
    unfold compose_meminj in H.
    destruct (f b1) as [[bI delta1I] | ] eqn:H1I; [ | discriminate].
    exists (bI, Ptrofs.add ofs1 (Ptrofs.repr delta1I)); split; eauto.
    destruct (g bI) as [[xb2 deltaI2] | ] eqn:HI2; [ | discriminate].
    inv H.
    rewrite add_repr.
    rewrite <- Ptrofs.add_assoc.
    constructor; eauto.
  - intros p1 p3 (p2 & H12 & H23).
    destruct H12 as [b1 ofs1 b2 delta12].
    inv H23.
    rewrite Ptrofs.add_assoc.
    rewrite <- add_repr.
    constructor.
    unfold compose_meminj. rewrite H, H3.
    reflexivity.
Qed.

Lemma rptr_inject_compose f g:
  subrel
    (rptr_inject (compose_meminj f g))
    (rel_compose (rptr_inject f) (rptr_inject g)).
Proof.
  unfold rptr_inject.
  intros p1 p3 Hp.
  rewrite ptr_inject_compose in Hp.
  rewrite ptrbits_inject_compose in Hp.
  destruct Hp as [(p2 & H12 & H23) | [q1 q3 (q2 & H12 & H23)]].
  - exists p2; split; rauto.
  - exists (ptrbits_unsigned q2); split; rauto.
Qed.

Lemma ptrrange_inject_compose f g:
  eqrel
    (ptrrange_inject (compose_meminj f g))
    (rel_compose (ptrrange_inject f) (ptrrange_inject g)).
Proof.
  split.
  - destruct 1.
    apply ptr_inject_compose in H.
    destruct H as ([bi ofsi] & H1 & H2).
    exists (bi, ofsi, ofsi + sz).
    split; constructor; eauto.
  - intros r1 r3 (r2 & H12 & H23).
    destruct H12; inv H23.
    assert (sz0 = sz) by omega; subst.
    constructor.
    apply ptr_inject_compose.
    eexists; split; eauto.
Qed.

Lemma block_inject_compose f g:
  eqrel
    (block_inject (compose_meminj f g))
    (rel_compose (block_inject f) (block_inject g)).
Proof.
  split.
  - intros b1 b3 [d13 H13].
    unfold compose_meminj in H13.
    destruct (f b1) as [[b2 d12] | ] eqn:H12; [ | discriminate].
    destruct (g b2) as [[xb3 d23] | ] eqn:H23; [ | discriminate].
    inv H13.
    exists b2; eexists; eauto.
  - intros b1 b3 (b2 & [d2 H12] & [d3 H23]).
    exists (d2 + d3).
    unfold compose_meminj.
    rewrite H12, H23.
    reflexivity.
Qed.

Lemma block_inject_sameofs_compose f g:
  subrel
    (rel_compose (block_inject_sameofs f) (block_inject_sameofs g))
    (block_inject_sameofs (compose_meminj f g)).
Proof.
  intros b1 b3 (b2 & H12 & H23).
  red in H12, H23 |- *.
  unfold compose_meminj. rewrite H12, H23.
  reflexivity.
Qed.

Lemma flat_inj_idemp thr:
  compose_meminj (Mem.flat_inj thr) (Mem.flat_inj thr) = Mem.flat_inj thr.
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj, Mem.flat_inj.
  destruct Block.lt_dec eqn:Hb; eauto.
  rewrite Hb.
  reflexivity.
Qed.

Lemma compose_meminj_wf f1 f2:
  meminj_wf f1 ->
  meminj_wf f2 ->
  meminj_wf (compose_meminj f1 f2).
Proof.
  intros [Hf1 Hi1] [Hf2 Hi2].
  split.
  - rewrite <- flat_inj_idemp.
    rauto.
  - intros b1 b2 Hb Hb2.
    apply block_inject_compose in Hb as (bI & Hb1I & HbI2).
    eauto using meminj_wf_img.
Qed.

(** ** Definition *)

Program Definition cklr_compose (R1 R2: cklr): cklr :=
  {|
    world := world R1 * world R2;
    wacc := wacc R1 * wacc R2;
    mi w := compose_meminj (mi R1 (fst w)) (mi R2 (snd w));
    match_mem w := rel_compose (match_mem R1 (fst w)) (match_mem R2 (snd w));
  |}.

Next Obligation.
  rauto.
Qed.

Next Obligation.
  destruct H as (mI & Hm1I & HmI2); simpl in *.
  apply compose_meminj_wf; eapply cklr_wf; eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) lo hi.
  edestruct (cklr_alloc R1 w12 m1 m2 Hm12 lo hi)
    as (w12' & Hw12' & Hm12' & Hb12).
  edestruct (cklr_alloc R2 w23 m2 m3 Hm23 lo hi)
    as (w23' & Hw23' & Hm23' & Hb23).
  exists (w12', w23'); split; [rauto | ].
  rstep. simpl. split.
  - eexists; split; rauto.
  - red. apply block_inject_sameofs_compose.
    eexists; split; eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [[b1 lo1] hi1] [[b3 lo3] hi3] H.
  apply ptrrange_inject_compose in H.
  destruct H as ([[b2 lo2] hi2] & Hr12 & Hr23).
  simpl in *. red.
  destruct (Mem.free m1 _ _ _) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23').
  split; [rauto | ].
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  red. simpl in *. unfold klr_pullw.
  rewrite val_inject_compose.
  apply option_le_compose.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  simpl in *. red. unfold klr_pullw in *.
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  apply val_inject_compose in Hv. destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.store chunk m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr sz.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  unfold k1, klr_pullw. simpl in *.
  eapply option_le_subrel. (* XXX coqrel *)
  {
    apply list_subrel.
    apply memval_inject_compose.
  }
  rewrite list_rel_compose.
  apply option_le_compose.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  unfold k1, klr_pullw in *. simpl in *.
  apply rptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  rewrite memval_inject_compose in Hv. apply list_rel_compose in Hv.
  destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.storebytes m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm [b1 o1] [b3 o3] Hptr pk pe.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  etransitivity; rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm b1 b3 Hb.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply block_inject_compose in Hb. destruct Hb as (b2 & Hb12 & Hb23).
  etransitivity; rauto.
Qed.

Next Obligation. (* no overlap *)
  intros a1 a2 da b1 b2 db oa ob Hab1 Ha Hb Hoa Hob. simpl in *.
  destruct H as (mx & Hm1x & Hmx2).
  unfold compose_meminj in *.
  destruct (mi R1 w a1) as [[ax da1x] | ] eqn:Ha1x; [ | discriminate].
  destruct (mi R2 w0 ax) as [[ay dax2] | ] eqn:Hax2; [ | discriminate].
  inv Ha.
  destruct (mi R1 w b1) as [[bx db1x] | ] eqn:Hb1x; [ | discriminate].
  destruct (mi R2 w0 bx) as [[bz dbz2] | ] eqn:Hbx2; [ | discriminate].
  inv Hb.
  assert (Mem.perm mx ax (oa + da1x) Max Nonempty).
  { revert Hoa. repeat rstep. left. constructor; eauto. }
  assert (Mem.perm mx bx (ob + db1x) Max Nonempty).
  { revert Hob. repeat rstep. left. constructor; eauto. }
  edestruct (cklr_no_overlap R1 w m1 mx); eauto.
  - edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
    rewrite !Z.add_assoc.
    eauto.
  - destruct (Block.eq ax bx); eauto.
    + right. assert (dax2 = dbz2) by congruence. xomega.
    + edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
      rewrite !Z.add_assoc.
      eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H1. simpl in H1.
  destruct (mi R1 w b1) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H1.
  simpl in *.
  assert (d1I >= 0 /\ 0 <= ofs1 + d1I <= Ptrofs.max_unsigned) as [? ?].
  { eapply (cklr_representable R1); eauto. }
  assert (dI2 >= 0 /\ 0 <= (ofs1 + d1I) + dI2 <= Ptrofs.max_unsigned).
  { eapply (cklr_representable R2); eauto.
    revert H0. repeat rstep.
    - left.
      constructor; eauto.
    - left.
      replace (ofs1 + d1I -1) with (ofs1 - 1 + d1I) by xomega.
      constructor; eauto. }
  xomega.
Qed.

Next Obligation. (* aligned_area_inject *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H5. simpl in H5.
  destruct (mi R1 w b) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H5.
  simpl in *.
  rewrite Z.add_assoc.
  eapply (cklr_aligned_area_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b (x - d1I) Cur Nonempty). { eapply H3. xomega. }
    revert H. repeat rstep. left.
    replace x with (x - d1I + d1I) at 2 by xomega.
    constructor; eauto.
  - eapply (cklr_aligned_area_inject R1); eauto.
Qed.

Next Obligation. (* disjoint_or_equal_inject *)
  simpl in *.
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in *.
  destruct (mi R1 w b1) as [[b1I d1] | ] eqn:Hb1I; [ | discriminate].
  destruct (mi R2 w0 b1I) as [[xb1' d1'] | ] eqn:Hb1'; [ | discriminate].
  inv H0.
  destruct (mi R1 w b2) as [[b2I d2] | ] eqn:Hb2I; [ | discriminate].
  destruct (mi R2 w0 b2I) as [[xb2' d2'] | ] eqn:Hb2'; [ | discriminate].
  inv H1.
  rewrite !Z.add_assoc.
  eapply (cklr_disjoint_or_equal_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b1 (x - d1) Max Nonempty). { eapply H2. xomega. }
    revert H. repeat rstep. left.
    replace x with (x - d1 + d1) at 2 by xomega.
    constructor; eauto.
  - intros x Hx.
    assert (Mem.perm m b2 (x - d2) Max Nonempty). { eapply H3. xomega. }
    revert H. repeat rstep. left.
    replace x with (x - d2 + d2) at 2 by xomega.
    constructor; eauto.
  - eapply (cklr_disjoint_or_equal_inject R1); eauto.
Qed.

Bind Scope cklr_scope with cklr.
Delimit Scope cklr_scope with cklr.
Infix "@" := cklr_compose (at level 30, right associativity) : cklr_scope.

(** ** Properties *)

(** Monotonicity *)

Global Instance cklr_compose_subcklr:
  Proper (subcklr ++> subcklr ++> subcklr) (@cklr_compose).
Proof.
  intros R12 R12' H12 R23 R23' H23.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23). simpl in *.
  specialize (H12 w12 m1 m2 Hm12) as (w12' & Hm12' & Hincr12 & H12).
  specialize (H23 w23 m2 m3 Hm23) as (w23' & Hm23' & Hincr23 & H23).
  exists (w12', w23'); simpl.
  repeat apply conj; try rauto.
  - eexists; split; eauto.
  - intros [v12' v23'] m1' m3' (m2' & Hm'12 & Hm'23) [Hwv12 Hwv23].
    specialize (H12 v12' m1' m2' Hm'12 Hwv12) as (v12 & Hm'12' & Hwv12' & Hi12').
    specialize (H23 v23' m2' m3' Hm'23 Hwv23) as (v23 & Hm'23' & Hwv23' & Hi23').
    simpl in *.
    exists (v12, v23).
    split; [ | split].
    + eexists; split; eauto.
    + rauto.
    + rauto.
Qed.

(** Associativity *)

Require Import Axioms.

Lemma compose_meminj_assoc f g h:
  compose_meminj (compose_meminj f g) h =
  compose_meminj f (compose_meminj g h).
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj.
  destruct (f b) as [[b' d] | ]; eauto.
  destruct (g b') as [[b'' d'] | ]; eauto.
  destruct (h b'') as [[b''' d''] | ]; eauto.
  rewrite Z.add_assoc; eauto.
Qed.

Lemma cklr_compose_assoc R1 R2 R3:
  subcklr ((R1 @ R2) @ R3) (R1 @ (R2 @ R3)).
Proof.
  intros [[w1 w2] w3] ma md (mb & (mc & Hm1 & Hm2) & Hm3).
  simpl in *.
  exists (w1, (w2, w3)).
  repeat apply conj.
  - repeat (eexists; eauto).
  - rewrite compose_meminj_assoc. apply inject_incr_refl.
  - intros (w1' & w2' & w3') ma' md' (mb' & Hm1' & (mc' & Hm2' & Hm3')).
    intros (Hw1 & Hw2 & Hw3).
    simpl in *.
    exists ((w1', w2'), w3').
    split; [ | split].
    + repeat (econstructor; eauto).
    + rauto.
    + rewrite compose_meminj_assoc. apply inject_incr_refl.
Qed.
