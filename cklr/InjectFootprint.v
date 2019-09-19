Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.
Require Import Events.


(** * Injection CKLR with footprint invariants *)

(** ** Worlds *)

Inductive injp_world :=
  injpw (f: meminj) (m1 m2: mem).

(** In addition to the criteria in [ec_mem_inject], in order to ensure
  that [injp_acc] is transitive we will need the following property,
  which corresponds to [ec_max_perm]. *)

Definition injp_max_perm_decrease (f: meminj) (m1 m1': mem) :=
  forall b1 ofs1 x p,
    f b1 = Some x ->
    Mem.perm m1' b1 ofs1 Max p ->
    Mem.perm m1 b1 ofs1 Max p.

Inductive injp_acc: relation injp_world :=
  injp_acc_intro f m1 m2 f' m1' m2':
    injp_max_perm_decrease f m1 m1' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m2 ->
    injp_acc (injpw f m1 m2) (injpw f' m1' m2').

Definition injp_mi :=
  fun '(injpw f _ _) => f.

Inductive injp_match_mem: injp_world -> relation mem :=
  injp_match_mem_intro f m1 m2:
    Mem.inject f m1 m2 ->
    meminj_wf f ->
    injp_match_mem (injpw f m1 m2) m1 m2.

Hint Constructors injp_match_mem.

(** ** Properties *)

(** Proving the transitivity of the accessibility relation is somewhat
  involved because the different properties need each other. *)

Lemma mem_unchanged_on_trans_implies_valid (P Q: block -> Z -> Prop) m m' m'':
  Mem.unchanged_on P m m' ->
  Mem.unchanged_on Q m' m'' ->
  (forall b ofs, P b ofs -> Mem.valid_block m b -> Q b ofs) ->
  Mem.unchanged_on P m m''.
Proof.
  intros H HPQ H'.
  eapply (Mem.unchanged_on_implies (fun b o => P b o /\ Mem.valid_block m b)).
  - eapply Mem.unchanged_on_trans; eauto.
    + eapply Mem.unchanged_on_implies; eauto.
      tauto.
    + eapply Mem.unchanged_on_implies; eauto.
      firstorder.
  - eauto.
Qed.

Global Instance injp_acc_preo:
  PreOrder injp_acc.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. eauto.
    + apply Mem.unchanged_on_refl.
    + apply Mem.unchanged_on_refl.
    + reflexivity.
    + intros b ofs. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 f' m1' m2' Hp H1 H2 Hf Hs].
    inversion H23 as [? ? ? f'' m1'' m2'' Hp' H1' H2' Hf' Hs']; subst.
    constructor.
    + intros b1 ofs1 [b2 delta] p Hb H. eauto.
    + eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped.
      intros b1 _ Hb Hb1.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs; eauto. contradiction.
    + eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach.
      intros b2 ofs2 Hptr2 Hb2 b1 delta Hb' Hperm.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hf in Hb; split; congruence); subst.
        eapply Hptr2; eauto.
      * edestruct Hs; eauto.
    + rauto.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hf' in Hb'; split; congruence); subst.
        eapply Hs; eauto.
      * edestruct Hs'; eauto.
        intuition eauto using Mem.valid_block_unchanged_on.
Qed.

Global Instance injp_mi_acc:
  Monotonic (@injp_mi) (injp_acc ++> inject_incr).
Proof.
  unfold injp_mi. rauto.
Qed.

Lemma inject_separated_refl f m1 m2:
  inject_separated f f m1 m2.
Proof.
  red.
  congruence.
Qed.

(** ** CKLR *)

Program Definition injp: cklr :=
  {|
    world := injp_world;
    wacc := injp_acc;
    mi := injp_mi;
    match_mem := injp_match_mem;
  |}.

Next Obligation. (* meminj_wf *)
  destruct H; auto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros _ _ _ [f m1 m2 Hm Hwf] lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf' & Hb2 & Hff');
    eauto using Zle_refl.
  rewrite Hm2'.
  exists (injpw f' m1' m2'); split; repeat rstep; eauto.
  constructor.
  - intros b ofs [b' delta] p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
    eapply (Mem.valid_block_inject_1 f); eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - assumption.
  - red. intros b b' delta Hb Hb'.
    assert (b = b1).
    {
      destruct (Block.eq b b1); eauto.
      rewrite Hff' in Hb'; eauto.
      congruence.
    }
    assert (b' = b2) by congruence.
    subst.
    split; eauto using Mem.fresh_block_alloc.
  - constructor; eauto.
    split.
    + transitivity f; eauto.
      apply meminj_wf_incr; auto.
    + intros x y [d Hxy] Hy.
      destruct (Block.eq x b1); subst.
      * assert (y = b2) by congruence; subst.
        eapply Mem.alloc_result in Hm2'; subst.
        elim (Block.lt_strict Block.init).
        eapply Block.le_lt_trans; eauto.
        apply Mem.init_nextblock.
      * rewrite Hff' in Hxy by eauto.
        eapply meminj_wf_img; eauto.
Qed.

Next Obligation. (* Mem.free *)
  intros _ _ _ [f m1 m2 Hm Hwf] [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. inv H0. simpl in H1.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by xomega.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2'); split; repeat rstep; eauto.
  constructor.
  - red. eauto using Mem.perm_free_3.
  - eapply Mem.free_unchanged_on; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.free_unchanged_on; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H.
    eelim H; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.free_range_perm; eauto.
    xomega.
  - reflexivity.
  - apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.load *)
  intros _ chunk _ _ [f m1 m2 Hm Hwf] _ _ [b1 ofs1 b2 delta Hptr].
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation. (* Mem.store *)
  intros _ chunk _ _ [f m1 m2 Hm Hwf] _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  simpl in *. red.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2'); split; repeat rstep; eauto.
  constructor.
  - red. eauto using Mem.perm_store_2.
  - eapply Mem.store_unchanged_on; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.store_unchanged_on; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H.
    eelim H; eauto.
    edestruct (Mem.store_valid_access_3 chunk m1); eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply H0; eauto.
    xomega.
  - reflexivity.
  - apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros _ _ _ [f m1 m2 Hm Hwf] _ _ [b1 ofs1 b2 delta Hptr] sz.
  simpl. red.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros _ _ _ [f m1 m2 Hm Hwf] [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl. red.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. xomega.
    }
    rewrite Hm2'.
    constructor.
    exists (injpw f m1' m2'); split.
    + constructor; eauto.
      * red. eauto using Mem.perm_storebytes_2.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. xomega.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. xomega.
      * apply inject_separated_refl.
    + constructor; eauto.
      eapply Mem.storebytes_empty_inject; eauto.
  - assert (ptr_inject f (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. xomega.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. constructor.
    exists (injpw f m1' m2'); split; repeat rstep; eauto.
    constructor.
    + red. eauto using Mem.perm_storebytes_2.
    + eapply Mem.storebytes_unchanged_on; eauto.
      unfold loc_unmapped. congruence.
    + eapply Mem.storebytes_unchanged_on; eauto.
      unfold loc_out_of_reach.
      intros ofs Hofs H.
      eelim H; eauto.
      eapply Mem.perm_cur_max.
      eapply Mem.perm_implies; [ | eapply perm_any_N].
      eapply Mem.storebytes_range_perm; eauto.
      red in Hvs. rewrite Hvs.
      xomega.
    + reflexivity.
    + apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.perm *)
  intros _ _ _ [f m1 m2 Hm Hwf] _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros _ _ _ [f m1 m2 Hm Hwf] b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 Hm Hwf].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 Hm Hwf].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by xomega.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by xomega.
  assumption.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm Hwf].
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation. 
  destruct H as [f m1 m2 Hm Hwf].
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.


(** * Properties *)

Lemma injp_max_perm_decrease_dom f m m':
  injp_max_perm_decrease (meminj_dom f) m m' <->
  injp_max_perm_decrease f m m'.
Proof.
  split; repeat intro.
  - eapply H; eauto.
    unfold meminj_dom.
    destruct (f b1); try discriminate.
    reflexivity.
  - unfold meminj_dom in *.
    destruct (f b1) eqn:Hb1; try discriminate.
    eapply H; eauto.
Qed.

Lemma injp_inj_injp:
  subcklr injp (injp @ inj @ injp).
Proof.
  intros _ _ _ [f m1 m4 Hm14 Hwf].
  exists (injpw (meminj_dom f) m1 m1, (meminj_dom f, injpw f m1 m4)).
  simpl.
  repeat apply conj.
  - exists m1; split.
    { constructor. eapply mem_inject_dom; eauto. apply meminj_dom_wf; auto. }
    exists m1; split.
    { repeat rstep; eauto using mem_inject_dom, meminj_dom_wf. }
    constructor; eauto.
  - rewrite !meminj_dom_compose.
    reflexivity.
  - intros (w12' & f23 & w34') m1' m4'.
    intros (m2' & Hm12' & m3' & [Hm23' Hwf23'] & Hm34').
    intros (H12 & H23 & H34). simpl in *.
    destruct Hm12' as [f12 m1' m2' Hm12' Hwf12'].
    destruct Hm34' as [f34 m3' m4' Hm34' Hwf34'].
    inv H12.
    inv H34.
    exists (injpw (compose_meminj f12 (compose_meminj f23 f34)) m1' m4').
    repeat apply conj.
    + constructor; eauto using compose_meminj_wf.
      eauto using Mem.inject_compose.
    + constructor; eauto.
      * apply injp_max_perm_decrease_dom; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. apply loc_unmapped_dom; eauto.
      * rewrite <- (meminj_dom_compose f).
        rewrite <- (meminj_dom_compose f) at 2.
        rauto.
      * (* XXX we can't actually prove this because the intermediate
          injection may map a new block into an old one, and falsify
          the composite separation property. *)
Abort.
