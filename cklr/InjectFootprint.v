Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.


(** * Injection CKLR with footprint invariants *)

(** ** Worlds *)

Inductive injp_world :=
  injpw (f: meminj) (m1 m2: mem) (Hm: Mem.inject f m1 m2).

(** In addition to the criteria in [ec_mem_inject], in order to ensure
  that [injp_acc] is transitive we will need the following property,
  which corresponds to [ec_max_perm]. *)

Definition injp_max_perm_decrease (m m': mem) :=
  forall b ofs p,
    Mem.valid_block m b ->
    Mem.perm m' b ofs Max p ->
    Mem.perm m b ofs Max p.

Inductive injp_acc: relation injp_world :=
  injp_acc_intro f m1 m2 Hm f' m1' m2' Hm':
    injp_max_perm_decrease m1 m1' ->
    injp_max_perm_decrease m2 m2' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m2 ->
    injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Definition injp_mi :=
  fun '(injpw f _ _ _) => f.

Inductive injp_match_mem: injp_world -> relation mem :=
  injp_match_mem_intro f m1 m2 Hm:
    injp_match_mem (injpw f m1 m2 Hm) m1 m2.

Inductive injp_match_stbls: injp_world -> relation Genv.symtbl :=
  injp_match_stbls_intro f m1 m2 Hm se1 se2:
    Genv.match_stbls f se1 se2 ->
    Mem.sup_include (Genv.genv_sup se1) (Mem.support m1) ->
    Mem.sup_include (Genv.genv_sup se2) (Mem.support m2) ->
    injp_match_stbls (injpw f m1 m2 Hm) se1 se2.

Hint Constructors injp_match_mem injp_match_stbls.

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
    + red. eauto.
    + apply Mem.unchanged_on_refl.
    + apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hp1 Hp2 H1 H2 Hf Hs].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hp1' Hp2' H1' H2' Hf' Hs']; subst.
    constructor.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
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
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs; eauto.
    + eapply inject_incr_trans; eauto.
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
    match_stbls := injp_match_stbls;
  |}.

(** Acc separated *)
Next Obligation.
  rename m1 into M1. rename m2 into M2.
  inv H0.
  unfold inject_separated in *.
  intros b1 b2 delta Hw Hw'.
  destruct (H6 _ _ _ Hw Hw') as [Hm1 Hm2].
  inv H.
  tauto.
Qed.

Next Obligation. (* ~> vs. match_stbls *)
  intros w w' Hw' se1 se2 Hse.
  destruct Hse as [f m1 m2 se1 se2 Hse Hnb1 Hnb2]. inv Hw'.
  constructor.
  - eapply Genv.match_stbls_incr; eauto.
    intros b1 b2 delta Hb Hb'. specialize (H9 b1 b2 delta Hb Hb').
    unfold Mem.valid_block in H9. split; inv H9; eauto.
  - apply Mem.unchanged_on_support in H5. eauto.
  - apply Mem.unchanged_on_support in H6. eauto.
Qed.

Next Obligation. (* match_stbls vs. Genv.match_stbls *)
  destruct 1; auto.
Qed.

Next Obligation.
  destruct H. inv H0. auto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros _ _ _ [f m1 m2 Hm] lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf' & Hb2 & Hff');
    eauto using Z.le_refl.
  rewrite Hm2'.
  exists (injpw f' m1' m2' Hm'); split; repeat rstep; eauto.
  constructor.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - assumption.
  - red. intros b b' delta Hb Hb'.
    assert (b = b1).
    {
      destruct (eq_block b b1); eauto.
      rewrite Hff' in Hb'; eauto.
      congruence.
    }
    assert (b' = b2) by congruence.
    subst.
    split; eauto using Mem.fresh_block_alloc.
Qed.

Next Obligation. (* Mem.free *)
  intros _ _ _ [f m1 m2 Hm] [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. inv H0. simpl in H1.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by extlia.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
  constructor.
  - red. eauto using Mem.perm_free_3.
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
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.load *)
  intros _ chunk _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr].
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation. (* Mem.store *)
  intros _ chunk _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  simpl in *. red.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
  constructor.
  - red. eauto using Mem.perm_store_2.
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
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros _ _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr] sz.
  simpl. red.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros _ _ _ [f m1 m2 Hm] [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl. red.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. extlia.
    }
    rewrite Hm2'.
    constructor.
    assert (Hm': Mem.inject f m1' m2') by eauto using Mem.storebytes_empty_inject.
    exists (injpw f m1' m2' Hm'); split.
    + constructor; eauto.
      * red. eauto using Mem.perm_storebytes_2.
      * red. eauto using Mem.perm_storebytes_2.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. extlia.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. extlia.
      * apply inject_separated_refl.
    + constructor; eauto.
  - assert (ptr_inject f (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. extlia.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto.
    rauto.
    rewrite Hm2'. constructor.
    exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
    constructor.
    + red. eauto using Mem.perm_storebytes_2.
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
      extlia.
    + apply inject_incr_refl.
    + apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.perm *)
  intros _ _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros _ _ _ [f m1 m2 Hm] b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 Hm].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 Hm].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by extlia.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by extlia.
  assumption.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  inv H0. cbn in *.
  eapply Mem.perm_inject_inv; eauto.
Qed.

Next Obligation.
  destruct H0 as (w' & Hw' & Hm').
  destruct Hw'. inv H. inv Hm'.
  split; eauto using Mem.unchanged_on_support.
Qed.


(** * Properties *)

(** Needs memory interpolation

Lemma injp_injp:
  subcklr injp (injp @ inj @ injp).
Proof.
  intros _ _ _ [f m1 m4 Hm14].
  eexists (injpw (meminj_dom f) m1 m1,
           (injw (meminj_dom f) (Mem.nextblock m1) (Mem.nextblock m1) _,
            injpw f m1 m4)).
  simpl.
  repeat apply conj.
  - exists m1; split.
    { constructor. eapply mem_inject_dom; eauto. }
    exists m1; split.
    { constructor; repeat rstep; eauto using mem_inject_dom. }
    constructor; eauto.
  - rewrite !meminj_dom_compose.
    apply inject_incr_refl.
  - intros (w12' & w23' & w34') m1' m4'.
    intros (m2' & Hm12' & m3' & Hm23' & Hm34').
    intros (H12 & H23 & H34). simpl in *.
    destruct Hm12' as [f12 m1' m2' Hm12'].
    inversion Hm23' as [f23 xm2' xm3' Hm23'']; clear Hm23'; subst.
    destruct Hm34' as [f34 m3' m4' Hm34'].
    inv H12.
    inv H23.
    inv H34.
    exists (injpw (compose_meminj f12 (compose_meminj f23 f34)) m1' m4').
    repeat apply conj.
    + constructor; eauto.
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
        (* XXX now we can, if we need to. *)
Abort.
*)

(*
Lemma injp_inj_injp:
  subcklr injp (injp @ inj @ injp).
Proof.
  intros _ _ _ [f m1 m4 Hm14].
  eexists (injpw (meminj_dom f) m1 m1,
           (injw (meminj_dom f) (Mem.nextblock m1) (Mem.nextblock m1) _,
            injpw f m1 m4)).
  simpl.
  repeat apply conj.
  - exists m1; split.
    { constructor. eapply mem_inject_dom; eauto. }
    exists m1; split.
    { constructor; repeat rstep; eauto using mem_inject_dom. }
    constructor; eauto.
  - rewrite !meminj_dom_compose.
    apply inject_incr_refl.
  - intros (w12' & w23' & w34') m1' m4'.
    intros (m2' & Hm12' & m3' & Hm23' & Hm34').
    intros (H12 & H23 & H34). simpl in *.
    destruct Hm12' as [f12 m1' m2' Hm12'].
    inversion Hm23' as [f23 xm2' xm3' Hm23'']; clear Hm23'; subst.
    destruct Hm34' as [f34 m3' m4' Hm34'].
    inv H12.
    inv H23.
    inv H34.
    exists (injpw (compose_meminj f12 (compose_meminj f23 f34)) m1' m4').
    repeat apply conj.
    + constructor; eauto.
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
        (* XXX now we can, if we need to. *)
Abort.
*)
