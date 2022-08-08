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

Lemma max_perm_decrease_refl :
  forall m, injp_max_perm_decrease m m.
Proof.
  intros. red. eauto.
Qed.

Lemma max_perm_decrease_trans :
  forall m1 m2 m3,
    injp_max_perm_decrease m1 m2 ->
    injp_max_perm_decrease m2 m3 ->
    Mem.sup_include (Mem.support m1) (Mem.support m2) ->
    injp_max_perm_decrease m1 m3.
Proof.
  intros. red in *. intros.
  apply H. auto. apply H0. apply H1. eauto. auto.
Qed.

Hint Resolve max_perm_decrease_refl max_perm_decrease_trans.

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

Definition inject_dom_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b s.

Definition inject_image_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b' s.

Definition inject_image_eq (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) <-> Mem.sup_In b' s.


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

Lemma injp_injp:
  subcklr injp (injp @ injp).
Proof.
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [f m1 m2 Hm].
  exists (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm),
          injpw f m1 m2 Hm); simpl.
  repeat apply conj.
  - exists se1. split; eauto.
    inv Hse. econstructor; auto. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [w12' w23'] m1' m3' (m2' & H12' & H23') [Hw12' Hw23']. cbn in *.
    destruct H12' as [f12' m1' m2' Hm12'].
    inversion H23' as [f23' xm2' xm3' Hm23']. clear H23'; subst.
    inversion Hw12' as [? ? ? ? ? ? ? ? ? ? UNMAP1 ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? ? ? ? ? ? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    eexists (injpw (compose_meminj f12' f23') m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; auto.
    + constructor; auto.
      *
        generalize (loc_unmapped_dom f). intros.
        inv UNMAP1. constructor; eauto.
        intros. apply unchanged_on_perm. apply H6. eauto.
        eauto.
        intros. apply unchanged_on_contents. apply H6. eauto.
        eauto.
      * rewrite <- (meminj_dom_compose f). rauto.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct SEP12'; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct SEP23'; eauto.
    + cbn. rstep; auto.
Qed.

(** Injection implies image is in the support *)

Lemma inject_implies_image_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_image_in f (Mem.support m2).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_2 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

(** Injection implies domain is in the support *)
Lemma inject_implies_dom_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_dom_in f (Mem.support m1).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_1 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

Lemma inject_dom_in_inv: forall f s b,
    inject_dom_in f s -> ~sup_In b s -> f b = None.
Proof.
  intros. destruct (f b) eqn:?. destruct p.
  apply H in Heqo. congruence. auto.
Qed.

(** Construction of meminj j1' j2' *)

Definition meminj_add (f:meminj) b1 r:=
  fun b => if (eq_block b b1) then Some r else f b.

Lemma meminj_add_new: forall f a b,
    meminj_add f a b a = Some b.
Proof.
  intros. unfold meminj_add. rewrite pred_dec_true; auto.
Qed.

Lemma meminj_add_diff: forall j a b a' ofs,
    a <> b ->
    meminj_add j a (a',ofs ) b = j b.
Proof.
  intros. unfold meminj_add. destruct eq_block; congruence.
Qed.

Lemma meminj_add_incr: forall f a b,
    f a = None -> inject_incr f (meminj_add f a b).
Proof.
  intros. intro. unfold meminj_add. intros.
  destruct eq_block. subst. congruence. eauto.
Qed.

Lemma meminj_add_compose : forall f1 f2 a b c o,
    (forall b0 z, ~ f1 b0 = Some (b,z)) ->
    compose_meminj (meminj_add f1 a (b,0)) (meminj_add f2 b (c,o)) =
    meminj_add (compose_meminj f1 f2) a (c,o).
Proof.
  intros. apply Axioms.extensionality. intro x.
  unfold compose_meminj, meminj_add.
  destruct (eq_block x a). rewrite pred_dec_true; eauto.
  destruct (f1 x) eqn: Hf1; eauto. destruct p.
  destruct (eq_block b0 b); eauto. subst. apply H in Hf1. inv Hf1.
Qed.

Fixpoint update_meminj12 (sd1': list block) (j1 j2 j': meminj) (si1: sup) :=
  match sd1' with
    |nil => (j1,j2,si1)
    |hd::tl =>
       match compose_meminj j1 j2 hd, (j' hd) with
       | None , Some (b2,ofs) =>
         let b0 := fresh_block si1 in
         update_meminj12 tl (meminj_add j1 hd (b0,0) )
                         (meminj_add j2 (fresh_block si1) (b2,ofs))
                         j' (sup_incr si1)
       | _,_ => update_meminj12 tl j1 j2 j' si1
       end
  end.

(* results of update_meminj*)
Definition inject_incr_no_overlap' (j j' : meminj) : Prop :=
  forall b1 b2 b1' b2' delta1 delta2,
    b1 <> b2 -> j b1 = None -> j b2 = None ->
    j' b1 = Some (b1', delta1) -> j' b2 = Some (b2',delta2) ->
    b1' <> b2'.

Definition update_add_exists (j12 j12' j': meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) ->
    exists b3 ofs3, j' b1 = Some (b3,ofs3).

Definition update_add_zero (j12 j12' : meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) -> ofs2 = 0.

Definition update_add_same (j23 j23' j12': meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    exists b1, j12' b1 = Some (b2,0) /\
    (forall b1' d, j12' b1' = Some (b2,d) -> b1' = b1).

Lemma update_properties: forall s1' s1 j1 j2 s2 s2' j1' j2' j' s3,
    update_meminj12 s1' j1 j2 j' s2 = (j1',j2',s2') ->
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include s2 s2'
    /\ inject_image_in j1' s2'
    /\ inject_dom_in j2' s2'
    /\ inject_incr_disjoint j1 j1' s1 s2
    /\ inject_incr_disjoint j2 j2' s2 s3
    /\ inject_incr_no_overlap' j1 j1'
    /\ update_add_exists j1 j1' j'
    /\ update_add_zero j1 j1'
    /\ update_add_same j2 j2' j1'.
Proof.
  induction s1'.
  - (*base*)
    intros; inv H. repeat apply conj; try congruence; eauto.
  - (*induction*)
    intros until s3. intros UPDATE DOMIN12 IMGIN12 DOMIN23
           INCR13 INCRDISJ13. inv UPDATE.
    destruct (compose_meminj j1 j2 a) eqn: Hja. eauto.
    destruct (j' a) as [[b z]|] eqn:Hj'a; eauto.
    exploit INCRDISJ13; eauto. intros [a_notin_sd1 b_notin_si2].
    (* facts *)
    assert (MIDINCR1: inject_incr j1 (meminj_add j1 a (fresh_block s2,0))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN12 in H. congruence.
    }
    assert (MIDINCR2: inject_incr j2 (meminj_add j2 (fresh_block s2) (b,z))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN23 in H. subst. apply freshness in H. inv H.
    }
    assert (MIDINCR3: inject_incr (meminj_add (compose_meminj j1 j2) a (b,z)) j').
    {
      red. intros b0 b' o INJ. unfold meminj_add in INJ.
      destruct (eq_block b0 a). congruence. eauto.
    }
    exploit IHs1'. eauto.
    (* rebuild preconditions for induction step *)
    + instantiate (1:= (a :: s1)).
      red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      left. auto. right. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + rewrite meminj_add_compose; eauto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    + instantiate (1:= s3). rewrite meminj_add_compose.
      red. intros b0 b' o INJ1 INJ2. unfold meminj_add in INJ1. destruct (eq_block b0 a).
      congruence. exploit INCRDISJ13; eauto. intros [A B]. split.
      intros [H|H]; congruence.
      auto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    +
    intros (incr1& incr2 & sinc & imagein1 & domin2 &
            disjoint1 & disjoint2 & no_overlap & add_exists & add_zero & add_same).
    repeat apply conj; eauto.
    (*incr1*)
    eapply inject_incr_trans; eauto.
    (*incr2*)
    eapply inject_incr_trans; eauto.
    (*disjoint1*)
    {
    red. red in disjoint1. intros b0 b' delta INJ1 INJ2.
    destruct (eq_block b0 a).
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intro INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd. split. auto. apply freshness.
    + exploit disjoint1. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. right. auto. intro. apply B. apply Mem.sup_incr_in2. auto.
    }
    (*disjoint2*)
    {
    red. red in disjoint2. intros b0 b' delta INJ1 INJ2. set (nb := fresh_block s2).
    destruct (eq_block b0 nb).
    + subst. generalize (meminj_add_new j2 nb (b,z)). intro INJadd. apply incr2 in INJadd.
      rewrite INJ2 in INJadd. inv INJadd. split. apply freshness. auto.
    + exploit disjoint2. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. apply Mem.sup_incr_in2. auto. intro. apply B. auto.
    }
    (*new_no_overlap*)
    {
    red. red in no_overlap. intros b1 b2 b1' b2' delta1 delta2 Hneq NONE1 NONE2 INJ1 INJ2.
    destruct (eq_block b1 a); destruct (eq_block b2 a).
    + congruence.
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ1 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff; eauto. eauto. intros [A B].
      intro. subst. apply B. apply Mem.sup_incr_in1.
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff. apply NONE1. eauto. eauto. intros [A B].
      intro. subst. apply B. apply Mem.sup_incr_in1.
    + eapply no_overlap. apply Hneq. rewrite meminj_add_diff; eauto.
      rewrite meminj_add_diff; eauto. eauto. eauto.
    }
    (* add_exists*)
    {
    red. red in add_exists. intros. destruct (eq_block a b1).
    + subst. eauto.
    + eapply add_exists; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_zero. intros. destruct (eq_block a b1).
      subst. generalize (meminj_add_new j1 b1 (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite H1 in INJadd. inv INJadd. auto.
      eapply add_zero; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_same. intros. destruct (eq_block b2 (fresh_block s2)).
      - subst.
      generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. eauto. exists a. split. auto.
      intros.
      destruct (meminj_add j1 a (fresh_block s2, 0) b1') as [[b2' d']|] eqn : Hj1add.
        + destruct (eq_block b1' a). subst. auto.
          apply incr1 in Hj1add as Hj1'.
          rewrite meminj_add_diff in Hj1add; eauto.
          apply IMGIN12 in Hj1add as FRESH.
          rewrite H2 in Hj1'. inv Hj1'.
          exfalso. eapply freshness; eauto.
        + exploit disjoint1; eauto. intros [A B].
          exfalso. apply B. apply Mem.sup_incr_in1.
      - eapply add_same; eauto. rewrite meminj_add_diff; eauto.
    }
Qed.

(** Lemmas to prove j' = compose_meminj j1' j2' *)
Fixpoint update_meminj sd1' j j':=
  match sd1' with
    |nil => j
    |hd::tl => match j hd, j' hd with
              |None, Some (b,ofs) => update_meminj tl (meminj_add j hd (b,ofs)) j'
              |_,_ => update_meminj tl j j'
              end
  end.


Definition meminj_sub (j:meminj) (b:block) :=
  fun b0 => if (eq_block b b0) then None else j b0.

Lemma update_meminj_old: forall s j j' b b' ofs,
  j b = Some (b', ofs) ->
  update_meminj s j j' b = Some (b',ofs).
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja.
    eauto. destruct (j' a) eqn: Hj'a. destruct p.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto.
    eauto.
Qed.

Lemma update_meminj_diff1: forall s j j' a b a' ofs,
    a <> b ->
    update_meminj s j j' b =
    update_meminj s (meminj_add j a (a',ofs)) j' b.
Proof.
  induction s; intros.
  - simpl. unfold meminj_add. destruct (eq_block b a); congruence.
  - simpl.
    destruct (j a) eqn: Hja. eauto.
    + unfold meminj_add at 1. destruct eq_block.
      -- subst. eauto.
      -- rewrite Hja. eauto.
    + unfold meminj_add at 2. destruct eq_block.
      -- subst. destruct (j' a0). destruct p.
         erewrite <- IHs; eauto.
         erewrite <- IHs; eauto.
      -- rewrite Hja. destruct (j' a). destruct p.
         destruct (eq_block a b).
         ++ subst. erewrite update_meminj_old. 2: apply meminj_add_new.
            erewrite update_meminj_old. 2: apply meminj_add_new. auto.
         ++ erewrite <- IHs; eauto.
         erewrite <- IHs with (j := (meminj_add j a0 (a', ofs))); eauto.
         ++ erewrite <- IHs; eauto.
Qed.

Lemma update_meminj_diff: forall s j j' a b,
    a <> b ->
    update_meminj s j (meminj_sub j' a) b =
    update_meminj s j j' b.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja. eauto.
    destruct (eq_block a0 a).
    + subst. unfold meminj_sub. rewrite pred_dec_true; eauto.
      replace (fun b0 : positive => if eq_block a b0 then None else j' b0) with (meminj_sub j' a); eauto.
      rewrite IHs. destruct (j' a).
      -- destruct p. erewrite update_meminj_diff1; eauto.
      -- auto.
      -- auto.
    + unfold meminj_sub. rewrite pred_dec_false; eauto.
      destruct (j' a). destruct p. eauto.
      eauto.
Qed.

Lemma inject_dom_in_sub: forall j a s,
    inject_dom_in j (a::s) ->
    inject_dom_in (meminj_sub j a) s.
Proof.
  intros.
  red. red in H. intros. unfold meminj_sub in H0.
  destruct eq_block in H0. congruence. exploit H; eauto.
  intros [A|A]. congruence. auto.
Qed.

Lemma meminj_sub_diff: forall j a b,
    a <> b -> meminj_sub j a b = j b.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma meminj_sub_none : forall j a,
    meminj_sub j a a = None.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma update_meminj_new: forall s j j' b b' ofs,
  j b = None ->
  j' b = Some (b',ofs) ->
  inject_dom_in j' s ->
  update_meminj s j j' b = j' b.
Proof.
  induction s; intros.
  - simpl. apply H1 in H0. inv H0.
  - simpl.
    destruct (j a) as [[a' ofs']|]eqn:Hja.
    + (*here we know a <> b by j a <> j b*)
      generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false; congruence.
      apply inject_dom_in_sub; eauto.
      intro IH.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto. congruence. congruence.
    + destruct (eq_block a b).
      -- subst. rewrite H0. erewrite update_meminj_old. eauto.
         apply meminj_add_new.
      -- generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false.
      auto. congruence. apply inject_dom_in_sub; eauto. intro IH.
      destruct (j' a). destruct p. erewrite <- update_meminj_diff1; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
Qed.

Lemma update_meminj_none: forall s j j' b,
  j b = None ->
  j' b = None ->
  update_meminj s j j' b = None.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) as [[a' ofs']|]eqn:Hja.
    eauto. destruct (j' a) as [[a' ofs']|]eqn:Hj'a.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto. auto. eauto.
Qed.

Lemma update_meminj_eq: forall sd1' j j',
    inject_dom_in j' sd1' ->
    inject_incr j j' ->
    update_meminj sd1' j j' = j'.
Proof.
  intros. apply Axioms.extensionality.
  intro x.
  destruct (j x) as [[y ofs]|] eqn: Hj.
  - erewrite update_meminj_old; eauto.
    apply H0 in Hj. congruence.
  - destruct (j' x) as [[y ofs]|] eqn: Hj'.
    erewrite update_meminj_new; eauto.
    erewrite update_meminj_none; eauto.
Qed.

Lemma update_compose_meminj : forall sd1' j1 j2 j' si1 si1' j1' j2',
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    inject_image_in j1 si1 ->
    update_meminj sd1' (compose_meminj j1 j2) j' = (compose_meminj j1' j2').
Proof.
  induction sd1'; intros.
  - inv H. simpl. auto.
  - inv H. simpl. destruct (compose_meminj) eqn : Hja.
    + eauto.
    + destruct (j' a) eqn: Hj'a.
      -- destruct p.
         apply IHsd1' in H2.
         rewrite <- H2. f_equal. apply Axioms.extensionality.
         intro x.
         destruct (compose_meminj j1 j2 x) eqn: Hjx.
         ++ destruct (eq_block a x).
            * congruence.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness; eauto.
              ** auto.
         ++ destruct (eq_block a x).
            * subst. rewrite meminj_add_new.
              unfold compose_meminj.
              rewrite meminj_add_new. rewrite meminj_add_new. eauto.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness; eauto.
              ** auto.
         ++ red. intros. red in H0. destruct (eq_block a b0).
            * subst. rewrite meminj_add_new in H. inv H. apply Mem.sup_incr_in1.
            * rewrite meminj_add_diff in H. exploit H0; eauto.
              intro. right. auto. auto.
      -- eauto.
Qed.

Lemma update_compose: forall j1 j2 j' sd1' si1 si1' j1' j2' sd1 si2,
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    inject_dom_in j' sd1' ->
    inject_dom_in j1 sd1 ->
    inject_image_in j1 si1 ->
    inject_dom_in j2 si1 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' sd1 si2 ->
    j' = (compose_meminj j1' j2').
Proof.
  intros.
  exploit update_compose_meminj; eauto.
  intro A.
  exploit update_meminj_eq. apply H0.  eauto.
  intro B. congruence.
Qed.

Lemma add_from_to_dom_in : forall s1 s1' j12 j12' j',
    update_add_exists j12 j12' j' ->
    Mem.sup_include s1 s1' ->
    inject_dom_in j12 s1 ->
    inject_incr j12 j12' ->
    inject_dom_in j' s1' ->
    inject_dom_in j12' s1'.
Proof.
  intros. red. intros.
  destruct (j12 b) as [[b'' o']|] eqn: Hj12.
  + erewrite H2 in H4; eauto.
  + exploit H; eauto. intros (b3 & ofs3 & Hj'). eauto.
Qed.


(** Inversion of inject increment *)
Lemma inject_incr_inv: forall j1 j2 j' s1 s2 s3 s1',
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_dom_in j' s1' ->
    Mem.sup_include s1 s1' ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    exists j1' j2' s2', j' = compose_meminj j1' j2' /\
               inject_incr j1 j1' /\
               inject_incr j2 j2' /\
               Mem.sup_include s2 s2' /\
               inject_dom_in j1' s1' /\
               inject_image_in j1' s2' /\
               inject_dom_in j2' s2' /\
               inject_incr_disjoint j1 j1' s1 s2 /\
               inject_incr_disjoint j2 j2' s2 s3 /\
               inject_incr_no_overlap' j1 j1' /\
               update_add_zero j1 j1' /\
               update_add_exists j1 j1' j' /\
               update_add_same j2 j2' j1'.
Proof.
  intros.
  destruct (update_meminj12 s1' j1 j2 j' s2) as [[j1' j2'] s2'] eqn: UPDATE.
  exists j1' ,j2' ,s2'.
  exploit update_compose; eauto. intro COMPOSE.
  exploit update_properties; eauto. intros (A & B & C & D & E & F & G & I & J & K & L).
  repeat apply conj; eauto. eapply add_from_to_dom_in; eauto.
Qed.

(** Inversion of injection composition *)

(* no_overlaping from update_meminj12 *)
Lemma update_meminj_no_overlap1 : forall m1' m1 m2 j1 j1',
    injp_max_perm_decrease m1 m1' ->
    inject_incr j1 j1' ->
    Mem.inject j1 m1 m2 ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    inject_incr_no_overlap' j1 j1' ->
    Mem.meminj_no_overlap j1' m1' .
Proof.
  intros m1' m1 m2 j1 j1' MPD INCR INJECT INCRDISJ INCRNOLAP.
  red. intros.
  destruct (j1 b1) as [[b1'' delta1']|] eqn : H0';
  destruct (j1 b2) as [[b2'' delta2']|] eqn : H1'.
  - (* old mappings *)
    erewrite INCR in H0; eauto. inv H0.
    erewrite INCR in H1; eauto. inv H1.
    inversion INJECT. apply inject_implies_dom_in in INJECT as DOMIN.
    eapply mi_no_overlap; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
  - (* b1 old, b2 new *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H0; eauto. inv H0.
    apply IMGIN in H0'. left. congruence.
  - (* b1 new, b2 old *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H1; eauto. inv H1.
    apply IMGIN in H1'. left. congruence.
  - (* new mappings *)
    left. eauto.
Qed.

Lemma pmap_update_diff: forall (A:Type) b f (map1 map2: NMap.t A) b',
  Mem.pmap_update b f map1 = map2 ->
  b <> b' ->
  NMap.get _ b' map1 = NMap.get _ b' map2.
Proof.
  intros. rewrite <- H. unfold Mem.pmap_update.
  rewrite NMap.gsspec. rewrite pred_dec_false; auto.
Qed.

Lemma map_perm_1 : forall f b1 m1 m2 m2' b2 ofs2 k p,
        Mem.map f b1 m1 m2 = m2' ->
        (~ exists delta, f b1 = Some (b2, delta)) ->
        Mem.perm m2' b2 ofs2 k p <->
        Mem.perm m2 b2 ofs2 k p.
Proof.
  intros. unfold Mem.map in H.
  destruct (f b1) as [[b1' delta']|] eqn :Hfb.
  - destruct (eq_block b1' b2).
    + subst. exfalso. apply H0. eauto.
    + destruct (Mem.sup_dec b1' (Mem.support m2)).
      inv H. unfold Mem.perm in *. simpl in *.
      erewrite <- pmap_update_diff; eauto;
      reflexivity.
      subst. reflexivity.
  - subst. reflexivity.
Qed.

Lemma map_perm_2 : forall f b1 m1 m2 m2' b2 delta ofs2 k p,
    Mem.map f b1 m1 m2 = m2' ->
    f b1 = Some (b2, delta) ->
    Mem.perm m2' b2 ofs2 k p <->
    if ((Mem.sup_dec b2 (Mem.support m2))&& (Mem.perm_dec m1 b1 (ofs2 - delta) Max Nonempty)) then
      Mem.perm m1 b1 (ofs2 - delta) k p else
      Mem.perm m2 b2 ofs2 k p.
Proof.
  intros.
  unfold Mem.map in H. rewrite H0 in H.
  destruct (Mem.sup_dec b2 (Mem.support m2)) eqn: Hb1; try (simpl; subst; reflexivity).
  inv H. unfold Mem.perm. simpl. unfold Mem.pmap_update. rewrite NMap.gsspec.
  rewrite pred_dec_true; eauto.
  destruct (Mem.perm_dec m1 b1 (ofs2 - delta) Max Nonempty); simpl.
    + unfold Mem.update_mem_access. unfold Mem.perm in p0.
      destruct (NMap.get (Z -> perm_kind -> option permission) b1 (Mem.mem_access m1) (ofs2 - delta) Max) eqn: Hperm.
      unfold Mem.perm_check_any. rewrite Hperm. reflexivity. exfalso. apply p0.
    + unfold Mem.update_mem_access.
      unfold Mem.perm in n.
      destruct (NMap.get (Z -> perm_kind -> option permission) b1 (Mem.mem_access m1) (ofs2 - delta) Max) eqn: Hperm.
      exfalso. apply n. simpl. constructor.
      unfold Mem.perm_check_any. rewrite Hperm. reflexivity.
Qed.

Lemma map_perm_3 :  forall f b1 m1 m2 m2' b2 b2' delta ofs2 k p,
        Mem.map f b1 m1 m2 = m2' ->
        f b1 = Some (b2,delta) ->
        b2 <> b2' ->
        Mem.perm m2' b2' ofs2 k p <->
        Mem.perm m2 b2' ofs2 k p.
Proof.
  intros. eapply map_perm_1; eauto.
  intros [d A]. congruence.
Qed.

Lemma inject_map_meminj_sub : forall s1' s2' j1' b1 m1' m2 m2' m2'1 b2 delta b2' ofs k p,
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
    Mem.inject_map s1' s2' (meminj_sub j1' b1) m1' m2 = m2'1 ->
    j1' b1 = Some (b2, delta) ->
    b2' <> b2 ->
    Mem.perm m2' b2' ofs k p <-> Mem.perm m2'1 b2' ofs k p.
Proof.
  induction s1'; intros.
  - inv H0. simpl. reflexivity.
  - exploit IHs1'; eauto. intro IH.
    destruct (eq_block b1 a).
    + subst. simpl.
      etransitivity. erewrite map_perm_3; eauto. symmetry.
      etransitivity; eauto.
      erewrite map_perm_1. 2: eauto. symmetry. eauto. rewrite meminj_sub_none.
      intros [delta0 A]. congruence.
    + destruct (j1' a) as [[b2'' delta']|] eqn: Ha.
      * simpl in H0, H1. destruct (eq_block b2'' b2').
        -- subst.
           rewrite map_perm_2; eauto. rewrite Mem.inject_map_support. 2: eauto.  symmetry.
           rewrite map_perm_2; eauto. rewrite Mem.inject_map_support. 2: eauto.
           2: rewrite meminj_sub_diff; eauto.
           destruct (Mem.sup_dec b2' s2' && Mem.perm_dec m1' a (ofs - delta') Max Nonempty); eauto.
           reflexivity. symmetry. eauto.
        -- rewrite map_perm_3; eauto. symmetry.
           rewrite map_perm_3; eauto. symmetry. eauto.
           rewrite meminj_sub_diff; eauto.
      * simpl in H0, H1. unfold Mem.map in H0,H1. rewrite Ha in H0.
        rewrite meminj_sub_diff in H1. rewrite Ha in H1. congruence. eauto.
Qed.

Lemma inject_map_meminj_sub_1 : forall s1' s2' j1' b1 m1' m2 m2' m2'1 b2 delta ofs k p,
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
    Mem.inject_map s1' s2' (meminj_sub j1' b1) m1' m2 = m2'1 ->
    j1' b1 = Some (b2, delta) ->
    (forall ofs1 k p, Mem.perm m1' b1 ofs1 k p -> ofs1 + delta <> ofs) ->
    Mem.perm m2' b2 ofs k p <-> Mem.perm m2'1 b2 ofs k p.
Proof.
    induction s1'; intros.
  - inv H0. simpl. reflexivity.
  - exploit IHs1'; eauto. intro IH.
    destruct (eq_block b1 a).
    + subst. simpl.
      etransitivity. erewrite map_perm_2; eauto.
        destruct (Mem.perm_dec). apply H3 in p0 as p1. extlia.
        simpl. rewrite andb_false_r. eauto.
        symmetry. rewrite map_perm_1. 2: eauto. reflexivity.
        rewrite meminj_sub_none; eauto. intros [delta0 A]. congruence.
    + destruct (j1' a) as [[b2'' delta']|] eqn: Ha.
      * simpl in H0, H1. destruct (eq_block b2'' b2).
        -- subst.
           rewrite map_perm_2; eauto. rewrite Mem.inject_map_support; auto. symmetry.
           rewrite map_perm_2; eauto. rewrite Mem.inject_map_support; auto. 2: rewrite meminj_sub_diff; eauto.
           destruct (Mem.sup_dec b2 s2' && Mem.perm_dec m1' a (ofs - delta') Max Nonempty); eauto.
           reflexivity. symmetry. eauto.
        -- rewrite map_perm_3; eauto. symmetry.
           rewrite map_perm_3; eauto. symmetry. eauto.
           rewrite meminj_sub_diff; eauto.
      * simpl in H0, H1. unfold Mem.map in H0,H1. rewrite Ha in H0.
        rewrite meminj_sub_diff in H1. rewrite Ha in H1. congruence. eauto.
Qed.

Lemma inject_map_perm : forall s1' s2' j1' m1' m2 m2' b1 ofs1 delta b2 k p,
   Mem.sup_include (Mem.support m2) s2' ->
   Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
   Mem.meminj_no_overlap j1' m1' ->
   inject_dom_in j1' s1' ->
   inject_image_in j1' s2' ->
   j1' b1 = Some (b2,delta) ->
   Mem.perm m1' b1 ofs1 k p ->
   Mem.perm m2' b2 (ofs1 + delta) k p.
Proof.
  induction s1'; intros until p; intros SUPINCL INJMAP INJNOLAP DOMIN IMGIN MAP PERM1.
  - inv INJMAP. apply DOMIN in MAP. inv MAP.
  - simpl in INJMAP. destruct (eq_block a b1).
    + (*local*)
      subst. rewrite map_perm_2; eauto.
      rewrite Mem.inject_map_support; auto. replace (ofs1 + delta - delta) with ofs1 by lia.
      apply IMGIN in MAP as SUPIN2.
      destruct (Mem.sup_dec b2 s2') eqn : Hsup; try congruence; simpl.
      destruct (Mem.perm_dec m1' b1 ofs1 Max Nonempty). simpl. eauto.
      exfalso. apply n. eauto with mem.
    + (* induction *)
      generalize (IHs1' s2' (meminj_sub j1' a) m1').
      intros. exploit H; eauto.
      {
        red. red in INJNOLAP. intros.
        destruct (eq_block a b0); destruct (eq_block a b3).
        * subst. congruence.
        * subst. unfold meminj_sub in H1. rewrite pred_dec_true in H1; auto. inv H1.
        * subst. unfold meminj_sub in H2. rewrite pred_dec_true in H2; auto. inv H2.
        * eapply INJNOLAP. apply H0. rewrite meminj_sub_diff in H1; eauto.
          rewrite meminj_sub_diff in H2; eauto. eauto. eauto.
      }
      {
        red. intros. destruct (eq_block a b).
        * subst. unfold meminj_sub in H0. rewrite pred_dec_true in H0; auto. inv H0.
        * rewrite meminj_sub_diff in H0. exploit DOMIN; eauto. intros [A | B].
          congruence. eauto. eauto.
      }
      { red. intros. destruct (eq_block a b).
        * subst. unfold meminj_sub in H0. rewrite pred_dec_true in H0; auto. inv H0.
        * rewrite meminj_sub_diff in H0. exploit IMGIN; eauto. eauto.
      }
      erewrite meminj_sub_diff; eauto.
      intro PERMmid.
      destruct (j1' a) as [[b2' delta']|] eqn : Hj1'a.
      * destruct (eq_block b2 b2').
        -- subst.
           assert (forall ofs1' k p, Mem.perm m1' a ofs1' k p -> ofs1' + delta' <> ofs1 + delta).
           { intros. exploit INJNOLAP; eauto with mem.
             intros [A|A]; congruence.
           }
           erewrite map_perm_2; eauto.
           destruct (Mem.perm_dec).
           apply H0 in p0 as p1. extlia. simpl. rewrite andb_false_r.
           eapply inject_map_meminj_sub_1; eauto.
        -- erewrite map_perm_1. 2: eauto.
           eapply inject_map_meminj_sub; eauto.
           intros [delta''  A]. congruence.
      * unfold Mem.map in INJMAP. rewrite Hj1'a in INJMAP.
        rewrite <- INJMAP.
        replace (meminj_sub j1' a) with j1' in PERMmid.
        auto. apply Axioms.extensionality. intro x. destruct (eq_block a x).
        subst. unfold meminj_sub. rewrite pred_dec_true; eauto.
        rewrite meminj_sub_diff; eauto.
Qed.

Definition mem_memval (m:mem) b ofs : memval :=
  Maps.ZMap.get ofs (NMap.get _ b (Mem.mem_contents m)).


Lemma map_content_1 : forall f b1 m1 m2 m2' b2 ofs2,
    Mem.map f b1 m1 m2 = m2' ->
    (~exists delta, f b1 = Some (b2,delta)) ->
    mem_memval m2' b2 ofs2 = mem_memval m2 b2 ofs2.
Proof.
  intros. unfold Mem.map in H.
  destruct (f b1) as [[b1' delta']|] eqn :Hfb.
  - destruct (eq_block b1' b2).
    + subst. exfalso. apply H0. eauto.
    + destruct (Mem.sup_dec b1' (Mem.support m2)).
      inv H. unfold mem_memval in *. simpl in *.
      erewrite <- pmap_update_diff; eauto;
      reflexivity.
      subst. reflexivity.
  - subst. reflexivity.
Qed.

Lemma map_content_2 : forall f b1 m1 m2 m2' b2 delta ofs2 ,
    Mem.map f b1 m1 m2 = m2' ->
    f b1 = Some (b2,delta) ->
    mem_memval m2' b2 ofs2 =
    if (Mem.sup_dec b2 (Mem.support m2) && Mem.perm_dec m1 b1 (ofs2 - delta) Cur Readable)
    then Mem.memval_map f (mem_memval m1 b1 (ofs2 - delta)) else mem_memval m2 b2 ofs2.
Proof.
  intros.
  unfold Mem.map in H. rewrite H0 in H.
  destruct (Mem.sup_dec b2 (Mem.support m2)); try (simpl; subst; reflexivity).
  inv H. unfold mem_memval. simpl. unfold Mem.pmap_update. rewrite NMap.gsspec.
  rewrite pred_dec_true; eauto.
  destruct (Mem.perm_dec m1 b1 (ofs2 - delta) Max Nonempty); simpl; eauto.
    + unfold Mem.update_mem_content. simpl. admit.
    + unfold Mem.update_mem_content. unfold Mem.content_map.
Admitted. (*ok*)


Lemma memval_map_inject_new : forall j1 j2 mv mv3,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j1 mv (Mem.memval_map j1 mv).
Proof.
  intros. destruct mv; simpl; try constructor.
  destruct v; simpl; try repeat constructor.
  destruct (j1 b) as [[b1 d]|] eqn : ?.
  repeat constructor. econstructor; eauto.
  inv H. inv H4. unfold compose_meminj in H1. rewrite Heqo in H1.
  congruence.
Qed.

Lemma memval_map_inject_old : forall j1 mv mv2,
    memval_inject j1 mv mv2 ->
    memval_inject j1 mv (Mem.memval_map j1 mv).
Proof.
  intros. destruct mv; simpl; try constructor.
  destruct v; simpl; try repeat constructor.
  destruct (j1 b) as [[b1 d]|] eqn : ?.
  repeat constructor. econstructor; eauto.
  inv H. inv H4. congruence.
Qed.

Lemma source_value_closure: forall m1 m2 m1' m3' j1 j2 j1' j2' b1 ofs1 b2 delta,
    Mem.inject j1 m1 m2 ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
    inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2') ->
    inject_incr j1 j1' ->
    update_add_exists j1 j1' (compose_meminj j1' j2') ->
    j1' b1 = Some (b2,delta) ->
    Mem.perm m1' b1 ofs1 Cur Readable ->
    memval_inject j1' (mem_memval m1' b1 ofs1)(Mem.memval_map j1' (mem_memval m1' b1 ofs1)).
Proof.
  intros until delta. intros INJ12 INJ13' UNMAP INCR13 INCR12 ADDEXISTS MAP PERM.
  destruct (j1 b1) as [[b2' delta2]|] eqn: Hmapped12.
  - destruct (compose_meminj j1 j2 b1) as [[b3 delta3]|] eqn: Hmapped13.
    + apply INCR13 in Hmapped13.
      eapply memval_map_inject_new.
      inversion INJ13'. inversion mi_inj.
      eapply mi_memval; eauto.
    + inversion UNMAP. inversion INJ12.
      assert (mem_memval m1' b1 ofs1 = mem_memval m1 b1 ofs1).
      unfold mem_memval. apply unchanged_on_contents.
      eauto. eapply unchanged_on_perm; eauto.
      destruct (Mem.sup_dec b1 (Mem.support m1)). eauto. apply mi_freeblocks in n. congruence.
      eapply memval_map_inject_old. inversion mi_inj. rewrite H.
      eapply memval_inject_incr. 2: eauto.
      eapply mi_memval. eauto.
      eapply unchanged_on_perm. eauto.
      destruct (Mem.sup_dec b1 (Mem.support m1)). eauto. apply mi_freeblocks in n. congruence.
      eauto.
  - exploit ADDEXISTS; eauto. intros (b3 & delta3 & Hmapped13).
    eapply memval_map_inject_new.
    inversion INJ13'. inversion mi_inj.
    eapply mi_memval; eauto.
Qed.

Lemma inject_map_content : forall s1' s2' j1' j2' m1' m2' m3' b1 ofs1 delta b2 j1 j2 m1 m2,
   Mem.sup_include (Mem.support m2) s2' ->
   Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
   Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
   Mem.inject (compose_meminj j1' j2') m1' m3' ->
   inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2') ->
   inject_incr j1 j1' ->
   Mem.inject j1 m1 m2 ->
   Mem.meminj_no_overlap j1' m1' ->
   update_add_exists j1 j1' (compose_meminj j1' j2') ->
   sup_In b1 s1' -> sup_In b2 s2' ->
   j1' b1 = Some (b2,delta) ->
   Mem.perm m1' b1 ofs1 Cur Readable ->
   memval_inject j1' (mem_memval m1' b1 ofs1) (mem_memval m2' b2 (ofs1+ delta)).
Proof.
  induction s1'; intros until m2; intros SUPINCL2 INJMAP UNMAP INJ13' INCR13 INCR12 INJ12 INJNOLAP ADDEXISTS IN1 IN2 MAP PERM1.
  - inv INJMAP. inv IN1.
  - simpl in INJMAP. destruct IN1.
    subst.
    + erewrite map_content_2 with (m2' :=(Mem.map j1' b1 m1' (Mem.inject_map s1' s2' j1' m1' m2))); eauto.
      rewrite Mem.inject_map_support; auto. replace (ofs1 + delta - delta) with ofs1 by lia.
      destruct (Mem.sup_dec b2 s2'); try congruence; simpl.
      destruct (Mem.perm_dec m1' b1 ofs1 Cur Readable); simpl.
      eapply source_value_closure; eauto.
      exfalso. apply n. eauto with mem.
    + destruct (j1' a) as [[a' delta']|] eqn: Hj1'a.
      -- destruct (eq_block a' b2).
         ++ (* the case where we need to use no_overlap to state the image of a and b1 diffs*)
            subst.
            destruct (eq_block a b1) eqn: Hab1.
            * replace delta' with delta in * by congruence. subst.
              erewrite map_content_2 with (m2' := (Mem.map j1' b1 m1' (Mem.inject_map s1' s2' j1' m1' m2))); eauto.
              rewrite Mem.inject_map_support; auto.
              destruct (Mem.sup_dec b2 s2'); try congruence. simpl.
              replace (ofs1 + delta - delta) with ofs1 in * by lia. subst.
              destruct (Mem.perm_dec m1' b1 ofs1 Cur Readable) eqn : Hb; simpl.
              eapply source_value_closure; eauto.
              eapply IHs1'; eauto.
            * simpl.
              erewrite map_content_2 with (m2' := (Mem.map j1' a m1' (Mem.inject_map s1' s2' j1' m1' m2))); eauto.
              rewrite Mem.inject_map_support; auto.
              destruct (Mem.sup_dec b2 s2'); try congruence. simpl.
              destruct (Mem.perm_dec m1' a (ofs1 + delta - delta') Cur Readable) eqn : Hb; simpl.
              exploit INJNOLAP; eauto with mem. intros [A | B].
              congruence. extlia.
              eapply IHs1'; eauto.
         ++ erewrite map_content_1 with (m2' := m2'); eauto. intros [d A]. congruence.
      -- erewrite map_content_1 with (m2' := m2'); eauto. intros [d A]. congruence.
Qed.

Theorem inject_mem_inj1 : forall m1 m1' s2' j1 j2 j1' j2' m2 m2' m3',
    Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
    Mem.inject j1 m1 m2 ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    Mem.sup_include (Mem.support m2) s2' ->
    inject_incr j1 j1' ->
    inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2') ->
    injp_max_perm_decrease m1 m1' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    inject_dom_in j1' (Mem.support m1') ->
    inject_image_in j1' s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    update_add_zero j1 j1' ->
    update_add_exists j1 j1' (compose_meminj j1' j2') ->
    Mem.mem_inj j1' m1' m2'.
Proof.
  intros until m3'. intros UNMAP1 INJ12 INJ13' SUPINCL2 INCR12 INCR13 MAXPERM1
                           INJMEM DOMIN' IMGIN' INCRNOLAP1 ADDZERO1 ADDEXISTS1.
  constructor.
  - intros. eapply inject_map_perm; eauto.
  - intros. destruct (j1 b1) as [[b2' delta']|] eqn : Hj1b1.
    + erewrite INCR12 in H; eauto. inv H. inversion INJ12. inversion mi_inj.
      eapply mi_align; eauto. apply inject_implies_dom_in in INJ12 as DOMIN.
      red. intros.
      red in H0. eapply MAXPERM1. eapply DOMIN; eauto. eapply H0; eauto.
    + exploit ADDZERO1; eauto. intro. subst. destruct chunk; simpl; eapply Z.divide_0_r.
  - intros. eapply inject_map_content; eauto.
Qed.

Lemma inject_mem_support : forall s2' j m1' m2 m2',
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_mem s2' j m1' m2 = m2' ->
    Mem.support m2' = s2'.
Proof.
  intros. rewrite <- H0.
  erewrite Mem.inject_mem_support; eauto.
Qed.

Lemma inject_map_perm_inv: forall s1' s2' j1' m1' m2' m2 b2 b1 delta ofs2 k p,
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
    sup_In b1 s1' -> sup_In b2 s2' ->
    j1' b1 = Some (b2, delta) ->
    Mem.perm m2' b2 ofs2 k p ->
    Mem.perm m1' b1 (ofs2 - delta) k p \/
    ~ Mem.perm m1' b1 (ofs2 - delta) Max Nonempty.
Proof.
  induction s1'; intros; simpl in *.
  - subst. inv H2.
  - destruct H2.
    + (* local a = b1, if copy left, else right. *)
      subst a. erewrite map_perm_2 in H5; eauto.
      rewrite Mem.inject_map_support in H5; auto.
      destruct (Mem.sup_dec b2 s2'); try congruence. simpl in H5.
      destruct (Mem.perm_dec m1' b1 (ofs2 - delta) Max Nonempty) eqn : Hb.
      -- left. auto.
      -- right. eauto.
    + destruct (j1' a) as [[a' delta']|] eqn: Hj1'a.
      -- destruct (eq_block a' b2).
         ++ (* the case where we need to use no_overlap to state the image of a and b1 diffs*)
            subst. erewrite map_perm_2 in H5; eauto.
            rewrite Mem.inject_map_support in H5; auto.
            destruct (Mem.sup_dec b2 s2'); try congruence. simpl in H5.
            destruct (Mem.perm_dec m1' a (ofs2 - delta') Max Nonempty) eqn : Hb. simpl in H5.
            * destruct (eq_block a b1) eqn: Hab1.
              replace delta' with delta in * by congruence.
              subst. left. auto.
              red in H0.
              destruct (Mem.perm_dec m1' b1 (ofs2 - delta) Max Nonempty).
              exploit H0; eauto. intros [A | B]. congruence. extlia.
              right. auto.
            * simpl in H5. eapply IHs1'; eauto.
         ++ eapply IHs1'; eauto. erewrite map_perm_3 in H5; eauto.
      -- eapply IHs1'; eauto. erewrite map_perm_1 in H5; eauto.
         intros (d & A). congruence.
Qed.

Lemma inject_mem_perm_inv: forall m1' m2 s2' j1' m2' ofs1 k p b2 b1 delta,
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    sup_In b1 (Mem.support m1') -> sup_In b2 s2' ->
    j1' b1 = Some (b2, delta) ->
    Mem.perm m2' b2 (ofs1 + delta) k p ->
    Mem.perm m1' b1 ofs1 k p \/
    ~ Mem.perm m1' b1 ofs1 Max Nonempty.
Proof.
  intros. set (ofs2 := ofs1 + delta).
  replace ofs1 with (ofs2 - delta) in * by lia.
  replace (ofs2 - delta + delta) with ofs2 in H5 by lia.
  eapply inject_map_perm_inv; eauto.
Qed.

Theorem inject_mem_inject1 : forall m1 m1' m2 m2' j1 j2 j1' j2' s2' m3',
    Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
    Mem.inject j1 m1 m2 ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    inject_incr j1 j1' ->
    inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2') ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    inject_incr_no_overlap' j1 j1' ->
    injp_max_perm_decrease m1 m1' ->
    inject_dom_in j1' (Mem.support m1') ->
    inject_image_in j1' s2' ->
    update_add_zero j1 j1' ->
    update_add_exists j1 j1' (compose_meminj j1' j2') ->
    Mem.inject j1' m1' m2'.
Proof.
  intros until m3'.
  intros UNMAP1 INJ12 INJ13' SUPINCL1 INJMEM INCR12 INCR13 INCRDISJ1
         INCRNOLAP1 MAXPERM1 DOMIN1 IMGIN1 ADDZERO1 ADDEXISTS1.
  assert (NOLAP : Mem.meminj_no_overlap j1' m1').
  eapply update_meminj_no_overlap1; eauto.
  constructor.
  - eapply inject_mem_inj1; eauto.
  - intros. destruct (j1' b) as [[b' o]|] eqn: Hj1; auto.
    apply DOMIN1 in Hj1. exfalso. eauto.
  - intros. red in IMGIN1. apply inject_mem_support in INJMEM. unfold Mem.valid_block. rewrite INJMEM. eauto.
    eauto.
  - eauto.
  - intros. destruct (j1 b) as [[b'' delta']|] eqn: Hj1b.
    + erewrite INCR12 in H; eauto. inv H.
      inversion INJ12. eapply mi_representable; eauto.
      destruct H0. left. apply MAXPERM1; eauto. eapply inject_implies_dom_in; eauto.
      right. apply MAXPERM1; eauto. eapply inject_implies_dom_in; eauto.
    + exploit ADDZERO1; eauto. intro. subst. split. lia.
      generalize (Ptrofs.unsigned_range_2 ofs). lia.
  - intros.
    eapply inject_mem_perm_inv; eauto.
Qed.
(*
Lemma inject_map_some_perm:
  forall s1' s2' j1' m1' m2 ofs delta p a b,
    Mem.perm m1' a (ofs - delta) Max p ->
    sup_In a s1' ->
    j1' a = Some (b, delta) ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.perm (Mem.inject_map s1' s2' j1' m1' m2) b ofs Max p.
Proof.
(*  induction s1'; intros; simpl; eauto.
  - *)
Admitted.

Theorem inject_map_max_perm : forall s1' m1' m2 m2' s2' j1',
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_map s1' s2' j1' m1' m2 = m2' ->
    Mem.meminj_no_overlap j1' m1' ->
(*    injp_max_perm_decrease m1 m1' -> *)
    injp_max_perm_decrease m2 m2'.
Proof.
  induction s1'; intros; simpl in *.
  - inv H0. unfold Mem.supext. destruct Mem.sup_include_dec.
    red. intros. unfold Mem.perm in *. eauto. congruence.
  - assert (injp_max_perm_decrease m2 (Mem.inject_map s1' s2' j1' m1' m2)).
    eapply IHs1'; eauto.
    eapply max_perm_decrease_trans. eauto.
    {
      red. intros.
      destruct (j1' a) as [[a' delta]|] eqn: Hj1'.
      - destruct (eq_block a' b).
        + red in H2.
          subst. erewrite map_perm_2 in H4; eauto. unfold Mem.valid_block in H3.
          rewrite Mem.inject_map_support in H3; auto.
          rewrite Mem.inject_map_support in H4; auto.
          destruct Mem.sup_dec; try congruence. simpl in H4.
          destruct Mem.perm_dec; simpl in H4.

          eapply inject_map_some_perm; eauto.
          auto.
        + erewrite map_perm_1 in H4; eauto. intros [d A]. congruence.
      - subst. erewrite map_perm_1 in H4; eauto.
        intros [d A]. congruence.
    }
    rewrite Mem.inject_map_support; auto.
Qed.
*)

Theorem inject_mem_max_perm : forall m1' m2 m2' s2' j1',
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    Mem.meminj_no_overlap j1' m1' ->
    injp_max_perm_decrease m2 m2'.
Proof.
Admitted.

(*  intros. red. intros b2 ofs2 p VALID PERM2.
  exploit inject_mem_perm_inv; eauto.
  intros (b1 & delta & ofs1 & INJ & PERM1 & OFS).
  destruct (j1 b1) as [[b2' delta']|] eqn : Hj1b1.
  + erewrite H2 in INJ; eauto. inv INJ.
    eapply Mem.perm_inject; eauto.
    eapply H4; eauto. eapply H; eauto.
  + exploit H3; eauto. intros [A B]. exfalso. eauto.
Qed. *)

Definition loc_in_reach (f:meminj) m b ofs k p: Prop :=
  exists b0 delta, f b0 = Some (b,delta) /\ Mem.perm m b0 (ofs - delta) k p.

Lemma out_of_reach_reverse: forall f m b ofs,
    loc_out_of_reach f m b ofs <-> ~ loc_in_reach f m b ofs Max Nonempty.
Proof.
  intros. split; intro.
  - intro. red in H. red in H0. destruct H0 as (b0 & delta & A & B).
    exploit H; eauto.
  - red. intros. intro.
    apply H. red. eauto.
Qed.

Lemma loc_in_reach_dec: forall s m f b ofs k p,
    inject_dom_in f s ->
    {loc_in_reach f m b ofs k p}+{~ loc_in_reach f m b ofs k p}.
Proof.
  induction s; intros.
  - right. intros (b0 & delta & A & B).
    apply H in A. inv A.
  - apply inject_dom_in_sub in H as H'.
    eapply (IHs m (meminj_sub f a) b ofs) in H'.
    destruct H'.
    + left. red. red in l. destruct l as (b0 & d & A & B).
      exists b0,d. split; auto. unfold meminj_sub in A.
      destruct eq_block; eauto. congruence. eauto.
    +
    destruct (f a) as [[a' delta]|] eqn : Hfa.
    * destruct (eq_block a' b).
      -- subst.
         destruct (Mem.perm_dec m a (ofs-delta) k p).
         left. exists a,delta. eauto.
         right.
         intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
      -- right. intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
    * right.  intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
Qed.
(*
Lemma loc_out_of_reach_incr: forall j1 j1' m1 m1' b2 ofs2,
    loc_out_of_reach j1 m1 b2 ofs2 ->
    inject_incr j1 j1' ->
    injp_max_perm_decrease m1 m1' -> 
    loc_out_of_reach j1' m1' b2 ofs2.
Proof.
  intros. red. red in H. red in H0. red in H1.
  intros. intro.
Admitted.
*)
(*
Lemma loc_in_reach_incr : forall j1 j1' m1 m1' b2 ofs2 Max p,
    loc_in_reach j1 m1 b2 ofs2 Max p ->
    loc_in_reach j1' m1' b2 ofs2 Max p.
Proof.
  intros until p. intros INREACH1.
  red. red in INREACH1.
  destruct INREACH1 as (b0 & d & A & B).
*)
Lemma loc_out_of_reach_trans:
  forall m1 m2 m3 j1 j2 b2 ofs2 b3 delta3 k p,
    Mem.inject j1 m1 m2 ->
    Mem.inject j2 m2 m3 ->
    j2 b2 = Some (b3,delta3) ->
    Mem.perm m2 b2 ofs2 k p ->
    loc_out_of_reach j1 m1 b2 ofs2 ->
    loc_out_of_reach (compose_meminj j1 j2) m1 b3 (ofs2 + delta3).
Proof.
  intros until p. intros INJ12 INJ23 MAP2 PERM2 OUTOFREACH1.
  red.
  red in OUTOFREACH1.
  intros. (* assert (INJNOLAP2: Mem.meminj_no_overlap j2' m2'). admit. (*need meminj_no_overlap2*) *)
  unfold compose_meminj in H.
  destruct (j1 b0) as [[b2' delta']|] eqn: Hj1b; try congruence.
  destruct (j2 b2') as [[b3' delta'']|] eqn: Hj2b; try congruence.
  inv H.
  destruct (Mem.perm_dec m1 b0 (ofs2 + delta3 - (delta' + delta'')) Max Nonempty); auto.
  destruct (eq_block b2 b2'). subst. rewrite MAP2 in Hj2b. inv Hj2b. apply OUTOFREACH1 in Hj1b.
  replace (ofs2 + delta'' - (delta' + delta'')) with (ofs2 - delta') in p0 by lia.
  congruence.
  eapply Mem.perm_inject in Hj1b; eauto.
  inversion INJ23. exploit mi_no_overlap. apply n. eauto. eauto.
  eauto with mem. eauto. intros [A|A]. congruence. extlia.
Qed.

Theorem inject_mem_inj2 : forall m1 m1' s2' m2' m3' j1' j2' m2 m3 j1 j2,
    (* injp_max_perm_decrease m2 m2' -> to proof*)
    injp_max_perm_decrease m1 m1' ->
    Mem.inject j1 m1 m2 ->
    Mem.inject j2 m2 m3 ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3' ->
    inject_incr j1 j1' ->
    inject_incr j2 j2' ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    Mem.meminj_no_overlap j1' m1' ->
    inject_dom_in j1' (Mem.support m1') ->
    inject_image_in j1' s2' ->
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    Mem.inject j1' m1' m2' ->
    update_add_same j2 j2' j1' ->
    Mem.mem_inj j2' m2' m3'.
Proof.
  intros until j2. intros MAXPERM1 INJ12 INJ23 OUTOFREACH3 INCR1 INCR2 INJ13'
                          INJNOLAP1 DOMIN1' IMGIN1' SUPINCL1 INJMEM INJ12' ADDSAME.
  constructor.
  - intros b2 b3 delta3 ofs2 k p MAP2 PERM2.
    destruct (j2 b2) as [[b3' delta3']|] eqn: Hj2b2.
    + apply inject_implies_dom_in in INJ12 as DOMIN1.
      destruct (loc_in_reach_dec (Mem.support m1) m1 j1 b2 ofs2 Max Nonempty DOMIN1).
      * (* b2 is in the reach of j1,*)
      admit.
      * assert (Mem.perm m2 b2 ofs2 k p). admit. (* update_add_out_of_reach *)
        erewrite INCR2 in MAP2; eauto. inversion MAP2. subst b3' delta3'. clear MAP2.
        inversion OUTOFREACH3. eapply unchanged_on_perm.
        apply out_of_reach_reverse in n.
        eapply loc_out_of_reach_trans; eauto.
        inversion INJ23. eauto.
        eapply Mem.perm_inject; eauto.
    + exploit ADDSAME; eauto.
      intros (b1 & A & B).
      inversion INJ13'. inversion mi_inj. eapply mi_perm.
      unfold compose_meminj. rewrite A,MAP2. reflexivity.
      admit. (* update_add_perm_inv *)
(*


    destruct (loc_in_reach_dec (Mem.support m1') m1' j1' b2 ofs2 Max Nonempty DOMIN1').
    +  destruct l as (b1 & delta2 & MAP1 & PERM1).
       exploit inject_mem_perm_inv ; eauto.
       replace (ofs2) with ((ofs2 - delta2) + delta2) in PERM2 by lia. eauto.
       intros [A | A].
       * clear PERM1.
         inversion INJ13'. inversion mi_inj. exploit mi_perm.
         2: apply A. unfold compose_meminj. rewrite MAP1, MAP2.
         reflexivity.
         replace (ofs2 - delta2 + (delta2 + delta3)) with (ofs2 + delta3) by lia. auto.
       * congruence.
    + apply out_of_reach_reverse in n.
      assert (Mem.perm m2 b2 ofs2 k p). admit. (*out_of_reach + inject_map*)
      simpl. destruct (j2 b2) as [[b3' delta3']|] eqn: Hj2b2.
      erewrite INCR2 in MAP2; eauto. inversion MAP2. subst b3' delta3'. clear MAP2.
      * inversion OUTOFREACH3. eapply unchanged_on_perm.
        red. eapply loc_out_of_reach_incr in n; eauto.
        red in n.
        -- intros. (* assert (INJNOLAP2: Mem.meminj_no_overlap j2' m2'). admit. (*need meminj_no_overlap2*) *)
           unfold compose_meminj in H0.
           destruct (j1 b0) as [[b2' delta']|] eqn: Hj1b; try congruence.
           destruct (j2 b2') as [[b3' delta'']|] eqn: Hj2b; try congruence.
           inv H0.
           destruct (Mem.perm_dec m1 b0 (ofs2 + delta3 - (delta' + delta'')) Max Nonempty); auto.
           destruct (eq_block b2 b2'). subst. rewrite Hj2b2 in Hj2b. inv Hj2b. subst. apply n in Hj1b.
           replace (ofs2 + delta'' - (delta' + delta'')) with (ofs2 - delta') in p0 by lia.
           congruence.
           eapply Mem.perm_inject in Hj1b; eauto.
           inversion INJ23. exploit mi_no_overlap. apply n0. eauto. eauto.
           eauto with mem. eauto. intros [A|A]. congruence. extlia.
        -- inversion INJ23. eauto.
        -- eapply Mem.perm_inject; eauto.
      * exploit ADDSAME; eauto.
        intros (b1 & A & B).
        apply n in A. (*out_of_reach + inject_map + not in m2*)
        (*PERM2 is wrong*) admit.
*)
  - admit.
  - admit.
Admitted.
(*  -  intros. destruct (j2 b1) as [[b2' delta']|] eqn: Hj2b1.
    + erewrite INCR2 in H; eauto. inv H. inversion INJ23. inversion mi_inj.
      eapply mi_align; eauto. apply inject_implies_dom_in in INJ23 as DOMIN23.
      red. intros. red in H0. eapply MAXPERM2. eapply DOMIN23; eauto. eapply H0; eauto.
    + exploit ADDSAME; eauto. intros (b0 & MAP1 & INJECTIVE).
      inv INJ13'. inv mi_inj. eapply mi_align; eauto.
      unfold compose_meminj. rewrite MAP1. rewrite H. reflexivity.
      red. intros. red in H0. exploit H0. apply H1. intro.
      exploit inject_mem_perm_inv; eauto.
      intros (b1' & delta0 & ofs1 & MAP1' & PERM1 & OFS).
      apply INJECTIVE in MAP1' as eq. subst. rewrite MAP1 in MAP1'. inv MAP1'.
      replace (ofs1 + 0) with ofs1 by lia. eauto.
  - intros.
    admit. (* need another lemma like inject_mem_content_inv*)
Admitted.
*)
Theorem inject_mem_inject2: forall m1 m1' s2' m2' m3' j1' j2' j1 j2 m2 m3,
    injp_max_perm_decrease m1 m1' ->
    Mem.inject j1 m1 m2 ->
(*    injp_max_perm_decrease m2 m2' -> *)
    Mem.inject j2 m2 m3 ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3' ->
    inject_incr j1 j1' ->
    inject_incr j2 j2' ->
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.sup_include (Mem.support m3) (Mem.support m3') ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    inject_dom_in j1' (Mem.support m1') ->
    inject_image_in j1' s2' ->
    inject_dom_in j2' s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    Mem.inject j1' m1' m2' ->
    update_add_same j2 j2' j1' ->
    Mem.inject j2' m2' m3'.
Proof.
  intros until m3. intros MAXPERM1 INJ12 INJ23 OUROFREACH3 INCR1 INCR2 SUPINCR2 SUPINCR3 
                          INJ13' DOMIN1 IMGIN1 DOMIN2 INJNOLAP1 INJMEM INJ12' ADDSAME.
  generalize (Mem.inject_mem_support s2' j1' m1'). intro SUP.
  constructor.
  - eapply inject_mem_inj2; eauto.
  - intros. destruct (j2' b) as [[b' d]|] eqn:?.
    eapply DOMIN2 in Heqo. subst. unfold Mem.valid_block in H. rewrite SUP in H. congruence.
    eauto. auto.
  - intros. destruct (j2 b) as [[b'' delta']|] eqn : Hj2.
    + erewrite INCR2 in H; eauto. inv H. inv INJ23. apply mi_mappedblocks in Hj2.
      unfold Mem.valid_block. eauto.
    + exploit ADDSAME; eauto. intros (b1 & MAP1 & INJECTIVE).
      inv INJ13'. eapply mi_mappedblocks. unfold compose_meminj. rewrite MAP1. rewrite H.
      reflexivity.
  - admit.
  - admit.
  - admit.
(*
    red. intros b2 b3 delta2 b2' b3' delta2' ofs2 ofs2' NEQ MAP2 MAP2' PERM2 PERM2'.
    inversion INJ13'. (* assert (b1 <> b1'). intro. subst. congruence. *)
    exploit mi_no_overlap; eauto.
    unfold compose_meminj. rewrite MAP1,  MAP2. reflexivity.
    unfold compose_meminj. rewrite MAP1',  MAP2'. reflexivity.
    intros [|]. eauto. lia.
 
  - intros. destruct (j2 b) as [[b'' delta']|] eqn : Hj2.
    + erewrite INCR2 in H; eauto. inv H. inversion INJ23. eapply mi_representable; eauto.
      destruct H0. left. apply MAXPERM2; eauto. eapply inject_implies_dom_in; eauto.
      right. apply MAXPERM2; eauto. eapply inject_implies_dom_in; eauto.
    + exploit ADDSAME; eauto. intros (b1 & MAP1 & INJECTIVE).
      inversion INJ13'. eapply mi_representable. unfold compose_meminj. rewrite MAP1. rewrite H.
      reflexivity.
      destruct H0.
      -- left.
      exploit inject_mem_perm_inv; eauto.
      intros (b1' & delta0 & ofs1 & MAP1' & PERM1 & OFS).
      apply INJECTIVE in MAP1' as eq. subst. rewrite MAP1 in MAP1'. inv MAP1'. rewrite OFS.
      replace (ofs1 + 0) with ofs1 by lia. eauto.
      -- right.
      exploit inject_mem_perm_inv; eauto.
      intros (b1' & delta0 & ofs1 & MAP1' & PERM1 & OFS).
      apply INJECTIVE in MAP1' as eq. subst. rewrite MAP1 in MAP1'. inv MAP1'. rewrite OFS.
      replace (ofs1 + 0) with ofs1 by lia. eauto.

  - intros. (* if b2 is in the reach of j2 and j2', but out of reach of j and j'???*)
    admit.
    (* *) *)
Admitted.

Theorem inject_map_inject: forall m1 m2 m3 m1' m2' m3' s2' j1 j2 j1' j2',
    Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3' ->
    Mem.inject j1 m1 m2 -> Mem.inject j2 m2 m3 ->
    Mem.inject (compose_meminj j1' j2') m1' m3' ->
    inject_dom_in j1' (Mem.support m1') ->
    inject_image_in j1' s2' ->
    inject_dom_in j2' s2' ->
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.sup_include (Mem.support m3) (Mem.support m3') ->
    Mem.inject_mem s2' j1' m1' m2 = m2' ->
    injp_max_perm_decrease m1 m1' ->
    inject_incr j1 j1' -> inject_incr j2 j2' ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    inject_incr_no_overlap' j1 j1' ->
    update_add_zero j1 j1' ->
    update_add_exists j1 j1' (compose_meminj j1' j2') ->
    update_add_same j2 j2' j1' ->
    Mem.inject j1' m1' m2'
    /\ Mem.inject j2' m2' m3'
    /\ injp_max_perm_decrease m2 m2'
    /\ Mem.sup_include s2' (Mem.support m2').
Proof.
  intros until j2'. intros UNMAP1 OUTOFREACH3 INJ12 INJ23 INJ13' DOMIN1 IMGIN1' DOMIN2' SUPINCR2 SUPINCR3 INJMEM
  MAXPERM1 INCR1 INCR2 INCRDISJ1 INCRNOLAP1 ADDZERO ADDEXISTS ADDSAME.
  exploit inject_mem_inject1; eauto.
  eapply compose_meminj_incr; eauto.
  intros INJ12'.
  assert (INJNOLAP1 : Mem.meminj_no_overlap j1' m1').
  inversion INJ12'. eauto.
  assert (MAXPERM2 : injp_max_perm_decrease m2 m2').
  eapply inject_mem_max_perm; eauto.
  (* eapply inject_implies_dom_in. apply INJ12. all: eauto. *)
  exploit inject_mem_inject2. apply MAXPERM1. all: eauto.
  intros INJ23'.
  repeat apply conj; auto.
  rewrite <- INJMEM. erewrite Mem.inject_mem_support; eauto.
Qed.


Lemma inject_compose_inv:
  forall (j1 j1' j2 j2' : meminj) (m1 m2 m3 m1' m3': mem) s2',
  Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
  Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3' ->
  Mem.inject j1 m1 m2 ->
  Mem.inject j2 m2 m3 ->
  inject_incr j1 j1' -> inject_incr j2 j2' ->
  inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
  inject_incr_no_overlap' j1 j1' ->
  injp_max_perm_decrease m1 m1' ->
  Mem.inject (compose_meminj j1' j2') m1' m3' ->
  inject_dom_in j1' (Mem.support m1') ->
  inject_image_in j1' s2' ->
  inject_dom_in j2' s2' ->
  Mem.sup_include (Mem.support m2) s2' ->
  Mem.sup_include (Mem.support m3) (Mem.support m3') ->
  update_add_zero j1 j1' ->
  update_add_exists j1 j1' (compose_meminj j1' j2') ->
  update_add_same j2 j2' j1' ->
  exists m2' , Mem.inject j1' m1' m2' /\
         Mem.inject j2' m2' m3' /\
         injp_max_perm_decrease m2 m2' /\
         Mem.sup_include s2' (Mem.support m2').
Proof.
  intros.
  exists (Mem.inject_mem s2' j1' m1' m2).
  eapply inject_map_inject; eauto.
Qed.

Lemma out_of_reach_trans: forall j12 j23 m1 m2 m3 m3',
    Mem.inject j12 m1 m2 ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3' ->
    Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
Proof.
  intros.
  inv H0. constructor; auto.
  - intros. eapply unchanged_on_perm.
  red in H. red.
  intros b1 delta23 MAP13. unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto. auto.
  - intros. eapply unchanged_on_contents.
  red in H. red.
  intros b1 delta23 MAP13. unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto. auto.
Qed.
(*
Lemma memory_overwrite_out_of_closure: forall m1 m2 m3 m1' m2' m3' j12 j23 j12' j23',
    Mem.inject j12 m1 m2 ->
    Mem.inject j23 m2 m3 ->
    Mem.inject j12' m1' m2' ->
    Mem.inject j23' m2' m3' ->
    inject_incr j12 j12' -> inject_incr j23 j23' ->
    injp_max_perm_decrease m2 m2' ->
    Mem.unchanged_on (loc_unmapped (compose_meminj j12 j23)) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3' ->
    exists m2'', Mem.inject j12' m1' m2''
            /\ Mem.inject j23' m2'' m3'
            /\ injp_max_perm_decrease m2 m2''
            /\ Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2''
            /\ Mem.unchanged_on (loc_unmapped j23) m2 m2''.
Admitted.
*)
(** injp @ injp is refined by injp *)
Lemma injp_injp2:
  subcklr (injp @ injp) injp.
Proof.
  red.
  intros w se1 se3 m1 m3 MSTBL13 MMEM13. destruct w as [w12 w23].
  destruct MMEM13 as [m2 [MMEM12 MMEM23]].
  simpl in *.
  inv MMEM12. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  exists (injpw (compose_meminj j12 j23)
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23)).
  simpl.
  repeat apply conj.
  - inv MSTBL13. inv H. inv H0. inv H1.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - constructor.
  - apply inject_incr_refl.
  - intros w13' m1' m3' MMEM13' INCR13'.
    unfold rel_compose.
    clear MSTBL13.
    cbn in INCR13'.
    inv MMEM13'. rename f into j13'. rename Hm3 into INJ13'.
    cbn.
    inversion INCR13' as [? ? ? ? ? ? ? ? MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst.
    generalize (inject_compose_inv _ _ _ _ _ _ _ _ _ _ UNCHANGE1 UNCHANGE3 INJ12 INJ23 INCR12 INCR23 INCRDISJ12 INCRNOLAP MAXPERM1 INJ13' DOMIN12' IMGIN12' DOMIN23' SUPINCL2 SUPINCL3 ADDZERO ADDEXISTS ADDSAME).
    intros (m2' & INJ12' & INJ23' & MAXPERM2 & SUPINCL2').
    exists ((injpw j12' m1' m2' INJ12'), (injpw j23' m2' m3' INJ23')).
    cbn.
    repeat apply conj; cbn.
    + exists m2'.
      repeat apply conj; constructor; auto.
    + constructor; auto.
      inversion UNCHANGE1.
      constructor; auto.
      intros. eapply unchanged_on_perm; eauto. red.
      red in H. unfold compose_meminj. rewrite H. auto.
      intros. eapply unchanged_on_contents; eauto.
      red in H. red. unfold compose_meminj. rewrite H. auto.
      admit.
    + constructor; auto.
      admit.
      eapply out_of_reach_trans; eauto.
    + apply inject_incr_refl.
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
