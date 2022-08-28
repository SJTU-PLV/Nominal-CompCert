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

(** * Construction of meminj j1' j2' *)

(** meminj operations *)
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

Definition update_add_same2 (j23 j23' : meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    forall b2' ofs2',
      j23' b2' = Some (b3,ofs2') -> b2 = b2'.

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
(*    /\ update_add_same2 j2 j2' . *)
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
            disjoint1 & disjoint2 & no_overlap & add_exists & add_zero & add_same1).
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
      red. red in add_same1. intros. destruct (eq_block b2 (fresh_block s2)).
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
      - eapply add_same1; eauto. rewrite meminj_add_diff; eauto.
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

Lemma map_perm_1 : forall j1' j2 b1 s2 m1 m2 m2' b2 ofs2 k p,
        Mem.map j1' j2 b1 s2 m1 m2 = m2' ->
        (~ exists delta, j1' b1 = Some (b2, delta)) ->
        Mem.perm m2' b2 ofs2 k p <->
        Mem.perm m2 b2 ofs2 k p.
Proof.
  intros. unfold Mem.map in H.
  destruct (j1' b1) as [[b1' delta']|] eqn :Hfb.
  - destruct (eq_block b1' b2).
    + subst. exfalso. apply H0. eauto.
    + destruct (Mem.valid_position_dec) in H.
      inv H. unfold Mem.perm in *. simpl in *.
      erewrite <- pmap_update_diff; eauto.
      reflexivity.
      subst. reflexivity.
  - subst. reflexivity.
Qed.

Lemma map_perm_2 : forall j1' j2 b1 s2 m1 m2 m2' b2 delta ofs2 k p,
    Mem.map j1' j2 b1 s2 m1 m2 = m2' ->
    j1' b1 = Some (b2, delta) ->
    Mem.perm m2' b2 ofs2 k p <->
    if (Mem.valid_position_dec b2 j2 s2 (Mem.support m2) && (Mem.perm_dec m1 b1 (ofs2 - delta) Max Nonempty))
      then Mem.perm m1 b1 (ofs2 - delta) k p
    else Mem.perm m2 b2 ofs2 k p.
Proof.
  intros.
  unfold Mem.map in H. rewrite H0 in H.
  destruct Mem.valid_position_dec.
  -
  inv H. unfold Mem.perm. simpl. unfold Mem.pmap_update. rewrite NMap.gsspec.
  rewrite pred_dec_true; eauto.
  destruct (Mem.perm_dec m1 b1 (ofs2 - delta) Max Nonempty); simpl.
    + rewrite Mem.update_mem_access_result.
      unfold Mem.perm in p0.
      unfold Mem.perm_check_any.
      destruct (Maps.ZMap.get) eqn: Hperm.
      reflexivity. exfalso. apply p0.
    + rewrite Mem.update_mem_access_result.
      unfold Mem.perm in n. unfold Mem.perm_check_any.
      destruct (Maps.ZMap.get) eqn: Hperm.
      exfalso. apply n. simpl. constructor.
      reflexivity.
  - simpl. subst. reflexivity.
Qed.

Lemma map_perm_3 :  forall j1' j2 b1 s2 m1 m2 m2' b2 b2' delta ofs2 k p,
        Mem.map j1' j2 b1 s2 m1 m2 = m2' ->
        j1' b1 = Some (b2,delta) ->
        b2 <> b2' ->
        Mem.perm m2' b2' ofs2 k p <->
        Mem.perm m2 b2' ofs2 k p.
Proof.
  intros. eapply map_perm_1; eauto.
  intros [d A]. congruence.
Qed.

Definition mem_memval (m:mem) b ofs : memval :=
  Maps.ZMap.get ofs (NMap.get _ b (Mem.mem_contents m)).

Lemma to_mem_memval : forall m b ofs,
    Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b (Mem.mem_contents m)) = mem_memval m b ofs.
Proof. intros. reflexivity. Qed.

Lemma map_content_1 : forall j1' j2 b1 s2 m1 m2 m2' b2 ofs2,
    Mem.map j1' j2 b1 s2 m1 m2 = m2' ->
    (~exists delta, j1' b1 = Some (b2,delta)) ->
    mem_memval m2' b2 ofs2 = mem_memval m2 b2 ofs2.
Proof.
  intros. unfold Mem.map in H.
  destruct (j1' b1) as [[b1' delta']|] eqn :Hfb.
  - destruct (eq_block b1' b2).
    + subst. exfalso. apply H0. eauto.
    + destruct Mem.valid_position_dec.
      inv H. unfold mem_memval in *. simpl in *.
      erewrite <- pmap_update_diff; eauto;
      reflexivity.
      subst. reflexivity.
  - subst. reflexivity.
Qed.

Lemma map_content_2 : forall j1' j2 b1 m1 s2 m2 m2' b2 delta ofs2 ,
    Mem.map j1' j2 b1 s2 m1 m2 = m2' ->
    j1' b1 = Some (b2,delta) ->
    mem_memval m2' b2 ofs2 =
    if (Mem.valid_position_dec b2 j2 s2 (Mem.support m2) && Mem.perm_dec m1 b1 (ofs2 - delta) Cur Readable)
    then Mem.memval_map j1' (mem_memval m1 b1 (ofs2 - delta)) else mem_memval m2 b2 ofs2.
Proof.
  intros.
  unfold Mem.map in H. rewrite H0 in H.
  destruct Mem.valid_position_dec.
  -
  inv H. unfold mem_memval. simpl. unfold Mem.pmap_update. rewrite NMap.gsspec.
  rewrite pred_dec_true; eauto.
  destruct (Mem.perm_dec m1 b1 (ofs2 - delta) Cur Readable); simpl.
  +
    set (map2 := (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m2))) in *.
    set (map1 := (NMap.get (Maps.ZMap.t memval) b1 (Mem.mem_contents m1))) in *.
    unfold Mem.perm in p.
    set (pmap1 := (NMap.get (Maps.ZMap.t Mem.memperm) b1 (Mem.mem_access m1))) in *.
    assert (CHECK: Mem.perm_check_readable pmap1 (ofs2 - delta) = true).
    unfold Mem.perm_check_readable.
    destruct (Maps.ZMap.get); inv p; auto.
    erewrite Mem.update_mem_content_result; eauto.
    rewrite CHECK. reflexivity.
  +
    set (map2 := (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m2))) in *.
    set (map1 := (NMap.get (Maps.ZMap.t memval) b1 (Mem.mem_contents m1))) in *.
    unfold Mem.perm in n.
    set (pmap1 := (NMap.get (Maps.ZMap.t Mem.memperm) b1 (Mem.mem_access m1))) in *.
    assert (CHECK: Mem.perm_check_readable pmap1 (ofs2 - delta) = false).
    {unfold Mem.perm_check_readable.
    destruct (Maps.ZMap.get); auto.
    destruct p.
    exfalso. apply n. constructor.
    exfalso. apply n. constructor.
    exfalso. apply n. constructor.
    auto.
    }
    erewrite Mem.update_mem_content_result; eauto.
    rewrite CHECK. reflexivity.
  - simpl. subst. reflexivity.
Qed.

Lemma out_of_reach_free_support :forall m1 m1' j1 j2 j1' H1 H2 b m2 m2',
    Mem.out_of_reach_free m1 m1' j1 j2 j1' b H1 H2 m2 = m2' ->
    Mem.support m2' = Mem.support m2.
Proof.
  intros. unfold Mem.out_of_reach_free in H. inv H.
  auto.
Qed.

Lemma initial_m2'_support : forall s2 s2' m1 m1' j1 j1' j2 H1 H2 m2 m2',
    Mem.sup_include (Mem.support m2) s2' ->
    Mem.initial_m2' m1 m1' j1 j1' j2 H1 H2 s2 s2' m2 = m2' ->
    Mem.support m2' = s2'.
Proof.
  induction s2; intros.
  - inv H0. unfold Mem.initial_m2'. simpl.
    unfold Mem.supext. destruct Mem.sup_include_dec.
    auto. congruence.
  - unfold Mem.initial_m2' in *. simpl in *.
    assert (Mem.support (Mem.initial_free m1 m1' j1 j1' j2 H1 H2 s2 (Mem.supext s2' m2)) = s2').
    eapply IHs2; eauto.
    apply out_of_reach_free_support in H0.
    congruence.
Qed.

Definition loc_sup_in_unmapped (j2:meminj) (s2:sup) : block -> Z -> Prop :=
  fun b _ => Mem.sup_In b s2 /\ j2 b = None.

Lemma map_unmapped: forall j1' j2 b s2 m1' m2'1 m2',
    Mem.map j1' j2 b s2 m1' m2'1 = m2' ->
    Mem.unchanged_on ( loc_sup_in_unmapped j2 s2  ) m2'1 m2'.
Proof.
  intros. unfold Mem.map in H.
  destruct (j1' b) as [[b' d']|] eqn: Hj1'b.
  destruct Mem.valid_position_dec in H.
  - inv H.
    constructor.
    + eauto.
    + intros.
      unfold Mem.pmap_update. unfold Mem.perm. simpl.
      rewrite NMap.gsspec.
      destruct (NMap.elt_eq b0 b').
      * subst.
        exfalso.
        red in v. red in H. firstorder.
      * reflexivity.
    + intros.
      unfold Mem.pmap_update. unfold Mem.perm. simpl.
      rewrite NMap.gsspec.
      destruct (NMap.elt_eq b0 b').
      * subst.
        exfalso.
        red in v. red in H. firstorder.
      * reflexivity.
  - inv H. eauto with mem.
  - inv H. eauto with mem.
Qed.

Lemma inject_map_unmapped:
  forall s1' s2 j1' j2 m1' m2'1 m2',
    Mem.inject_map s1' s2 j1' j2 m1' m2'1 = m2' ->
    Mem.unchanged_on (loc_sup_in_unmapped j2 s2 ) m2'1 m2'.
Proof.
  induction s1'; intros; inv H; simpl in *.
  - eapply Mem.unchanged_on_refl.
  - eapply Mem.unchanged_on_trans; eauto.
    eapply map_unmapped; eauto.
Qed.

Lemma map_out_of_reach: forall j1' j2 b s2 m1' m2'1 m2',
    Mem.map j1' j2 b s2 m1' m2'1 = m2' ->
    Mem.unchanged_on (loc_out_of_reach j1' m1') m2'1 m2'.
Proof.
  intros.
  constructor.
  - inv H. rewrite Mem.support_map. eauto.
  - intros.
    destruct (j1' b) as [[b' d']|] eqn: Hj1'b.
    destruct (eq_block b0 b').
    + subst b'.
      erewrite map_perm_2 with (m2' := m2'); eauto.
      destruct (Mem.perm_dec m1' b (ofs -d') Max Nonempty).
      red in H0. apply H0 in Hj1'b. congruence.
      destruct Mem.valid_position_dec; simpl; reflexivity.
    + erewrite map_perm_3 with (m2' := m2'); eauto. reflexivity.
    + erewrite map_perm_1 with (m2' := m2'); eauto. reflexivity.
      intros [A B]. congruence.
  - intros.
    repeat rewrite to_mem_memval.
    destruct (j1' b) as [[b' d']|] eqn: Hj1'b.
    destruct (eq_block b0 b').
    + subst b'.
      erewrite map_content_2 with (m2' := m2'); eauto.
      destruct (Mem.perm_dec m1' b (ofs -d') Cur Readable).
      red in H0. apply H0 in Hj1'b. exfalso. apply Hj1'b. eauto with mem.
      destruct Mem.valid_position_dec; simpl; reflexivity.
    + erewrite map_content_1 with (m2' := m2'); eauto.
      intros [A B]. congruence.
    + erewrite map_content_1 with (m2' := m2'); eauto.
      intros [A B]. congruence.
Qed.

Lemma inject_map_out_of_reach:
  forall s1' s2' j1' j2 m1' m2'1 m2',
    Mem.inject_map s1' s2' j1' j2 m1' m2'1 = m2' ->
    Mem.unchanged_on (loc_out_of_reach j1' m1') m2'1 m2'.
Proof.
  induction s1'; intros; inv H; simpl in *.
  - eapply Mem.unchanged_on_refl.
  - eapply Mem.unchanged_on_trans; eauto.
    eapply map_out_of_reach; eauto.
Qed.

Lemma inject_mem_out_of_reach:
  forall s2' j1' j2 m1' m2'1 m2',
    Mem.inject_mem s2' j1' j2 m1' m2'1 = m2' ->
    Mem.unchanged_on (loc_out_of_reach j1' m1') m2'1 m2'.
Proof.
  intros.
  eapply inject_map_out_of_reach; eauto.
Qed.

Lemma supext_unchanged_on : forall s m m' P,
    Mem.supext s m = m' ->
    Mem.unchanged_on P m m'.
Proof.
  intros. unfold Mem.supext in H.
  destruct Mem.sup_include_dec in H.
  - constructor; inv H.
    + eauto.
    + intros. reflexivity.
    + intros. reflexivity.
  - subst. eauto with mem.
Qed.

Lemma out_of_reach_free_unchanged_on_2: forall m1 m1' j1 j1' j2 b H1 H2 m2 m2',
    Mem.out_of_reach_free m1 m1' j1 j1' j2 b H1 H2 m2 = m2' ->
    Mem.unchanged_on (loc_unmapped j2) m2 m2'.
Proof.
  intros. unfold Mem.out_of_reach_free in H.
  constructor.
  - inv H. eauto.
  - inv H. intros. unfold Mem.perm. simpl.
    unfold Mem.pmap_update. rewrite NMap.gsspec.
    destruct NMap.elt_eq.
    + subst.
      rewrite Mem.update_mem_access_free_result. red in H.
      rewrite H. reflexivity.
      apply Mem.access_default.
    + reflexivity.
  - inv H. intros. reflexivity.
Qed.

Lemma initial_free_unmapped: forall s2 m1 m1' j1 j1' j2 H1 H2 m2 m2',
    Mem.initial_free m1 m1' j1 j1' j2 H1 H2 s2 m2 = m2' ->
    Mem.unchanged_on (loc_unmapped j2) m2 m2'.
Proof.
  induction s2; intros; inv H; simpl in *.
  - eapply Mem.unchanged_on_refl.
  - eapply Mem.unchanged_on_trans; eauto.
    eapply out_of_reach_free_unchanged_on_2; eauto.
Qed.
Lemma initial_unmapped:
  forall m2 m2'1 s2' m1 m1' j1 j2 j1' DOMIN1 DOMIN2,
    Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN2 (Mem.support m2) s2' m2 = m2'1  ->
    Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
Proof.
  intros. unfold Mem.initial_m2' in H.
  eapply Mem.unchanged_on_trans.
  eapply supext_unchanged_on; eauto.
  eapply initial_free_unmapped; eauto.
Qed.

Lemma out_of_reach_free_unchanged_on_1: forall m1 m1' j1 j1' j2 b H1 H2 m2 m2',
    Mem.out_of_reach_free m1 m1' j1 j1' j2 H1 H2 b m2 = m2' ->
    Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
Proof.
  intros. unfold Mem.out_of_reach_free in H.
  constructor.
  - inv H. eauto.
  - inv H. intros. unfold Mem.perm. simpl.
    unfold Mem.pmap_update. rewrite NMap.gsspec.
    destruct NMap.elt_eq.
    + subst.
      rewrite Mem.update_mem_access_free_result.
      destruct (j2 b); try reflexivity.
      destruct (Mem.loc_in_reach_dec (Mem.support m1) m1 j1 b ofs Max Nonempty H1);
      destruct (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b ofs Max Nonempty H2);
      simpl; try reflexivity.
      apply Mem.out_of_reach_reverse in l; eauto. inv l.
      apply Mem.access_default.
    + reflexivity.
  - inv H. intros. reflexivity.
Qed.

Lemma initial_free_out_of_reach1: forall s2 m1 m1' j1 j2 j1' H1 H2 m2 m2',
    Mem.initial_free m1 m1' j1 j2 j1' H1 H2 s2 m2 = m2' ->
    Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
Proof.
  induction s2; intros; inv H; simpl in *.
  - eapply Mem.unchanged_on_refl.
  - eapply Mem.unchanged_on_trans; eauto.
    eapply out_of_reach_free_unchanged_on_1; eauto.
Qed.
Lemma initial_out_of_reach1:
  forall m2 m2'1 s2' m1 m1' j1 j2 j1' DOMIN1 DOMIN2,
    Mem.initial_m2' m1 m1' j1 j2 j1' DOMIN1 DOMIN2 (Mem.support m2) s2' m2 = m2'1  ->
    Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'1.
Proof.
  intros. unfold Mem.initial_m2' in H.
  eapply Mem.unchanged_on_trans.
  eapply supext_unchanged_on; eauto.
  eapply initial_free_out_of_reach1; eauto.
Qed.

Lemma out_of_reach_free_decrease: forall m1 m1' j1 j1' j2 b H1 H2 m2 m2' b2 ofs k p,
      Mem.out_of_reach_free m1 m1' j1 j1' j2 H1 H2 b m2 = m2' ->
      Mem.perm m2' b2 ofs k p -> Mem.perm m2 b2 ofs k p.
Proof.
  intros. unfold Mem.out_of_reach_free in H. inv H.
  unfold Mem.perm in *. simpl in *.
  unfold Mem.pmap_update in H0. rewrite NMap.gsspec in H0.
  destruct (NMap.elt_eq b2 b); eauto.
  subst. rewrite Mem.update_mem_access_free_result in H0.
  destruct (j2 b); eauto.
  destruct (Mem.loc_in_reach_dec (Mem.support m1) m1 j1 b ofs Max Nonempty H1 &&
           negb (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b ofs Max Nonempty H2)).
  inv H0. eauto.
  apply Mem.access_default.
Qed.

Lemma initial_free_decrease: forall s2 m1 m1' j1 j1' j2 H1 H2 m2 m2' b2 ofs k p,
    Mem.initial_free m1 m1' j1 j1' j2 H1 H2 s2 m2 = m2' ->
    Mem.perm m2' b2 ofs k p -> Mem.perm m2 b2 ofs k p.
Proof.
  induction s2; intros; simpl in H.
  - subst. eauto.
  - assert (Mem.perm (Mem.initial_free m1 m1' j1 j1' j2 H1 H2 s2 m2) b2 ofs k p).
    eapply out_of_reach_free_decrease; eauto.
    eauto.
Qed.

Lemma initial_perm_decrease: forall m2 m2'1 s2' m1 m1' j1 j1' j2 DOMIN1 DOMIN2 b2 ofs k p,
    Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN2 (Mem.support m2) s2' m2 = m2'1  ->
    Mem.perm m2'1 b2 ofs k p -> Mem.perm m2 b2 ofs k p.
Proof.
  intros.
  unfold Mem.initial_m2' in H.
  assert (Mem.perm (Mem.supext s2' m2) b2 ofs k p).
  eapply initial_free_decrease; eauto.
  unfold Mem.supext in H1. destruct Mem.sup_include_dec in H1.
  subst. unfold Mem.perm in *; simpl in *; eauto.
  auto.
Qed.

Lemma initial_max_perm_decrease: forall m2 m2'1 s2' m1 m1' j1 j1' j2 DOMIN1 DOMIN2,
    Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN2 (Mem.support m2) s2' m2 = m2'1  ->
    injp_max_perm_decrease m2 m2'1.
Proof.
  intros. red. intros.
  eapply initial_perm_decrease; eauto.
Qed.

Lemma initial_free_valid:
  forall s2 s2' m1 m1' j1 j1' j2 DOMIN1 DOMIN1' m2 m2'1 b2 ofs2 b3 delta3,
    Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN1' s2 s2' m2 = m2'1 ->
    j2 b2 = Some (b3,delta3) ->
    Mem.loc_in_reach j1 m1 b2 ofs2 Max Nonempty ->
    ~ Mem.loc_in_reach j1' m1' b2 ofs2 Max Nonempty ->
    sup_In b2 s2 ->
    ~ Mem.perm m2'1 b2 ofs2 Max Nonempty.
Proof.
  induction s2; intros.
  - inv H3.
  - destruct H3.
    + subst. unfold Mem.initial_m2'. simpl.
      unfold Mem.out_of_reach_free. unfold Mem.perm. simpl.
      unfold Mem.pmap_update. rewrite NMap.gsspec. rewrite pred_dec_true; auto.
      rewrite Mem.update_mem_access_free_result. rewrite H0.
      destruct (Mem.loc_in_reach_dec); try congruence.
      destruct (Mem.loc_in_reach_dec); try congruence.
      simpl. congruence.
      apply Mem.access_default.
    + subst. unfold Mem.initial_m2'. simpl.
      assert (~Mem.perm (Mem.initial_free m1 m1' j1 j1' j2 DOMIN1 DOMIN1' s2 (Mem.supext s2' m2)) b2 ofs2 Max Nonempty).
      eapply IHs2; eauto.
      unfold Mem.initial_m2'. reflexivity.
      intro. apply H.
      eapply out_of_reach_free_decrease; eauto.
Qed.

Lemma inject_map_perm_inv: forall s1' s2 s2' j1' j2 m1' m2' m2 b2 b1 delta ofs2 k p,
    Mem.support m2 = s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.inject_map s1' s2 j1' j2 m1' m2 = m2' ->
    sup_In b1 s1' -> sup_In b2 s2' ->
    j1' b1 = Some (b2, delta) ->
    Mem.valid_position b2 j2 s2 s2' ->
    Mem.perm m2' b2 ofs2 k p ->
    Mem.perm m1' b1 (ofs2 - delta) k p \/
    ~ Mem.perm m1' b1 (ofs2 - delta) Max Nonempty.
Proof.
  induction s1'; intros; simpl in *.
  - subst. inv H2.
  - destruct H2.
    + (* local a = b1, if copy left, else right. *)
      subst a. erewrite map_perm_2 in H6; eauto.
      rewrite Mem.inject_map_support in H6; auto. subst.
      destruct (Mem.valid_position_dec); try congruence; simpl in H6.
      destruct (Mem.perm_dec m1' b1 (ofs2 - delta) Max Nonempty) eqn : Hb.
      -- left. auto.
      -- right. eauto.
    + destruct (j1' a) as [[a' delta']|] eqn: Hj1'a.
      -- destruct (eq_block a' b2).
         ++ (* the case where we need to use no_overlap to state the image of a and b1 diffs*)
            subst. erewrite map_perm_2 in H6; eauto.
            rewrite Mem.inject_map_support in H6; auto.
            destruct (Mem.valid_position_dec); try congruence; simpl in H6.
            destruct (Mem.perm_dec m1' a (ofs2 - delta') Max Nonempty) eqn : Hb. simpl in H6.
            * destruct (eq_block a b1) eqn: Hab1.
              replace delta' with delta in * by congruence.
              subst. left. auto.
              red in H0.
              destruct (Mem.perm_dec m1' b1 (ofs2 - delta) Max Nonempty).
              exploit H0; eauto. intros [A | B]. congruence. extlia.
              right. auto.
            * simpl in H6. eapply IHs1'; eauto.
         ++ eapply IHs1'; eauto. erewrite map_perm_3 in H6; eauto.
      -- eapply IHs1'; eauto. erewrite map_perm_1 in H6; eauto.
         intros (d & A). congruence.
Qed.

Lemma inject_mem_perm_inv: forall m1' m2 s2 s2' j1' j2 m2' ofs1 k p b2 b1 delta,
    Mem.support m2 = s2' ->
    Mem.meminj_no_overlap j1' m1' ->
    Mem.inject_mem s2 j1' j2 m1' m2 = m2' ->
    sup_In b1 (Mem.support m1') -> sup_In b2 s2' ->
    j1' b1 = Some (b2, delta) ->
    Mem.valid_position b2 j2 s2 s2' ->
    Mem.perm m2' b2 (ofs1 + delta) k p ->
    Mem.perm m1' b1 ofs1 k p \/
    ~ Mem.perm m1' b1 ofs1 Max Nonempty.
Proof.
  intros. set (ofs2 := ofs1 + delta).
  replace ofs1 with (ofs2 - delta) in * by lia.
  replace (ofs2 - delta + delta) with ofs2 in H6 by lia.
  eapply inject_map_perm_inv; eauto.
Qed.

Lemma inject_map_perm : forall s1' s2 s2' j1' j2 m1' m2 m2' b1 ofs1 delta b2 k p,
   Mem.support m2 =  s2' ->
   Mem.inject_map s1' s2 j1' j2 m1' m2 = m2' ->
   Mem.meminj_no_overlap j1'  m1' ->
   sup_In b1 s1' -> sup_In b2 s2' ->
   j1' b1 = Some (b2,delta) ->
   Mem.valid_position b2 j2 s2 (Mem.support m2) ->
   Mem.perm m1' b1 ofs1 k p ->
   Mem.perm m2' b2 (ofs1 + delta) k p.
Proof.
  induction s1'; intros; simpl in *.
  - subst. inv H2.
  - destruct H2.
    + (* local a = b1, if copy left, else right. *)
      subst a.
      erewrite map_perm_2; eauto.
      rewrite Mem.inject_map_support; eauto.
      destruct (Mem.valid_position_dec); try congruence. simpl.
      replace (ofs1 + delta - delta) with ofs1 by lia.
      destruct (Mem.perm_dec m1' b1 ofs1 Max Nonempty) eqn : Hb; simpl.
      -- auto.
      -- exfalso. apply n. eauto with mem.
    + destruct (j1' a) as [[a' delta']|] eqn: Hj1'a.
      -- destruct (eq_block a' b2).
         ++ (* the case where we need to use no_overlap to state the image of a and b1 diffs*)
            subst. erewrite map_perm_2; eauto.
            rewrite Mem.inject_map_support; eauto.
            destruct (Mem.valid_position_dec); try congruence. simpl.
            destruct (Mem.perm_dec m1' a (ofs1 + delta - delta') Max Nonempty) eqn : Hb; simpl.
            * destruct (eq_block a b1) eqn: Hab1.
              replace delta' with delta in * by congruence.
              subst.
              replace (ofs1 + delta - delta) with ofs1 by lia. auto.
              red in H1.
              destruct (Mem.perm_dec m1' b1 ofs1 Max Nonempty).
              exploit H1; eauto. intros [A | B]. congruence. extlia.
              exfalso. apply n0. eauto with mem.
            * simpl. eapply IHs1'; eauto.
         ++ erewrite map_perm_3; eauto.
     -- erewrite map_perm_1; eauto.
         intros (d & A). congruence.
Qed.

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

Lemma source_value_closure: forall m1 m2 m1' m3' j1 j1' j2 j2' b1 ofs1 b2 delta,
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
  -   (* b1 is mapped in j1 *)
    destruct (compose_meminj j1 j2 b1) as [[b3 delta3]|] eqn: Hmapped13.
    + (* b1 is mapped in compose_meminj j1 j2 *)
      apply INCR13 in Hmapped13.
      eapply memval_map_inject_new.
      inversion INJ13'. inversion mi_inj.
      eapply mi_memval; eauto.
    + (* b1 is unmapped in compose_meminj j1 j2*)
      inversion UNMAP. inversion INJ12.
      assert (mem_memval m1' b1 ofs1 = mem_memval m1 b1 ofs1).
      unfold mem_memval. apply unchanged_on_contents.
      eauto. eapply unchanged_on_perm; eauto.
      destruct (Mem.sup_dec b1 (Mem.support m1)). eauto. apply mi_freeblocks in n. congruence.
      eapply memval_map_inject_old. rewrite H.
      eapply memval_inject_incr. 2: eauto.
      inversion mi_inj. eapply mi_memval. eauto.
      eapply unchanged_on_perm. eauto.
      destruct (Mem.sup_dec b1 (Mem.support m1)). eauto. apply mi_freeblocks in n. congruence.
      eauto.
  - (* b1 is unmapped in j1 *)
    exploit ADDEXISTS; eauto. intros (b3 & delta3 & Hmapped13).
    eapply memval_map_inject_new.
    inversion INJ13'. inversion mi_inj.
    eapply mi_memval; eauto.
Qed.


Lemma inject_map_content : forall s1' s2 s2' j1'  j2' m1' m2' m3' b1 ofs1 delta b2 j1 j2 m1 m2 m2'1,
   Mem.support m2'1 = s2' ->
   Mem.inject_map s1' s2 j1' j2 m1' m2'1 = m2' ->
   Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
   Mem.inject (compose_meminj j1' j2') m1' m3' ->
   inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2') ->
   inject_incr j1 j1' ->
   Mem.inject j1 m1 m2 ->
   Mem.meminj_no_overlap j1' m1' ->
   update_add_exists j1 j1' (compose_meminj j1' j2') ->
   sup_In b1 s1' -> sup_In b2 s2' ->
   j1' b1 = Some (b2,delta) ->
   Mem.valid_position b2 j2 s2 s2' ->
   Mem.perm m1' b1 ofs1 Cur Readable ->
   memval_inject j1' (mem_memval m1' b1 ofs1) (mem_memval m2' b2 (ofs1+ delta)).
Proof.
  induction s1'; intros until m2'1; intros SUPINCL2 INJMAP UNMAP INJ13' INCR13 INCR12 INJ12 INJNOLAP ADDEXISTS IN1 IN2 MAP VALID PERM1.
  - inv INJMAP. inv IN1.
  - simpl in INJMAP. destruct IN1.
    subst.
    + erewrite map_content_2 with (m2' :=(Mem.map j1' j2 b1 s2 m1' (Mem.inject_map s1' s2 j1' j2 m1' m2'1))); eauto.
      rewrite Mem.inject_map_support; auto. replace (ofs1 + delta - delta) with ofs1 by lia.
      destruct (Mem.valid_position_dec); simpl; try congruence.
      destruct (Mem.sup_dec b2 (Mem.support m2'1)); try congruence; simpl.
      destruct (Mem.perm_dec m1' b1 ofs1 Cur Readable); simpl.
      eapply source_value_closure; eauto.
      exfalso. apply n. eauto with mem.
    + destruct (j1' a) as [[a' delta']|] eqn: Hj1'a.
      -- destruct (eq_block a' b2).
         ++ (* the case where we need to use no_overlap to state the image of a and b1 diffs*)
            subst.
            destruct (eq_block a b1) eqn: Hab1.
            * replace delta' with delta in * by congruence. subst.
              erewrite map_content_2 with (m2' := (Mem.map j1' j2 b1 s2 m1' (Mem.inject_map s1' s2 j1' j2 m1' m2'1))); eauto.
              rewrite Mem.inject_map_support; auto.
              destruct (Mem.valid_position_dec); simpl; try congruence.
              destruct (Mem.sup_dec b2 (Mem.support m2'1)); try congruence. simpl.
              replace (ofs1 + delta - delta) with ofs1 in * by lia. subst.
              destruct (Mem.perm_dec m1' b1 ofs1 Cur Readable) eqn : Hb; simpl.
              eapply source_value_closure; eauto.
              eapply IHs1'; eauto.
            * simpl.
              erewrite map_content_2 with (m2' := (Mem.map j1' j2 a s2 m1' (Mem.inject_map s1' s2 j1' j2 m1' m2'1))); eauto.
              rewrite Mem.inject_map_support; auto.
              destruct (Mem.valid_position_dec); simpl; try congruence.
              destruct (Mem.sup_dec b2 (Mem.support m2'1)); try congruence. simpl.
              destruct (Mem.perm_dec m1' a (ofs1 + delta - delta') Cur Readable) eqn : Hb; simpl.
              exploit INJNOLAP; eauto with mem. intros [A | B].
              congruence. extlia.
              eapply IHs1'; eauto.
         ++ erewrite map_content_1 with (m2' := m2'); eauto. intros [d A]. congruence.
      -- erewrite map_content_1 with (m2' := m2'); eauto. intros [d A]. congruence.
Qed.

Lemma loc_out_of_reach_incr : forall j1 j1' m1 m2 m1' b ofs,
    loc_out_of_reach j1 m1 b ofs ->
    inject_dom_in j1 (Mem.support m1) ->
    inject_incr j1 j1' ->
    injp_max_perm_decrease m1 m1' ->
    sup_In b (Mem.support m2) ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    loc_out_of_reach j1' m1' b ofs.
Proof.
  intros. red. intros.
  destruct (j1 b0) as [[b' delta']|] eqn : Hj1b.
  - erewrite H1 in H5; eauto. inv H5.
    intro. apply H2 in H5.
    apply H in Hj1b. congruence.
    unfold Mem.valid_block. eauto.
  - exploit H4; eauto. intros [A B].
    congruence.
Qed.

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
  intros.
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

Lemma memval_compose_2:
  forall mv mv3 j1 j2,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j2 (Mem.memval_map j1 mv) mv3.
Proof.
  intros; inv H; simpl.
  - constructor.
  - inv H0; try constructor; try constructor.
    unfold compose_meminj in H.
    destruct (j1 b1) as [[b2' delta']|] eqn:Hj1; try constructor.
    destruct (j2 b2') as [[b2'' delta'']|] eqn:Hj2; try constructor.
    inv H.
    econstructor; eauto.
    rewrite add_repr.
    rewrite Ptrofs.add_assoc. auto.
    congruence.
  - constructor.
Qed.

Lemma inject_map_new_perm_inv : forall s1 s2 j1' j2 m1' m2 m2' b2 ofs2 k p,
    Mem.inject_map s1 s2 j1' j2 m1' m2 = m2' ->
    ~ Mem.perm m2 b2 ofs2 Max Nonempty ->
    Mem.perm m2' b2 ofs2 k p ->
    exists b1 delta2, j1' b1 = Some (b2,delta2) /\
                 Mem.perm m1' b1 (ofs2 - delta2) k p.
Proof.
  induction s1; intros.
  - simpl in H. subst. exfalso. apply H0. eauto with mem.
  - simpl in H.
    destruct (Mem.perm_dec (Mem.inject_map s1 s2 j1' j2 m1' m2) b2 ofs2 k p).
    + eapply IHs1; eauto.
    + destruct (j1' a) as [[b d]|] eqn: MAP1.
      * destruct (eq_block b b2).
        -- 
        subst.
        erewrite map_perm_2 in H1; eauto.
        rewrite Mem.inject_map_support in H1.
        destruct (Mem.valid_position_dec b2 j2 s2 (Mem.support m2));
        destruct (Mem.perm_dec m1' a (ofs2 - d) Max Nonempty); simpl in H1; try congruence.
        exists a ,d. split. auto. auto.
        -- erewrite map_perm_3 in H1; eauto.
      * erewrite map_perm_1 in H1; eauto.
        intros [d A]. congruence.
Qed.

Lemma inject_map_new_content : forall s1' s2 j1' j2 m1' m2 m2' b1 ofs2 b2 delta2,
    Mem.inject_map s1' s2 j1' j2 m1' m2 = m2' ->
    sup_In b1 s1' ->
    j1' b1 = Some (b2, delta2) ->
    Mem.perm m1' b1 (ofs2 -delta2) Cur Readable ->
    Mem.valid_position b2 j2 s2 (Mem.support m2) ->
    Mem.meminj_no_overlap j1' m1' ->
    mem_memval m2' b2 ofs2 = Mem.memval_map j1' (mem_memval m1' b1 (ofs2 - delta2)).
Proof.
  induction s1'; intros.
  - simpl in H. inv H0.
  - simpl in H.
    destruct H0.
    + subst. erewrite map_content_2; eauto.
      rewrite Mem.inject_map_support.
      destruct (Mem.valid_position_dec b2 j2 s2 (Mem.support m2));
      destruct (Mem.perm_dec m1' b1 (ofs2 - delta2) Cur Readable); simpl; try congruence.
    + exploit IHs1'; eauto. intro MVAL.
      destruct (j1' a) as [[b2' delta2']|] eqn: Hj1'a.
      * destruct (eq_block b2 b2').
        -- subst.
           erewrite map_content_2; eauto.
           rewrite Mem.inject_map_support.
           destruct (Mem.valid_position_dec b2' j2 s2 (Mem.support m2));
           destruct (Mem.perm_dec m1' a (ofs2 - delta2') Cur Readable); simpl; try congruence.
           destruct (eq_block a b1). replace delta2' with delta2 by congruence.
           subst. auto.
           exploit H4; eauto with mem.
           intros [A|B]. congruence. extlia.
        -- erewrite map_content_1; eauto. intros [d A]. congruence.
      * erewrite map_content_1; eauto. intros [d A]. congruence.
Qed.


(*
SUPEXT : supext s2' m2



j1 b1 = Some (b2,0) j2 b2 = Some (b3,0)
j1' b1 = Some (b2,0) j2' b1 = Some (b3,0)


m1 m2 m3              m1' m2' m3'
b1 [p1]      ----->   b1 [None]

b2 [p1]      ----->   b2 [None]

b3 [p1]      ------>  b3 [p1 or None]

INITIAL : 1) extend the suppor to s2'
          2) pre_free of regions {(b2,ofs2)} in m2 which are
             a) in_reach of j1 m1 /\ j2 b2 = Some (_) (which means it's in the closure of Mem.inject j m1 m3)
             b) loc_out_of_reach j1' m1' (out of the closure of Mem.inject j' m1' m3' because of free in m1')


MAP : 

m1'  suppoort (m1')
sup_In b1' support m1'

j1' b1 = Some (b2,_) /\ j2 b2 = Some

*)

Section meminj1.

Variable m1 m1' m2 m2'1 m2' m3 m3': mem.
Variable j1 j1' j2 j2': meminj.
Variable s2': sup.
Hypothesis DOMIN1: inject_dom_in j1 (Mem.support m1).
Hypothesis DOMIN1': inject_dom_in j1' (Mem.support m1').
Hypothesis INITIAL : Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN1' (Mem.support m2) s2' m2 = m2'1.
Hypothesis INJMAP: Mem.inject_mem (Mem.support m2) j1' j2 m1' m2'1 = m2'.
(*Hypothesis CONSTRUCTION : Mem.construction_m2' m1 m1' m2 j1 j1' (Mem.support m2) s2'
                                               DOMIN1 DOMIN2 m2'. *)
Hypothesis UNCHANGE1: Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1'.
Hypothesis UNCHANGE3: Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3'.
Hypothesis INJ12 : Mem.inject j1 m1 m2.
Hypothesis INJ23 : Mem.inject j2 m2 m3.
Hypothesis INJ13': Mem.inject (compose_meminj j1' j2') m1' m3'.
Hypothesis SUPINCL2 : Mem.sup_include (Mem.support m2) s2'.
Hypothesis SUPINCL3 : Mem.sup_include (Mem.support m3) (Mem.support m3').
Hypothesis INCR1 : inject_incr j1 j1'.
Hypothesis INCR2 : inject_incr j2 j2'.
Hypothesis INCRDISJ1 :inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2).
Hypothesis INCRDISJ2 :inject_incr_disjoint j2 j2' (Mem.support m2) (Mem.support m3).
Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j1 j1'.
Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'.
Hypothesis IMGIN1': inject_image_in j1' s2'.
Hypothesis DOMIN2': inject_dom_in j2' s2'.
Hypothesis ADDZERO: update_add_zero j1 j1'.
Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2').
Hypothesis ADDSAME : update_add_same j2 j2' j1'.

Lemma INJNOLAP1 : Mem.meminj_no_overlap j1' m1'.
Proof.
  eapply update_meminj_no_overlap1; eauto.
Qed.

Lemma SUP2' : Mem.support m2'1 = s2'.
Proof.
  simpl. apply initial_m2'_support in INITIAL. congruence. eauto.
Qed.

Lemma SUP2 : Mem.support m2' = s2'.
Proof.
  simpl.
  rewrite <-INJMAP.
  rewrite Mem.inject_mem_support.
  apply SUP2'.
Qed.

Lemma INITIAL_UNMAP2 : Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
Proof. eapply initial_unmapped; eauto. Qed.

Lemma INJMAP_UNMAP2 : Mem.unchanged_on (loc_sup_in_unmapped j2 (Mem.support m2)) m2'1 m2'.
Proof. eapply inject_map_unmapped; eauto. Qed.

Theorem UNMAP2: Mem.unchanged_on (loc_unmapped j2) m2 m2'.
Proof.
  generalize INITIAL_UNMAP2. intro UN1.
  generalize INJMAP_UNMAP2. intro UN2.
  constructor.
  - rewrite SUP2. auto.
  - intros.
    inversion UN1. rewrite unchanged_on_perm; eauto.
    inversion UN2. rewrite unchanged_on_perm0; eauto.
    reflexivity.
    red. split. apply H0. apply H. unfold Mem.valid_block in *.
    rewrite SUP2'. eauto.
  - intros.
    inversion UN2. rewrite unchanged_on_contents; eauto.
    inversion UN1. rewrite unchanged_on_contents0; eauto.
    red. split; eauto. eapply Mem.perm_valid_block; eauto.
    inversion UN1. rewrite <- unchanged_on_perm0; eauto.
    eapply Mem.perm_valid_block; eauto.
Qed.

Lemma ADD_MAP2: forall b1 b2 delta,
    j1 b1 = None ->
    j1' b1 = Some (b2, delta) ->
    j2' b2 <> None.
Proof.
  intros. exploit ADDEXISTS; eauto.
  intros (b3 & ofs3 & A). unfold compose_meminj in A.
  rewrite H0 in A.
  destruct (j2' b2) eqn:?; congruence.
Qed.
Theorem inject_mem_inj1:
  Mem.mem_inj j1' m1' m2'.
Proof.
  constructor.
  - intros.
    destruct (Mem.valid_position_dec b2 j2 (Mem.support m2) s2').
    + eapply inject_map_perm; eauto.
      eapply INJNOLAP1.
      rewrite SUP2'. eauto.
      rewrite SUP2'. eauto.
    + unfold Mem.valid_position in n.
      assert (sup_In b2 s2'). eauto.
      destruct (Mem.sup_dec b2 (Mem.support m2));
        destruct (j2 b2) eqn: Hj2.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      *
      destruct (j1 b1) as [[b2' delta']|] eqn: Hj1.
      **
      apply INCR1 in Hj1 as H'. rewrite H in H'. inversion H'.
      subst b2' delta'. clear H'.
      assert (IN1: Mem.valid_block m1 b1).
      unfold Mem.valid_block. eauto.
      assert (UNMAP: loc_unmapped (compose_meminj j1 j2) b1 ofs).
      red. unfold compose_meminj. rewrite Hj1, Hj2. auto.
      generalize UNMAP2. intro UNMAP2. inversion UNMAP2.
      erewrite <- unchanged_on_perm; eauto.
      eapply Mem.perm_inject; eauto.
      inversion UNCHANGE1.
      erewrite unchanged_on_perm0; eauto.
      ** exploit INCRDISJ1; eauto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
  - intros. destruct (j1 b1) as [[b2' delta']|] eqn : Hj1b1.
    + erewrite INCR1 in H; eauto. inv H. inversion INJ12. inversion mi_inj.
      eapply mi_align; eauto. apply inject_implies_dom_in in INJ12 as DOMIN.
      red. intros.
      red in H0. eapply MAXPERM1. eapply DOMIN; eauto. eapply H0; eauto.
    + exploit ADDZERO; eauto. intro. subst. destruct chunk; simpl; eapply Z.divide_0_r.
  - intros.
    destruct (Mem.valid_position_dec b2 j2 (Mem.support m2) s2').
    + eapply inject_map_content. 13: eauto. apply SUP2'. all: eauto.
      eapply compose_meminj_incr; eauto.
      eapply INJNOLAP1.
    + unfold Mem.valid_position in n.
      assert (sup_In b2 s2'). eauto.
      destruct (Mem.sup_dec b2 (Mem.support m2));
        destruct (j2 b2) eqn: Hj2.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      *
      destruct (j1 b1) as [[b2' delta']|] eqn: Hj1.
      **
      apply INCR1 in Hj1 as H'. rewrite H in H'. inversion H'.
      subst b2' delta'. clear H'.
      assert (IN1: Mem.valid_block m1 b1).
      unfold Mem.valid_block. eauto.
      assert (UNMAP: loc_unmapped (compose_meminj j1 j2) b1 ofs).
      red. unfold compose_meminj. rewrite Hj1, Hj2. auto.
      assert (PEMR1: Mem.perm m1 b1 ofs Cur Readable).
      inversion UNCHANGE1. eapply unchanged_on_perm; eauto.
      assert (PERM2: Mem.perm m2 b2 (ofs+delta) Cur Readable).
      eapply Mem.perm_inject; eauto.
      inversion UNCHANGE1.
      erewrite unchanged_on_contents; eauto.
      generalize UNMAP2. intro UNMAP2. inversion UNMAP2.
      erewrite unchanged_on_contents0; eauto.
      inversion INJ12. inversion mi_inj.
      eapply memval_inject_incr; eauto.
      ** exploit INCRDISJ1; eauto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
Qed.

Theorem inject_mem_inject1 :
    Mem.inject j1' m1' m2'.
Proof.
  constructor.
  - eapply inject_mem_inj1; eauto.
  - intros. destruct (j1' b) as [[b' o]|] eqn: Hj1; auto.
    apply DOMIN1' in Hj1. exfalso. eauto.
  - intros. red in IMGIN1'. unfold Mem.valid_block.
    rewrite SUP2. eauto.
  - eapply INJNOLAP1; eauto.
  - intros. destruct (j1 b) as [[b'' delta']|] eqn: Hj1b.
    + erewrite INCR1 in H; eauto. inv H.
      inversion INJ12. eapply mi_representable; eauto.
      destruct H0. left. apply MAXPERM1; eauto. eapply inject_implies_dom_in; eauto.
      right. apply MAXPERM1; eauto. eapply inject_implies_dom_in; eauto.
    + exploit ADDZERO; eauto. intro. subst. split. lia.
      generalize (Ptrofs.unsigned_range_2 ofs). lia.
  - intros.
        destruct (Mem.valid_position_dec b2 j2 (Mem.support m2) s2').
    + eapply inject_mem_perm_inv; eauto.
      eapply INJNOLAP1.
      rewrite SUP2'. eauto.
      rewrite SUP2'. eauto.
    + unfold Mem.valid_position in n.
      assert (sup_In b2 s2'). eauto.
      destruct (Mem.sup_dec b2 (Mem.support m2));
        destruct (j2 b2) eqn: Hj2.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      *
      destruct (j1 b1) as [[b2' delta']|] eqn: Hj1.
      **
      apply INCR1 in Hj1 as H'. rewrite H in H'. inversion H'.
      subst b2' delta'. clear H'.
      assert (IN1: Mem.valid_block m1 b1).
      unfold Mem.valid_block. eauto.
      assert (UNMAP: loc_unmapped (compose_meminj j1 j2) b1 ofs).
      red. unfold compose_meminj. rewrite Hj1, Hj2. auto.
      generalize UNMAP2. intro UNMAP2. inversion UNMAP2.
      erewrite <- unchanged_on_perm in H0; eauto.
      inversion INJ12. exploit mi_perm_inv; eauto.
      inversion UNCHANGE1.
      intros [A | B].
      left. eapply unchanged_on_perm0; eauto.
      right. eauto.
      ** exploit INCRDISJ1; eauto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
      * exfalso. apply n. split. auto. intros [A B]. congruence.
Qed.


Theorem MAXPERM2: injp_max_perm_decrease m2 m2'.
Proof.
  red. intros b2 ofs2 p IN2 PERM2'. unfold Mem.valid_block in IN2.
  generalize inject_mem_inject1.
  intro INJ12'.
  destruct (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b2 ofs2 Max Nonempty); eauto.
  - (* in reach of j1' m1'*)
    simpl.
    destruct l as (b0 & d & MAP1' & PERM1'').
    assert (MAP1: j1 b0 = Some (b2,d)).
    {
      destruct (j1 b0) as [[b' d']|] eqn: Hj1b0.
      erewrite INCR1 in MAP1'; eauto.
      exploit INCRDISJ1; eauto. intros [A B].
      congruence.
    }
    assert (PERM1' : Mem.perm m1' b0 (ofs2 - d) Max p).
    inversion INJ12'.
    exploit mi_perm_inv; eauto.
    replace ofs2 with (ofs2 -d + d) in PERM2' by lia.
    eauto. intros [A | A].
    auto. congruence.
    apply MAXPERM1 in PERM1' as PERM1; eauto.
    inversion INJ12. inversion mi_inj.
    exploit mi_perm; eauto.
    intros. replace (ofs2 - d + d) with ofs2 in H by lia.
    auto. unfold Mem.valid_block. red in DOMIN1. eauto.
  - (* out of reach *)
    simpl.
    apply Mem.out_of_reach_reverse in n.
    exploit inject_mem_out_of_reach; eauto.
    intros UNCHANGE.
    destruct UNCHANGE.
    exploit unchanged_on_perm; eauto.
    unfold Mem.valid_block. rewrite SUP2'.
    eauto.
    intro PERM. apply PERM in PERM2' as PERM2'1.
    eapply initial_max_perm_decrease; eauto.
Qed.

Theorem OUTOFREACH1 : Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
Proof.
  constructor.
  generalize SUP2. intro SUP2.
  - rewrite SUP2. auto.
  - intros.
    exploit initial_out_of_reach1; eauto.
    intro. inversion H1.
    exploit unchanged_on_perm; eauto. intro PERM1.
    eapply loc_out_of_reach_incr in H; eauto.
    exploit inject_mem_out_of_reach; eauto.
    intro. inversion H2.
    exploit unchanged_on_perm0; eauto.
    unfold Mem.valid_block. rewrite SUP2'. eauto.
    intro PERM2.
    etransitivity; eauto.
  - intros.
    exploit initial_out_of_reach1; eauto.
    intro. inversion H1.
    exploit unchanged_on_contents; eauto. intro CONTENT1.
    eapply loc_out_of_reach_incr in H as H'; eauto.
    exploit inject_mem_out_of_reach; eauto.
    intro. inversion H2.
    exploit unchanged_on_contents0; eauto.
    exploit unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    intro PERM1.
    apply PERM1. eauto.
    intro CONTENT2.
    etransitivity; eauto.
    eapply Mem.perm_valid_block; eauto.
Qed.

Lemma manual_free_valid:
  forall b2 ofs2 b3 delta3,
    j2 b2 = Some (b3,delta3) ->
    Mem.loc_in_reach j1 m1 b2 ofs2 Max Nonempty ->
    ~ Mem.loc_in_reach j1' m1' b2 ofs2 Max Nonempty ->
    ~ Mem.perm m2' b2 ofs2 Max Nonempty.
Proof.
  intros.
  apply inject_implies_dom_in in INJ23.
  assert (~ Mem.perm m2'1 b2 ofs2 Max Nonempty).
  eapply initial_free_valid; eauto.
  exploit inject_mem_out_of_reach; eauto. intro UNCHANGE.
  apply Mem.out_of_reach_reverse in H1.
  inversion UNCHANGE. intro. apply H2.
  erewrite unchanged_on_perm; eauto.
  unfold Mem.valid_block. rewrite SUP2'. eauto.
Qed.

Lemma initial_new_region_no_perm: forall b2 ofs2 k p,
    ~ sup_In b2 (Mem.support m2) ->
    ~ Mem.perm m2'1 b2 ofs2 k p.
Proof.
  intros.
  unfold Mem.initial_m2' in INITIAL.
  intro.
  eapply initial_perm_decrease in H0; eauto.
  apply Mem.perm_valid_block in H0. eauto.
Qed.

Lemma update_new_perm_inv': forall b2 ofs2 b3 delta3 k p,
    j2 b2 = None ->
    j2' b2 = Some (b3, delta3) ->
    Mem.perm m2' b2 ofs2 k p ->
    exists b1, j1' b1 = Some (b2, 0) /\
    Mem.perm m1' b1 ofs2 k p.
Proof.
  intros.
  exploit inject_map_new_perm_inv; eauto.
  exploit INCRDISJ2; eauto. intros [A B].
  eapply initial_new_region_no_perm; eauto.
  intros (b1 & d2 & A & B).
  exploit ADDSAME; eauto.
  intros (b1' & C & INJECTIVE).
  apply INJECTIVE in A as EQ. subst. rewrite A in C. inv C.
  exists b1'. split. auto. replace (ofs2) with (ofs2 - 0) by lia. auto.
Qed.

Lemma update_new_memval:
  forall b1 b2 b3 ofs2 delta3,
    j2 b2 = None ->
    j2' b2 = Some (b3,delta3) ->
    j1' b1 = Some (b2,0) ->
    Mem.perm m1' b1 ofs2 Cur Readable ->
    (Maps.ZMap.get ofs2 (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m2'))) =
    Mem.memval_map j1' (Maps.ZMap.get ofs2 (NMap.get (Maps.ZMap.t memval) b1 (Mem.mem_contents m1'))).
Proof.
  intros.
  generalize inject_mem_inject1. intro INJ12'.
  exploit inject_map_new_content; eauto.
  replace (ofs2) with (ofs2 - 0) in H2 by lia. eauto.
  red. split. rewrite SUP2'. eauto.
  exploit INCRDISJ2; eauto. intros [A B].
  intros [C D]. congruence.
  inversion INJ12'. auto.
  replace (ofs2 - 0) with ofs2 by lia. eauto.
Qed.

Lemma update_old_memval:
  forall b1 b2 b3 ofs2 delta2 delta3,
    j2 b2 = Some (b3,delta3) ->
    j2' b2 = Some (b3,delta3) ->
    j1' b1 = Some (b2,delta2) ->
    Mem.perm m1' b1 (ofs2 - delta2) Cur Readable ->
    (Maps.ZMap.get ofs2 (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m2'))) =
    Mem.memval_map j1' (Maps.ZMap.get (ofs2 - delta2) (NMap.get (Maps.ZMap.t memval) b1 (Mem.mem_contents m1'))).
Proof.
  intros.
  generalize inject_mem_inject1. intro INJ12'.
  eapply inject_map_new_content; eauto.
  red. split. rewrite SUP2'. eauto.
  intros [A B]. congruence.
  inversion INJ12'. eauto.
Qed.

Theorem inject_mem_inj2 :
    Mem.mem_inj j2' m2' m3'.
Proof.
  generalize inject_mem_inject1. intro INJ12'.
  generalize MAXPERM2. intro MEXPERM2.
 constructor.
  - intros b2 b3 delta3 ofs2 k p MAP2 PERM2.
    destruct (j2 b2) as [[b3' delta3']|] eqn: Hj2b2.
    + apply INCR2 in Hj2b2 as MAP2'. rewrite MAP2 in MAP2'. inversion MAP2'.
      subst b3' delta3'. clear MAP2'.
      destruct (Mem.loc_in_reach_dec (Mem.support m1) m1 j1 b2 ofs2 Max Nonempty DOMIN1).
      * (* b2 is in the reach of j1 *)
        destruct (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b2 ofs2 Max Nonempty DOMIN1').
        -- (* b2 is in the reach of j1' -- ok*)
          destruct l0 as (b1 & delta2 & MAP1 & PERM1).
          replace (ofs2 + delta3) with ((ofs2 - delta2) + (delta2 + delta3)) by lia.
          eapply Mem.perm_inject. 2: eauto. unfold compose_meminj.
          rewrite MAP1, MAP2. reflexivity.
          inversion INJ12'.
          exploit mi_perm_inv. apply MAP1.
          replace ofs2 with (ofs2 - delta2 + delta2) in PERM2 by lia.
          eauto.
          intros [A | A].
          auto. congruence.
        -- (* b1 is out of the reach of j1' -- Mem.perm m2' b2 ofs2 k p should not hold*)
          generalize (manual_free_valid _ _ _ _ Hj2b2 l n). intro.
          exfalso. apply H. eauto with mem.
      * (* b2 is out of the reach of j1 *)
        apply Mem.out_of_reach_reverse in n.
        assert (Mem.perm m2 b2 ofs2 k p).
        {
          generalize OUTOFREACH1. intro OUTOFREACH1.
          inversion OUTOFREACH1.
          exploit unchanged_on_perm; eauto.
          apply inject_implies_dom_in in INJ23. unfold Mem.valid_block.
          red in  INJ23; eauto.
          intro. apply H. auto.
        }
        (* update_add_out_of_reach *)
        inversion UNCHANGE3. eapply unchanged_on_perm.
        eapply loc_out_of_reach_trans; eauto.
        inversion INJ23. eauto.
        eapply Mem.perm_inject; eauto.
    + exploit update_new_perm_inv'; eauto.
      intros (b1 & MAP1 & PERM1).
      inversion INJ13'. inversion mi_inj. eapply mi_perm; eauto.
      unfold compose_meminj. rewrite MAP1,MAP2. reflexivity.
  - intros. destruct (j2 b1) as [[b2' d]|] eqn: Hj2b1.
    apply INCR2 in Hj2b1 as H'. rewrite H in H'. inversion H'.
    subst b2' d. clear H'.
    + inversion INJ23. inversion mi_inj.
      eapply mi_align; eauto.
      red. intros. apply H0 in H1. eapply MAXPERM2; eauto.
      apply inject_implies_dom_in in INJ23. unfold Mem.valid_block.
      red in  INJ23; eauto.
    +
      assert (PERM2' : Mem.perm m2' b1 ofs Max p).
      { eapply H0.
        destruct chunk; simpl; lia. }
      exploit update_new_perm_inv'; eauto.
      intros (b3 & A & B).
      assert (RANGEPERM1 : Mem.range_perm m1' b3 ofs (ofs + size_chunk chunk) Max p).
      {
        red. intros. red in H0. exploit H0; eauto.
        intros.
        exploit ADDSAME; eauto.
        intros (b0 & MAP0 & INJECTIVE).
        apply INJECTIVE in A. subst b3.
        exploit update_new_perm_inv'; eauto.
        intros (b3' & MAP3' & PERM3').
        apply INJECTIVE in MAP3'. subst b3'.
        eauto.
      }
      inversion INJ13'. inversion mi_inj. eapply mi_align.
      unfold compose_meminj.
      rewrite A,H. reflexivity.
      eauto.
  - intros b2 ofs2 b3 delta3 MAP2 PERM2.
    destruct (j2 b2) as [[b3' delta3']|] eqn: Hj2b2.
    + apply INCR2 in Hj2b2 as MAP2'. rewrite MAP2 in MAP2'. inversion MAP2'.
      subst b3' delta3'. clear MAP2'.
      destruct (Mem.loc_in_reach_dec (Mem.support m1) m1 j1 b2 ofs2 Max Nonempty DOMIN1).
      * (* b2 is in the reach of j1 *)
        destruct (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b2 ofs2 Max Nonempty DOMIN1').
        -- destruct l0 as (b1 & delta2 & MAP1 & PERM1).
           inversion INJ12'. exploit mi_perm_inv; eauto.
           replace ofs2 with (ofs2 - delta2 + delta2) in PERM2 by lia. eauto.
           intros [A | A]; try congruence.
           erewrite update_old_memval; eauto.
           inversion INJ13'. inversion mi_inj0.
           exploit mi_memval; eauto.
           unfold compose_meminj. rewrite MAP1, MAP2. eauto.
           intro.
           replace (ofs2 - delta2 + (delta2 + delta3)) with (ofs2 + delta3) in H by lia.
           apply memval_compose_2; eauto.
        -- (* b1 is out of the reach of j1' -- Mem.perm m2' b2 ofs2 k p should not hold*)
          generalize (manual_free_valid _ _ _ _ Hj2b2 l n). intro.
          exfalso. apply H. eauto with mem.
      * (* b2 is out of the reach of j1 *)
        apply Mem.out_of_reach_reverse in n.
        generalize OUTOFREACH1. intro OUTOFREACH1.
        assert (Mem.perm m2 b2 ofs2 Cur Readable).
        {
          inversion OUTOFREACH1.
          exploit unchanged_on_perm; eauto.
          apply inject_implies_dom_in in INJ23. unfold Mem.valid_block.
          red in  INJ23; eauto.
          intro. apply H. auto.
        }

        inversion OUTOFREACH1. erewrite unchanged_on_contents; eauto.
        (* update_add_out_of_reach *)
        inversion UNCHANGE3. erewrite unchanged_on_contents0; eauto.
        eapply memval_inject_incr; eauto.
        inversion INJ23. inversion mi_inj. eauto.
        eapply loc_out_of_reach_trans; eauto.
        inversion INJ23. eauto.
        eapply Mem.perm_inject; eauto.
    + exploit update_new_perm_inv'; eauto.
      intros (b1 & MAP1 & PERM1').
      erewrite update_new_memval; eauto.
      inversion INJ13'. inversion mi_inj.
      exploit mi_memval.
      unfold compose_meminj. rewrite MAP1,MAP2. reflexivity. eauto.
      intros.
      apply memval_compose_2; eauto.
Qed.

Theorem inject_mem_inject2:
    Mem.inject j2' m2' m3'.
Proof.
  generalize inject_mem_inject1. intro INJ12'.
  constructor.
  - eapply inject_mem_inj2; eauto.
  - intros. destruct (j2' b) as [[b' d]|] eqn:?.
    eapply DOMIN2' in Heqo.
    unfold Mem.valid_block in H. erewrite SUP2 in H; eauto. congruence.
    auto.
  - intros. destruct (j2 b) as [[b'' delta']|] eqn : Hj2.
    + erewrite INCR2 in H; eauto. inv H. inv INJ23. apply mi_mappedblocks in Hj2.
      unfold Mem.valid_block. eauto.
    + exploit ADDSAME; eauto. intros (b1 & MAP1 & INJECTIVE).
      inv INJ13'. eapply mi_mappedblocks. unfold compose_meminj. rewrite MAP1. rewrite H.
      reflexivity.
  - red. intros b2 b3 delta3 b2' b3' delta3' ofs2 ofs2' NEQ MAP2 MAP2' PERM2 PERM2'.
    apply inject_implies_dom_in in INJ23 as DOMIN2.
    apply inject_implies_image_in in INJ23 as IMGIN2.
    destruct (j2 b2) as [[b33 delta33]|] eqn : Hj2b2;
    destruct (j2 b2') as [[b33' delta33']|] eqn : Hj2b2'.
    + erewrite INCR2 in MAP2; eauto. inversion MAP2. subst b33 delta33. clear MAP2.
      erewrite INCR2 in MAP2'; eauto. inversion MAP2'. subst b33' delta33'. clear MAP2'.
      inversion INJ23. eapply mi_no_overlap; eauto.
      eapply MAXPERM2; eauto. apply DOMIN2 in Hj2b2. eauto.
      eapply MAXPERM2; eauto. apply DOMIN2 in Hj2b2'. eauto.
    + erewrite INCR2 in MAP2; eauto. inversion MAP2. subst b33 delta33. clear MAP2.
      apply IMGIN2 in Hj2b2. exploit INCRDISJ2; eauto. intros [A B]. left. congruence.
    + erewrite INCR2 in MAP2'; eauto. inversion MAP2'. subst b33' delta33'. clear MAP2'.
      apply IMGIN2 in Hj2b2'. exploit INCRDISJ2; eauto. intros [A B]. left. congruence.
    + exploit update_new_perm_inv'; eauto. intros (b1' & MAP1' & PERM1').
      exploit update_new_perm_inv'. apply Hj2b2. all: eauto. intros (b1 & MAP1 & PERM1).
      assert (b1 <> b1'). { destruct (eq_block b1 b1'). congruence. auto. }
      inversion INJ13'. exploit mi_no_overlap. apply H.
      unfold compose_meminj. rewrite MAP1, MAP2. reflexivity.
      unfold compose_meminj. rewrite MAP1', MAP2'. reflexivity.
      eauto. eauto. eauto.
  - intros. destruct (j2 b) as [[b'' delta']|] eqn : Hj2.
    + apply inject_implies_dom_in in INJ23 as DOMIN23.
      erewrite INCR2 in H; eauto. inversion H. subst b'' delta'. clear H.
      inversion INJ23. eapply mi_representable; eauto.
      destruct H0 as [A|A].
      left. eapply MAXPERM2 in A; eauto. unfold Mem.valid_block. red in DOMIN23; eauto.
      right. eapply MAXPERM2 in A; eauto. unfold Mem.valid_block. red in DOMIN23; eauto.
    + destruct H0 as [A|A].
      exploit update_new_perm_inv'; eauto.
      intros (b1 & MAP1 & PERM1).
      inversion INJ13'. eapply mi_representable. unfold compose_meminj. rewrite MAP1. rewrite H.
      reflexivity. left. auto.
      exploit update_new_perm_inv'; eauto.
      intros (b1 & MAP1 & PERM1).
      inversion INJ13'. eapply mi_representable. unfold compose_meminj. rewrite MAP1. rewrite H.
      reflexivity. right. auto.
  - intros b2 ofs2 b3 delta3 k p MAP2' PERM3'.
    destruct (j2 b2) as [[b3' delta3']|] eqn: Hj2b2.
    + eapply INCR2 in Hj2b2 as Hj2'b2. rewrite MAP2' in Hj2'b2.
      inversion Hj2'b2. subst b3' delta3'. clear Hj2'b2.
      destruct (Mem.loc_in_reach_dec (Mem.support m1) m1 j1 b2 ofs2 Max Nonempty DOMIN1).
      * (* b2 is in the reach of j1 *)
        destruct (Mem.loc_in_reach_dec (Mem.support m1') m1' j1' b2 ofs2 Max Nonempty DOMIN1').
        -- (* b2 is in the reach of j1' -- ok*)
          destruct l0 as (b1 & delta2 & MAP1 & PERM1).
          inversion INJ13'.
          replace (ofs2 + delta3) with ((ofs2 - delta2) + (delta2 + delta3)) in PERM3' by lia.
          exploit mi_perm_inv; eauto.
          unfold compose_meminj. rewrite MAP1. rewrite MAP2'. reflexivity.
          intros [A | A].
          left.
          replace (ofs2) with (ofs2 - delta2 + delta2) by lia.
          eapply Mem.perm_inject; eauto.
          congruence.
        -- (* b1 is out of the reach of j1' -- Mem.perm m2' b2 ofs2 k p should not hold*)
          right.
          generalize (manual_free_valid _ _ _ _ Hj2b2 l n). intro. eauto.
      * (* b2 is out of the reach of j1 *)
        apply Mem.out_of_reach_reverse in n.
        generalize OUTOFREACH1. intro OUTOFREACH1. inversion OUTOFREACH1.
        destruct (Mem.perm_dec m2 b2 ofs2 Max Nonempty).
        --
          apply inject_implies_dom_in in INJ23 as DOMIN23.
          apply inject_implies_image_in in INJ23 as IMGIN23.
          assert (PERM3 : Mem.perm m3 b3 (ofs2 + delta3) k p).
          {
            inversion UNCHANGE3. eapply unchanged_on_perm0.
            eapply loc_out_of_reach_trans; eauto.
            apply IMGIN23 in Hj2b2. eauto. eauto.
          }
          inversion INJ23.
          exploit mi_perm_inv; eauto.
          intros [A | A].
          left. eapply unchanged_on_perm; eauto.
          apply DOMIN23 in Hj2b2. eauto.
          congruence.
        -- right.
           erewrite unchanged_on_perm in n0; eauto.
          apply inject_implies_dom_in in INJ23 as DOMIN23.
          apply DOMIN23 in Hj2b2. eauto.
    +
      exploit ADDSAME; eauto.
      intros (b1 & A & B).
      inversion INJ13'. exploit mi_perm_inv; eauto.
      unfold compose_meminj. rewrite A,MAP2'. reflexivity.
      intros [C | C].
      replace ofs2 with (ofs2 + 0) by lia.
      left. eapply Mem.perm_inject; eauto.
      right. intro. apply C.
      exploit update_new_perm_inv'; eauto.
      intros (b1' & MAP1' & PERM1').
      apply B in MAP1'. subst. eauto.
Qed.

End meminj1.

Lemma inject_compose_inv:
  forall (j1 j1' j2 j2' : meminj) (m1 m2 m3 m1' m3': mem) s2',
  Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1' ->
  Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3' ->
  Mem.inject j1 m1 m2 ->
  Mem.inject j2 m2 m3 ->
  inject_incr j1 j1' -> inject_incr j2 j2' ->
  inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
  inject_incr_disjoint j2 j2' (Mem.support m2) (Mem.support m3) ->
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
  exists m2', Mem.inject j1' m1' m2' /\
         Mem.inject j2' m2' m3' /\
         injp_max_perm_decrease m2 m2' /\
         Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2' /\
         Mem.unchanged_on (loc_unmapped j2) m2 m2' /\
         Mem.sup_include s2' (Mem.support m2').
Proof.
  intros.
  apply inject_implies_dom_in in H1 as DOMIN1.
  rename H10 into DOMIN1'.
  exists (Mem.inject_mem (Mem.support m2) j1' j2 m1' (Mem.initial_m2' m1 m1' j1 j1' j2 DOMIN1 DOMIN1' (Mem.support m2) s2' m2)).
  repeat apply conj.
  eapply inject_mem_inject1; eauto.
  eapply inject_mem_inject2; eauto.
  eapply MAXPERM2; eauto.
  eapply OUTOFREACH1; eauto.
  eapply UNMAP2; eauto.
  erewrite Mem.inject_mem_support; eauto.
  erewrite initial_m2'_support. apply Mem.sup_include_refl.
  eauto. reflexivity.
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
    generalize (inject_compose_inv _ _ _ _ _ _ _ _ _ _ UNCHANGE1 UNCHANGE3 INJ12 INJ23 INCR12 INCR23 INCRDISJ12 INCRDISJ23 INCRNOLAP MAXPERM1 INJ13' DOMIN12' IMGIN12' DOMIN23' SUPINCL2 SUPINCL3 ADDZERO ADDEXISTS ADDSAME).
    intros (m2' & INJ12' & INJ23' & MAXPERM2 & OUTOFREACH1 &  UNMAP2 & SUPINCL2').
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
    + constructor; auto.
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
