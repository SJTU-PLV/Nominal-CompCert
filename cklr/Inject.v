Require Import Axioms.
Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import LanguageInterface.


(** * [Mem.inject] as a CKLR *)

(** ** Separated injections *)

Record inj_world :=
  injw {
    injw_meminj :> meminj;
    injw_sup_l: sup;
    injw_sup_r: sup;
  }.

(** Increased injection only maps invalid blocks from source to target *)
Definition inject_incr_disjoint (j j':meminj) (sd si:sup) :=
  forall b b' delta,
    j b = None ->
    j' b = Some (b', delta) ->
    ~sup_In b sd /\ ~sup_In b' si.

Variant inj_incr: relation inj_world :=
  inj_incr_intro f f' s1 s2 s1' s2':
    inject_incr f f' ->
    inject_incr_disjoint f f' s1 s2 ->
    Mem.sup_include s1 s1' ->
    Mem.sup_include s2 s2' ->
    inj_incr (injw f s1 s2) (injw f' s1' s2').

Record inj_stbls (w: inj_world) (se1 se2: Genv.symtbl): Prop :=
  {
    inj_stbls_match: Genv.match_stbls (injw_meminj w) se1 se2;
    inj_stbls_next_l: Mem.sup_include (Genv.genv_sup se1) (injw_sup_l w);
    inj_stbls_next_r: Mem.sup_include (Genv.genv_sup se2) (injw_sup_r w);
  }.

Variant inj_mem: klr inj_world mem mem :=
  inj_mem_intro f m1 m2:
    Mem.inject f m1 m2 ->
    inj_mem (injw f (Mem.support m1) (Mem.support m2)) m1 m2.

(** ** Properties *)

(*
Instance injw_incr:
  Monotonic
    injw
    (forallr f1 f2: inject_incr, forallr -@s1, forallr -@s2, ⊤ ==> inj_incr).
Proof.
  repeat rstep. eauto using inj_incr_intro.
Qed.
*)

Global Instance inj_incr_preo:
  PreOrder inj_incr.
Proof.
  split.
  - intros [f s1 s2].
    constructor; auto using inject_incr_refl, Pos.le_refl.
    congruence.
  - intros w w' w'' H H'. destruct H. inv H'.
    constructor; eauto using inject_incr_trans, Pos.le_trans.
    intros b1 b2 delta Hb Hb''.
    destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
    + rewrite (H6 _ _ _ Hb') in Hb''. inv Hb''. eauto.
    + edestruct H7; eauto. split; eauto.
Qed.

Global Instance inj_stbls_subrel:
  Monotonic inj_stbls (inj_incr ++> subrel).
Proof.
  intros w w' Hw se1 se2 Hse.
  destruct Hse; inv Hw. cbn in *.
  constructor; cbn; try extlia.
  eapply Genv.match_stbls_incr; eauto.
  intros. edestruct H0; eauto. split; eauto. eauto. eauto.
Qed.

Instance inj_proj_incr:
  Monotonic injw_meminj (inj_incr ++> inject_incr).
Proof.
  destruct 1; auto.
Qed.

(** Hints *)

Lemma inj_mem_inject w m1 m2:
  inj_mem w m1 m2 ->
  Mem.inject w m1 m2.
Proof.
  destruct 1; auto.
Qed.

Hint Constructors inj_mem inj_incr.
Hint Resolve inj_mem_inject.

(** ** CKLR definition *)

Instance inj_cklr_kf: KripkeFrame unit inj_world.
split. intro. exact inj_incr.
Defined.

Program Definition inj : cklr :=
  {|
    world := inj_world;
    wacc := inj_incr;
    mi := injw_meminj;
    match_stbls := inj_stbls;
    match_mem := inj_mem;
  |}.

Lemma inj_acc_separated w w' m1 m2:
  inj_mem w m1 m2 ->
  inj_incr w w' ->
  inject_separated w w' m1 m2.
Proof.
  intros Hm Hw b1 b2 delta Hnone Hsome.
  inv Hm. inv Hw.
  unfold Mem.valid_block.
  eapply H4; eauto.
Qed.

Next Obligation. (* mi_acc_separated *)
  eapply inj_acc_separated; eauto.
Qed.

Next Obligation.
  destruct 1. cbn. auto.
Qed.

Next Obligation.
  destruct H. inv H0; cbn in *. eauto.
Qed.

Lemma inj_cklr_alloc:
    Monotonic Mem.alloc (|= inj_mem ++> - ==> - ==> (<> inj_mem * block_inject_sameofs @@ [injw_meminj])).
Proof.
  intros [f s1 s2] m1 m2 Hm lo hi. cbn in *. inv Hm.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf'1 & Hb2 & Hf'2);
    eauto using Z.le_refl.
  rewrite Hm2'.
  exists (injw f' (Mem.support m1') (Mem.support m2')); split; repeat rstep.
  - constructor; eauto.
    intros b1' b2' delta' Hb Hb'.
    destruct (eq_block b1' b1); subst.
    + assert (b2' = b2) by congruence; subst.
      apply Mem.alloc_result in Hm1'; subst.
      apply Mem.alloc_result in Hm2'; subst.
      split; eauto. apply freshness. apply freshness.
    + specialize (Hf'2 _ n). congruence.
    + erewrite (Mem.support_alloc m1 _ _ m1'); eauto.
    + erewrite (Mem.support_alloc m2 _ _ m2'); eauto.
  - econstructor; eauto; erewrite Mem.support_alloc by eauto; extlia.
  - cbn. red. auto.
Qed.

Next Obligation. (* Mem.alloc *)
  exact inj_cklr_alloc.
Qed.

Next Obligation. (* Mem.free *)
  intros [f s1 s2] m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. cbn in H0. inv H0. inv Hm.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by extlia.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence.
  erewrite <- Mem.support_free; eauto.
  erewrite <- Mem.support_free; eauto.
Qed.

Next Obligation. (* Mem.load *)
  intros [f s1 s2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr].
  cbn in *. red. inv Hm.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. repeat (econstructor; eauto).
Qed.

Next Obligation. (* Mem.store *)
  intros [f s1 s2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  red in Hv |- *. cbn in *. inv Hm.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence.
  erewrite <- Mem.support_store; eauto.
  erewrite <- Mem.support_store; eauto.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros [f s1 s2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] sz.
  red. cbn in *. inv Hm.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros [f s1 s2] m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  red in Hvs |- *. cbn in *. inv Hm.
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
    exists (injw f (Mem.support m1') (Mem.support m2')); split; repeat rstep.
    constructor; eauto. red. congruence.
    erewrite <- (Mem.support_storebytes m1); eauto.
    erewrite <- (Mem.support_storebytes m2); eauto.
    constructor. eapply Mem.storebytes_empty_inject; eauto.
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
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto. rauto.
    rewrite Hm2'.
    repeat (econstructor; eauto); try congruence;
      try (erewrite <- Mem.support_storebytes; eauto);
        (red; intros; eapply Mem.perm_storebytes_2; eauto).
Qed.

Next Obligation. (* Mem.perm *)
  intros [f s1 s2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros [f s1 s2] m1 m2 Hm b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 s1].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 s1].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by extlia.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by extlia.
  assumption.
Qed.

Next Obligation.
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation.
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.

Next Obligation. (* perm_inv *)
  inv H0.
  eapply Mem.perm_inject_inv; eauto.
Qed.
(*
Lemma nextblock_inject:
  Monotonic
    Mem.nextblock
    (|= inj_mem ++> (<> block_inject_sameofs @@ [injw_meminj])).
Proof.
  intros w m1 m2 Hm.
  remember (Mem.alloc m1 0 0) as mb eqn: Hmb1. destruct mb as [m1' b1].
  remember (Mem.alloc m2 0 0) as mb eqn: Hmb2. destruct mb as [m2' b2].
  exploit Mem.alloc_result. symmetry. apply Hmb1. intros <-.
  exploit Mem.alloc_result. symmetry. apply Hmb2. intros <-.
  edestruct inj_cklr_alloc as (w' & Hw' & Hm'). apply Hm.
  rewrite <- Hmb1 in Hm'. rewrite <- Hmb2 in Hm'.
  exists w'. split; auto. apply Hm'.
Qed.
*)
Next Obligation. (* sup include *)
  destruct H0 as (w' & Hw' & Hm').
  destruct H. inv Hm'. inv Hw'.
  split; eauto.
Qed.

(** * Useful theorems *)

(** ** Composition lemmas *)

Global Instance compose_meminj_incr:
  Proper (inject_incr ++> inject_incr ++> inject_incr) compose_meminj.
Proof.
  intros f1 f2 Hf g1 g2 Hg b xb xdelta.
  unfold compose_meminj.
  destruct (f1 b) as [[b' delta] | ] eqn:Hb'; try discriminate.
  erewrite Hf by eauto.
  destruct (g1 b') as [[b'' delta'] | ] eqn:Hb''; try discriminate.
  erewrite Hg by eauto.
  tauto.
Qed.

(*
Lemma compose_meminj_separated f12 f23 s1 s2 s3:
  inj_separated f12 s1 s2 ->
  inj_separated f23 s2 s3 ->
  inj_separated (compose_meminj f12 f23) s1 s3.
Proof.
  intros H12 H23 b1 b3 delta Hb13. unfold compose_meminj in Hb13.
  destruct (f12 b1) as [[b2 delta12] | ] eqn:Hb12; try congruence.
  destruct (f23 b2) as [[xb3 delta23] | ] eqn:Hb23; try congruence.
  inv Hb13.
  etransitivity; eauto.
Qed.
*)

(** ** The [meminj_dom] construction *)

(** The following injection is a sub-injection of [Mem.flat_inj],
  which contains only blocks mapped by the original injection [f].
  Like [Mem.flat_inj], it is a neutral element for composition
  with [f] on the left, but the fact that its domain and codomain
  correspond to the domain of [f] yields many desirable properties
  that do not hold for [Mem.flat_inj]. *)

Definition meminj_dom (f: meminj): meminj :=
  fun b => if f b then Some (b, 0) else None.

Global Instance meminj_dom_incr:
  Monotonic (@meminj_dom) (inject_incr ++> inject_incr).
Proof.
  intros f g Hfg b b' delta Hb.
  unfold meminj_dom in *.
  destruct (f b) as [[? ?] | ] eqn:Hb'; try discriminate. inv Hb.
  erewrite Hfg; eauto.
Qed.

Lemma meminj_dom_compose f:
  compose_meminj (meminj_dom f) f = f.
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj, meminj_dom.
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  rewrite Hfb.
  replace (0 + ofs) with ofs by extlia.
  reflexivity.
Qed.

Lemma meminj_dom_idemp f:
  meminj_dom (meminj_dom f) = meminj_dom f.
Proof.
  eapply functional_extensionality; intro b.
  unfold meminj_dom.
  destruct (f b); eauto.
Qed.

Lemma meminj_dom_flat_inj s:
  meminj_dom (Mem.flat_inj s) = Mem.flat_inj s.
Proof.
  apply functional_extensionality; intros b.
  unfold meminj_dom, Mem.flat_inj.
  destruct Mem.sup_dec; eauto.
Qed.

(*
Lemma meminj_dom_separated f s:
  inj_separated (meminj_dom f) s s.
Proof.
  intros b1 b2 delta Hb.
  unfold meminj_dom in Hb. destruct (f b1); try congruence. inv Hb.
  reflexivity.
Qed.
*)

Lemma block_inject_dom f b1 b2:
  block_inject f b1 b2 ->
  block_inject (meminj_dom f) b1 b1.
Proof.
  unfold meminj_dom.
  intros (delta & Hb).
  exists 0.
  rewrite Hb; eauto.
Qed.

Lemma val_inject_dom f v1 v2:
  Val.inject f v1 v2 ->
  Val.inject (meminj_dom f) v1 v1.
Proof.
  destruct 1; econstructor.
  - unfold meminj_dom.
    rewrite H.
    reflexivity.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Lemma memval_inject_dom f v1 v2:
  memval_inject f v1 v2 ->
  memval_inject (meminj_dom f) v1 v1.
Proof.
  destruct 1; econstructor.
  eapply val_inject_dom; eauto.
Qed.

Lemma val_inject_list_dom f vs1 vs2:
  Val.inject_list f vs1 vs2 ->
  Val.inject_list (meminj_dom f) vs1 vs1.
Proof.
  induction 1; constructor; eauto using val_inject_dom.
Qed.

Lemma mem_mem_inj_dom f m1 m2:
  Mem.mem_inj f m1 m2 ->
  Mem.mem_inj (meminj_dom f) m1 m1.
Proof.
  intros H.
  split.
  - unfold meminj_dom. intros b1 b2 delta ofs k p Hb1 Hp.
    destruct (f b1); inv Hb1.
    replace (ofs + 0) with ofs by extlia.
    auto.
  - unfold meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (f b1) as [[b1' delta'] | ]; inv Hb1.
    eauto using Z.divide_0_r.
  - unfold meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
Qed.

Lemma mem_inject_dom f m1 m2:
  Mem.inject f m1 m2 ->
  Mem.inject (meminj_dom f) m1 m1.
Proof.
  intros H.
  split.
  - eapply mem_mem_inj_dom.
    eapply Mem.mi_inj; eauto.
  - unfold meminj_dom. intros.
    erewrite Mem.mi_freeblocks; eauto.
  - unfold meminj_dom; intros.
    destruct (f b) as [[b'' delta'] | ] eqn:Hb; inv H0.
    eapply Mem.valid_block_inject_1; eauto.
  - red. unfold meminj_dom. intros.
    destruct (f b1); inv H1.
    destruct (f b2); inv H2.
    eauto.
  - unfold meminj_dom. intros.
    destruct (f b); inv H0.
    split; try extlia.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  - unfold meminj_dom. intros.
    destruct (f b1); inv H0.
    rewrite Z.add_0_r in H1; eauto.
Qed.

Lemma match_stbls_dom f se1 se2:
  Genv.match_stbls f se1 se2 ->
  Genv.match_stbls (meminj_dom f) se1 se1.
Proof.
  intros Hse. unfold meminj_dom. split; eauto; intros.
  - edestruct Genv.mge_dom as (b2 & Hb2); eauto. rewrite Hb2. eauto.
  - edestruct Genv.mge_dom as (b3 & Hb3); eauto. exists b2. rewrite Hb3. eauto.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
Qed.

Lemma loc_unmapped_dom f b ofs:
  loc_unmapped (meminj_dom f) b ofs <->
  loc_unmapped f b ofs.
Proof.
  unfold meminj_dom, loc_unmapped.
  destruct (f b) as [[b' delta] | ].
  - split; discriminate.
  - reflexivity.
Qed.

(** ** CKLR composition theorems *)

Lemma inj_inj:
  subcklr inj (inj @ inj).
Proof.
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [f m1 m2 Hm].
  exists (injw (meminj_dom f) (Mem.support m1)(Mem.support m1), injw f (Mem.support m1)(Mem.support m2)); simpl.
  repeat apply conj.
  - exists se1. split; eauto.
    inv Hse. econstructor; auto. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [w12' w23'] m1' m3' (m2' & H12' & H23') [Hw12' Hw23']. cbn in *.
    destruct H12' as [f12' m1' m2' Hm12'].
    inversion H23' as [f23' xm2' xm3' Hm23']. clear H23'; subst.
    inversion Hw12' as [? ? ? ? ? ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    eexists (injw (compose_meminj f12' f23') _ _).
    repeat apply conj.
    + constructor; auto. eapply Mem.inject_compose; eauto.
    + constructor; auto.
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
