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

Variant inj_incr: relation inj_world :=
  inj_incr_intro f f' s1 s2 s1' s2':
    inject_incr f f' ->
    (forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) ->
    ~sup_In b1 s1  /\ ~sup_In b2 s2) ->
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

Lemma inj_mem_sup_l w m1 m2:
  inj_mem w m1 m2 ->
  injw_sup_l w = Mem.support m1.
Proof.
  destruct 1; auto.
Qed.

Lemma inj_mem_sup_r w m1 m2:
  inj_mem w m1 m2 ->
  injw_sup_r w = Mem.support m2.
Proof.
  destruct 1; auto.
Qed.

Hint Constructors inj_mem inj_incr.
Hint Resolve inj_mem_inject inj_mem_sup_l inj_mem_sup_r.

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
  repeat (econstructor; eauto); try congruence;
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
  repeat (econstructor; eauto); try congruence;
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
    eexists; split; repeat rstep.
    erewrite <- (Mem.support_storebytes m1); eauto.
    erewrite <- (Mem.support_storebytes m2); eauto.
    constructor; eauto.
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
      simpl. extlia.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto. rauto.
    rewrite Hm2'.
    repeat (econstructor; eauto); try congruence;
      erewrite <- Mem.support_storebytes; eauto.
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
  exists (injw (meminj_dom f) (Mem.support m1) (Mem.support m1),
          injw f (Mem.support m1) (Mem.support m2)); simpl.
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

(*test
Definition meminj_incr_sep (f1 f2 f3 : meminj) : Prop :=
  forall b, f2 b =
    match f1 b with
      | Some _ => f1 b
      | None => f3 b
    end
 /\ forall b r1 r2, f1 b = Some r1 -> f3 b = Some r2 -> False.

Theorem inject_incr_sep : forall f1 f2,
    inject_incr f1 f2 -> exists f3, meminj_incr_sep f1 f2 f3.
Proof.
  intros. exists (fun b => if f1 b then None else f2 b).
  split. destruct (f1 b) eqn:?. destruct p.
  apply H in Heqo. eauto. congruence.
  intros. rewrite H0 in H1. congruence.
Qed.
*)


Definition inject_dom_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b s.

Definition inject_image_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b' s.

Definition inject_image_eq (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) <-> Mem.sup_In b' s.

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

(** Increased injection only maps invalid blocks from source to target *)
Definition inject_incr_disjoint (j j':meminj) (sd si:sup) :=
  forall b b' delta,
    j b = None ->
    j' b = Some (b', delta) ->
    ~sup_In b sd /\ ~sup_In b' si.

(** Construction of meminj j1' j2' *)

Definition meminj_add (f:meminj) b1 r:=
  fun b => if (eq_block b b1) then Some r else f b.

Lemma meminj_add_new: forall f a b,
    meminj_add f a b a = Some b.
Proof.
  intros. unfold meminj_add. rewrite pred_dec_true; auto.
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


Lemma update_properties: forall sd1' sd1 j1 j2 si1 si1' j1' j2' j' si2,
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    inject_dom_in j1 sd1 ->
    inject_image_in j1 si1 ->
    inject_dom_in j2 si1 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' sd1 si2 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include si1 si1'
    /\ inject_image_in j1' si1'
    /\ inject_incr_disjoint j1 j1' sd1 si1
    /\ inject_incr_disjoint j2 j2' si1 si2.
Proof.
  induction sd1'.
  - (*base*)
    intros; inv H.
    split. eauto. split. eauto. split. congruence.
    split. eauto. split; congruence.
  - intros sd1 j1 j2 si1 si1' j1' j2' j' si2 UPDATE DOMIN12 IMGIN12
           DOMIN23  INCR13 INCRDISJ13. inv UPDATE.
    destruct (compose_meminj j1 j2 a) eqn: Hja. eauto.
    destruct (j' a) eqn:Hj'a; eauto. destruct p.
    exploit INCRDISJ13; eauto. intros [a_notin_sd1 b_notin_si2].
    (* facts *)
    assert (MIDINCR1: inject_incr j1 (meminj_add j1 a (fresh_block si1,0))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN12 in H. congruence.
    }
    assert (MIDINCR2: inject_incr j2 (meminj_add j2 (fresh_block si1) (b,z))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN23 in H. subst. apply freshness in H. inv H.
    }
    assert (MIDINCR3: inject_incr (meminj_add (compose_meminj j1 j2) a (b,z)) j').
    {
      red. intros b0 b' o INJ. unfold meminj_add in INJ.
      destruct (eq_block b0 a). congruence. eauto.
    }
    exploit IHsd1'. eauto.
    (* rebuild preconditions for induction step *)
    + instantiate (1:= (a :: sd1)).
      red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      left. auto. right. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + rewrite meminj_add_compose; eauto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    + instantiate (1:= (si2)). rewrite meminj_add_compose.
      red. intros b0 b' o INJ1 INJ2. unfold meminj_add in INJ1. destruct (eq_block b0 a).
      congruence. exploit INCRDISJ13; eauto. intros [A B]. split.
      intros [H|H]; congruence.
      auto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    +
    intros (incr1& incr2 & sinc & imagein & disjoint1 & disjoint2).
    (*incr1*)
    split. eapply inject_incr_trans; eauto.
    (*incr2*)
    split. eapply inject_incr_trans; eauto.
    (*sinc*)
    split. eapply Mem.sup_include_trans; eauto.
    (*imagein*)
    split. eauto.
    (*disjoint1*)
    split.
    {
    red. red in disjoint1. intros b0 b' delta INJ1 INJ2.
    destruct (eq_block b0 a).
    + subst. generalize (meminj_add_new j1 a (fresh_block si1,0)). intro INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd. split. auto. apply freshness.
    + exploit disjoint1. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. right. auto. intro. apply B. apply Mem.sup_incr_in2. auto.
    }
    (*disjoint2*)
    {
    red. red in disjoint2. intros b0 b' delta INJ1 INJ2. set (nb := fresh_block si1).
    destruct (eq_block b0 nb).
    + subst. generalize (meminj_add_new j2 nb (b,z)). intro INJadd. apply incr2 in INJadd.
      rewrite INJ2 in INJadd. inv INJadd. split. apply freshness. auto.
    + exploit disjoint2. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. apply Mem.sup_incr_in2. auto. intro. apply B. auto.
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

Lemma meminj_add_diff: forall j a b a' ofs,
    a <> b ->
    meminj_add j a (a',ofs ) b = j b.
Proof.
  intros. unfold meminj_add. destruct eq_block; congruence.
Qed.

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

(** Inversion of inject increment *)
Lemma inject_incr_inv: forall j1 j2 j' sd1 si1 si2 sd1',
    inject_dom_in j1 sd1 ->
    inject_image_in j1 si1 ->
    inject_dom_in j2 si1 ->
    inject_dom_in j' sd1' ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' sd1 si2 ->
    exists j1' j2' si1', j' = compose_meminj j1' j2' /\
               inject_incr j1 j1' /\
               inject_incr j2 j2' /\
               Mem.sup_include si1 si1' /\
               inject_image_in j1' si1' /\
               inject_incr_disjoint j1 j1' sd1 si1 /\
               inject_incr_disjoint j2 j2' si1 si2.
Proof.
  intros.
  destruct (update_meminj12 sd1' j1 j2 j' si1) as [[j1' j2'] si1'] eqn: UPDATE.
  exists j1' ,j2' ,si1'.
  split. eapply update_compose; eauto.
  eapply update_properties; eauto.
Qed.

(** Inversion of injection composition *)

Lemma inject_compose_inv:
  forall (f f' : meminj) (m1 m3 : mem) s,
  Mem.inject (compose_meminj f f') m1 m3 ->
  inject_image_in f s ->
  exists m2 , Mem.inject f m1 m2 /\
         Mem.inject f' m2 m3 /\
         Mem.sup_include s (Mem.support m2).
Proof.
  intros.
  exists (Mem.inject_map (Mem.support m1) s f m1).
  
  Admitted.

(*
  we may need from construction:
  1) inject_dom_in f s'
  2) meminj_no_overlap f m1
  3) meminj_no_overlap f' ??
  step1 : construct memory m2 with correct support (repeat Mem.alloc empty 0 0)
  step2 : iterate b \in m1, if f b = Some (b',ofs), then expand the size of b' (Mem.expend, all value Vundef) and copy the content (deal with Vptr) and permission.

 *)


(** inj@inj is refined by inj *)
Lemma inj_inj2:
  subcklr (inj @ inj) inj.
Proof.
  red.
  intros w se1 se3 m1 m3 MSTBL13 MMEM13. destruct w as [w12 w23].
  destruct MMEM13 as [m2 [MMEM12 MMEM23]].
  simpl in *.
  exists (injw (compose_meminj (injw_meminj w12) (injw_meminj w23))
          (Mem.support m1)(Mem.support m3)).
  simpl.
  repeat apply conj.
  - inv MSTBL13. inv H. inv H0. inv H1.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
    + destruct MMEM12. auto.
    + destruct MMEM23. auto.
  - constructor.
    eapply Mem.inject_compose; eauto.
  - simpl.
    apply inject_incr_refl.
  - intros w13' m1' m3' MMEM13' INCR13.
    unfold rel_compose.
    clear MSTBL13.
    inv MMEM12. rename f into j12. rename H into INJ12.
    inv MMEM23. rename f into j23. rename H into INJ23.
    cbn in INCR13.
    inv MMEM13'. rename f into j13'. rename H into INJ13'.
    cbn.
    inv INCR13.
    rename H4 into INCR13.
    rename H6 into DISJ13.
    rename H7 into SUPINCL1.
    rename H8 into SUPINCL3.
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
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & IMGIN12' & INCRDISJ12 & INCRDISJ23).
    subst.
    generalize (inject_compose_inv _ _ _ _ _ INJ13' IMGIN12').
    intros (m2' & INJ12' & INJ23' & SUPINCL2').
    exists ((injw j12' (Mem.support m1') (Mem.support m2')),
       (injw j23' (Mem.support m2') (Mem.support m3'))).
    cbn.
    repeat apply conj; cbn.
    + exists m2'.
      repeat apply conj; constructor; auto.
    + constructor; auto.
      eapply Sup.sup_include_trans; eauto.
    + constructor; auto.
      ++ eapply Sup.sup_include_trans; eauto.
    + apply inject_incr_refl.
Qed.
