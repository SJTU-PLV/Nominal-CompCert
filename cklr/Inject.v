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
    injw_next_l: block;
    injw_next_r: block;
  }.

Variant inj_incr: relation inj_world :=
  inj_incr_intro f f' nb1 nb2:
    inject_incr f f' ->
    (forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) ->
     Pos.le nb1 b1 /\ Pos.le nb2 b2) ->
    inj_incr (injw f nb1 nb2) (injw f' nb1 nb2).

Variant inj_stbls: klr inj_world Genv.symtbl Genv.symtbl :=
  inj_stbls_intro f se1 se2:
    Genv.match_stbls f se1 se2 ->
    inj_stbls (injw f (Genv.genv_next se1) (Genv.genv_next se2)) se1 se2.

Variant inj_mem: klr inj_world mem mem :=
  inj_mem_intro f m1 m2 nb1 nb2:
    Mem.inject f m1 m2 ->
    Pos.le nb1 (Mem.nextblock m1) ->
    Pos.le nb2 (Mem.nextblock m2) ->
    inj_mem (injw f nb1 nb2) m1 m2.

(** ** Properties *)

(*
Instance injw_incr:
  Monotonic
    injw
    (forallr f1 f2: inject_incr, forallr -@nb1, forallr -@nb2, ⊤ ==> inj_incr).
Proof.
  repeat rstep. eauto using inj_incr_intro.
Qed.
*)

Global Instance inj_incr_preo:
  PreOrder inj_incr.
Proof.
  split.
  - intros [f nb1 nb2].
    constructor; auto using inject_incr_refl.
    congruence.
  - intros w w' w'' H H'. destruct H. inv H'.
    constructor; eauto using inject_incr_trans.
    intros b1 b2 delta Hb Hb''.
    destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'; eauto.
    rewrite (H5 _ _ _ Hb') in Hb''. inv Hb''. eauto.
Qed.

Global Instance inj_stbls_subrel:
  Monotonic inj_stbls (inj_incr ++> subrel).
Proof.
  intros w w' Hw se1 se2 Hse.
  destruct Hse; inv Hw.
  constructor. eapply Genv.match_stbls_incr; eauto.
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

Lemma inj_mem_next_l w m1 m2:
  inj_mem w m1 m2 ->
  Pos.le (injw_next_l w) (Mem.nextblock m1).
Proof.
  destruct 1; auto.
Qed.

Lemma inj_mem_next_r w m1 m2:
  inj_mem w m1 m2 ->
  Pos.le (injw_next_r w) (Mem.nextblock m2).
Proof.
  destruct 1; auto.
Qed.

Hint Constructors inj_mem inj_incr.
Hint Resolve inj_mem_inject inj_mem_next_l inj_mem_next_r.

(** ** CKLR definition *)

Program Definition inj : cklr :=
  {|
    world := inj_world;
    wacc := inj_incr;
    mi := injw_meminj;
    match_stbls := inj_stbls;
    match_mem := inj_mem;
  |}.

Next Obligation.
  destruct 1. cbn. auto.
Qed.

Next Obligation.
  destruct H. inv H0. eauto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros [f nb1 nb2] m1 m2 Hm lo hi. cbn in *. inv Hm.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf'1 & Hb2 & Hf'2);
    eauto using Z.le_refl.
  rewrite Hm2'.
  exists (injw f' nb1 nb2); split; repeat rstep.
  - constructor; eauto.
    intros b1' b2' delta' Hb Hb'.
    destruct (peq b1' b1); subst.
    + assert (b2' = b2) by congruence; subst.
      apply Mem.alloc_result in Hm1'; subst.
      apply Mem.alloc_result in Hm2'; subst.
      xomega.
    + specialize (Hf'2 _ n). congruence.
  - econstructor; eauto; erewrite Mem.nextblock_alloc by eauto; xomega.
  - cbn. red. auto.
Qed.

Next Obligation. (* Mem.free *)
  intros [f nb1 nb2] m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. cbn in H0. inv H0. inv Hm.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by xomega.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence;
    erewrite Mem.nextblock_free; eauto.
Qed.

Next Obligation. (* Mem.load *)
  intros [f nb1 nb2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr].
  cbn in *. red. inv Hm.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. repeat (econstructor; eauto).
Qed.

Next Obligation. (* Mem.store *)
  intros [f nb1 nb2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  red in Hv |- *. cbn in *. inv Hm.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence;
    erewrite Mem.nextblock_store; eauto.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros [f nb1 nb2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] sz.
  red. cbn in *. inv Hm.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros [f nb1 nb2] m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  red in Hvs |- *. cbn in *. inv Hm.
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
    eexists; split; repeat rstep. constructor; eauto.
    + eapply Mem.storebytes_empty_inject; eauto.
    + erewrite Mem.nextblock_storebytes; eauto.
    + erewrite Mem.nextblock_storebytes; eauto.
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
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto. rauto.
    rewrite Hm2'.
    repeat (econstructor; eauto); try congruence;
      erewrite Mem.nextblock_storebytes; eauto.
Qed.

Next Obligation. (* Mem.perm *)
  intros [f nb1 nb2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros [f nb1 nb2] m1 m2 Hm b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 nb1 nb2 Hm Hnb1 Hnb2].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 nb1 nb2 Hm Hnb1 Hnb2].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by xomega.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by xomega.
  assumption.
Qed.

Next Obligation.
  destruct H as [f m1 m2 nb1 nb2 Hm Hnb1 Hnb2].
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation. 
  destruct H as [f m1 m2 nb1 nb2 Hm Hnb1 Hnb2].
  eapply Mem.disjoint_or_equal_inject; eauto.
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
Lemma compose_meminj_separated f12 f23 nb1 nb2 nb3:
  inj_separated f12 nb1 nb2 ->
  inj_separated f23 nb2 nb3 ->
  inj_separated (compose_meminj f12 f23) nb1 nb3.
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
  replace (0 + ofs) with ofs by xomega.
  reflexivity.
Qed.

Lemma meminj_dom_idemp f:
  meminj_dom (meminj_dom f) = meminj_dom f.
Proof.
  eapply functional_extensionality; intro b.
  unfold meminj_dom.
  destruct (f b); eauto.
Qed.

Lemma meminj_dom_flat_inj nb:
  meminj_dom (Mem.flat_inj nb) = Mem.flat_inj nb.
Proof.
  apply functional_extensionality; intros b.
  unfold meminj_dom, Mem.flat_inj.
  destruct plt; eauto.
Qed.

(*
Lemma meminj_dom_separated f nb:
  inj_separated (meminj_dom f) nb nb.
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
    replace (ofs + 0) with ofs by xomega.
    auto.
  - unfold meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (f b1) as [[b1' delta'] | ]; inv Hb1.
    eauto using Z.divide_0_r.
  - unfold meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by xomega.
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
    split; try xomega.
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
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. auto.
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
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [f m1 m2 nb1 nb2 Hm].
  exists (injw (meminj_dom f) nb1 nb1, injw f nb1 nb2); simpl.
  repeat apply conj.
  - exists se1. split; eauto.
    inv Hse. econstructor. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [w12' w23'] m1' m3' (m2' & H12' & H23') [Hw12' Hw23']. cbn in *.
    destruct H12' as [f12' m1' m2' ? ? ? Hm12'].
    inversion H23' as [f23' xm2' xm3' ? ? ? Hm23']. clear H23'; subst.
    inversion Hw12' as [? ? ? ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    exists (injw (compose_meminj f12' f23') nb4 nb5).
    repeat apply conj.
    + constructor; auto. eapply Mem.inject_compose; eauto.
    + constructor.
      * rewrite <- (meminj_dom_compose f). rauto.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'. inv Hse.
        edestruct SEP12'; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[xb2 xdelta23] | ] eqn:Hbi.
        -- rewrite (Hf23' _ _ _ Hbi) in Hb2. inv Hb2.
           rewrite <- (Genv.mge_separated H10 _ Hbi). auto.
        -- edestruct (SEP23' bi b2); eauto. 
    + cbn. rstep; auto.
Qed.


(** * Connection to [cc_inj] *)

Lemma cc_c_inj:
  cceqv (cc_c inj) cc_inj.
Proof.
  split.
  - red. intros [f nb1 nb2] se1 se2 q1 q2 Hse Hq. cbn in *.
    inv Hse. inv Hq. cbn in *. inv H1.
    eexists (mit _ _ _). repeat apply conj.
    + constructor; eauto.
    + constructor; eauto.
    + intros r1 r2 Hr. inv Hr. inv H1. cbn in *.
      eexists. split; repeat (constructor; eauto).
  - red. intros [f nb1 nb2] se1 se2 q1 q2 Hse Hq. cbn in *.
    inv Hse. inv Hq. cbn in *.
    eexists. repeat apply conj.
    + constructor; eauto.
    + constructor; eauto.
      constructor; eauto.
    + intros r1 r2 (w' & Hw' & Hr). inv Hw'. inv Hr. inv H7. cbn in *.
      eexists; eauto. constructor; eauto.
Qed.
