Require Import Axioms.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Extends.
Require Import ValueAnalysis.
Require Import ValueDomain.
Unset Program Cases.


(** * Preliminaries *)

Instance inj_of_bc_id bc:
  Related (inj_of_bc bc) inject_id inject_incr.
Proof.
  unfold inj_of_bc, inject_id.
  intros b1 b2 delta Hb. destruct (bc b1); congruence.
Qed.


(** * Definition *)

(** ** Worlds *)

(** As in the case of [injp], we store a lot of properties in the world itself. *)

Record vaext_wf se bc m :=
  {
    vaext_genv_match : genv_match bc se;
    vaext_mmatch : mmatch bc m mtop;
    vaext_romatch : romatch_all se bc m;
    vaext_nostack : bc_nostack bc;
  }.

Record vaext_world :=
  vaextw {
    vaext_se : Genv.symtbl;
    vaext_bc : block_classification;
    vaext_m1 : mem;
    vaext_prop : vaext_wf vaext_se vaext_bc vaext_m1;
  }.

Record vaext_incr (w w' : vaext_world) : Prop :=
  {
    vaext_incr_se :
      vaext_se w = vaext_se w';
    vaext_incr_bc b :
      sup_In b (Mem.support (vaext_m1 w)) ->
      vaext_bc w' b = vaext_bc w b;
    vaext_incr_support :
      Mem.sup_include (Mem.support (vaext_m1 w)) (Mem.support (vaext_m1 w'));
    vaext_incr_load b ofs n bytes :
      sup_In b (Mem.support (vaext_m1 w)) ->
      vaext_bc w b = BCinvalid ->
      n >= 0 ->
      Mem.loadbytes (vaext_m1 w') b ofs n = Some bytes ->
      Mem.loadbytes (vaext_m1 w) b ofs n = Some bytes;
  }.

Instance vaext_incr_preo:
  PreOrder vaext_incr.
Proof.
  split.
  - intros [se bc m H]. constructor; cbn; eauto.
  - intros [se1 bc1 m1 H1] [se2 bc2 m2 H2] [se3 bc3 m3 H3].
    intros [Hse12 Hbc12 Hnb12 Hld12] [Hse23 Hbc23 Hnb23 Hld23]; cbn in *.
    constructor; cbn in *; try (etransitivity; eauto).
    + rewrite Hbc23; eauto.
    + eauto.
    + eapply Hld12; eauto. eapply Hld23; eauto.
      * rewrite Hbc12; auto.
Qed.

(** ** Relations *)

Inductive vaext_stbls : klr vaext_world Genv.symtbl Genv.symtbl :=
  vaext_stbls_intro se bc m H :
    genv_match bc se ->
    vaext_stbls (vaextw se bc m H) se se.

Inductive vaext_mem : klr vaext_world mem mem :=
  vaext_mem_intro se bc m1 m2 H :
    Mem.extends m1 m2 ->
    vaext_mem (vaextw se bc m1 H) m1 m2.

(** ** CKLR *)

Program Definition vaext : cklr :=
  {|
    world := vaext_world;
    wacc := vaext_incr;
    mi w := inj_of_bc (vaext_bc w);
    match_stbls := vaext_stbls;
    match_mem := vaext_mem;
  |}.

Instance inj_of_bc_incr:
  Monotonic (inj_of_bc) (bc_incr ++> inject_incr).
Proof.
  intros bc1 bc2 Hbc b1 b2 delta Hb. unfold inj_of_bc in *.
  destruct (bc1 b1) eqn:H; try rewrite Hbc, H; congruence.
Qed.

Next Obligation.
  intros [se1 bc1 m1 H1] [se2 bc2 m2 H2] [Hse Hbc Hnb Hld]; cbn in *.
  rstep. intros b Hb. apply Hbc.
  eapply mmatch_below; eauto.
  eapply vaext_mmatch; eauto.
Qed.

(** Acc separated *)
Next Obligation.
  intros b1 b2 delta Hw Hw'.
  assert (~ Mem.valid_block m1 b1).
  { unfold Mem.valid_block.
    intros Hvb1.
    inv H. cbn in *.
    specialize (vaext_incr_bc _ _ H0 b1 Hvb1) as w'_bc.
    cbn in w'_bc.
    unfold inj_of_bc in Hw, Hw'.
    rewrite w'_bc in Hw'. congruence.
  }
  split. auto.
  contradict H1.
  inv H.
  apply inj_of_bc_inv in Hw'. destruct Hw' as (_ & Hb & _). subst b2.
  erewrite Mem.valid_block_extends; eauto.
Qed.

Next Obligation.
  intros [se1 bc1 m1 H1] [se2 bc2 m2 H2] [Hse Hbc Hnb Hld]; cbn in *.
  inversion 1; clear H; subst. constructor.
  eapply vaext_genv_match; eauto.
Qed.

Next Obligation.
  destruct 1; cbn.
  eapply inj_of_bc_preserves_globals; auto.
Qed.

Next Obligation.
  destruct H0. inv H.
  erewrite <- Mem.mext_sup; eauto.
Qed.

(** Alloc *)

Program Definition alloc_bc (b : block) (bc : block_classification) :=
  {|
    bc_img x := if eq_block x b then BCother else bc x;
  |}.
Next Obligation.
  destruct eq_block; try discriminate.
  destruct eq_block; try discriminate.
  eapply bc_stack; eauto.
Qed.
Next Obligation.
  destruct eq_block; try discriminate.
  destruct eq_block; try discriminate.
  eapply bc_glob; eauto.
Qed.

Lemma alloc_bc_glob bc m am x id :
  mmatch bc m am ->
  bc x = BCglob id <-> alloc_bc (Mem.nextblock m) bc x = BCglob id.
Proof.
  intros Hm. cbn.
  destruct eq_block; try reflexivity; subst.
  split; try discriminate.
  intros Hb; exfalso.
  exploit mmatch_below; eauto. rewrite Hb; discriminate.
  apply freshness.
Qed.

Lemma alloc_bc_incr bc m am :
  mmatch bc m am ->
  bc_incr bc (alloc_bc (Mem.nextblock m) bc).
Proof.
  intros Hm x VALID. cbn.
  destruct eq_block; try reflexivity; subst.
  exploit mmatch_below; eauto.
  intro. apply freshness in H. inv H.
Qed.

Lemma alloc_mmatch m lo hi m' b bc am :
  bc_nostack bc ->
  mmatch bc m am ->
  Mem.alloc m lo hi = (m', b) ->
  mmatch (alloc_bc b bc) m' am.
Proof.
  intros Hbc Hm Hm'.
  rewrite (Mem.alloc_result m lo hi m' b); auto.
  split.
  - cbn. intros x Hx.
    destruct eq_block; try discriminate.
    eelim Hbc; eauto.
  - intros id ab x Hx Hab.
    eapply alloc_bc_glob in Hx; eauto.
    eapply bmatch_incr; eauto using alloc_bc_incr.
    eapply bmatch_ext; eauto using mmatch_glob.
    intros. erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
    eapply mmatch_below; eauto. congruence.
  - intros x NOSTK VALID.
    eapply smatch_incr; eauto using alloc_bc_incr.
    cbn in *. destruct eq_block.
    + subst.
      split; intros.
      * erewrite <- Mem.alloc_result in H; eauto.
        erewrite (Mem.load_alloc_same m lo hi m' b Hm' chunk ofs v); eauto.
        constructor.
      * erewrite <- Mem.alloc_result in H; eauto.
        exploit (Mem.loadbytes_alloc_same m lo hi m' b Hm'); eauto.
        -- left. reflexivity.
        -- congruence.
    + eapply smatch_ext; eauto using mmatch_nonstack. intros.
      erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
      eapply mmatch_below; eauto.
  - intros x VALID.
    eapply smatch_incr; eauto using alloc_bc_incr.
    cbn in *. destruct eq_block; subst.
    + split; intros.
      * erewrite <- Mem.alloc_result in H; eauto.
        erewrite (Mem.load_alloc_same m lo hi m' b Hm' chunk ofs v); eauto.
        constructor.
      * erewrite <- Mem.alloc_result in H; eauto.
        exploit (Mem.loadbytes_alloc_same m lo hi m' b Hm'); eauto.
        -- left. reflexivity.
        -- congruence.
    + eapply smatch_ext; eauto using mmatch_top. intros.
      erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
      eapply mmatch_below; eauto.
  - intros x Hx. cbn in Hx.
    rewrite (Mem.support_alloc m lo hi m' b); auto.
    destruct eq_block.
    + subst. unfold Mem.nextblock. eauto.
    + assert (sup_In x (Mem.support m)).
      eapply mmatch_below; eauto.
      apply Mem.sup_include_incr in H. auto.
Qed.

Next Obligation.
  destruct 1. intros lo hi.
  destruct (Mem.alloc m1) as [m1' b] eqn:Hm1'.
  edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto.
  reflexivity. reflexivity.
  assert (vaext_wf se (alloc_bc b bc) m1').
  {
    destruct H. split.
    - rewrite (Mem.alloc_result m1 lo hi m1' b); auto.
      eapply genv_match_exten; eauto.
      + eauto using alloc_bc_glob.
      + intros. erewrite alloc_bc_incr; eauto. congruence.
    - eapply alloc_mmatch; eauto.
    - rewrite (Mem.alloc_result m1 lo hi m1' b); auto.
      intros cu Hcu.
      eapply romatch_exten; eauto using romatch_alloc, mmatch_below.
      intros. symmetry. eapply alloc_bc_glob; eauto.
    - intros x. cbn. destruct eq_block; eauto. discriminate.
  }
  exists (vaextw se (alloc_bc b bc) m1' H1). split.
  - constructor; cbn; auto.
    + rewrite (Mem.alloc_result m1 lo hi m1' b); auto.
      intros. destruct eq_block; auto. subst.
      apply freshness in H2. inv H2.
    + rewrite (Mem.support_alloc m1 lo hi m1' b); auto.
    + intros.
      erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
  - rewrite Hm2'. repeat rstep.
    + constructor.
      edestruct (Mem.alloc_extends m1 m2 lo hi b m1' lo hi); eauto; extlia.
    + red. cbn. unfold inj_of_bc. cbn.
      rewrite pred_dec_true; reflexivity.
Qed.

(** Free *)
Next Obligation.
  intros w m1 m2 Hm p p' Hptr. destruct Hm.
  assert (p = p') as Hp by (apply coreflexivity; rauto). destruct Hp.
  destruct p as [[b lo] hi]. cbn in *.
  destruct (Mem.free m1) as [m1' | ] eqn:Hm1'; [ | constructor].
  edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  assert (H' : vaext_wf se bc m1').
  {
    destruct H.
    constructor; auto.
    + eapply mmatch_free; eauto.
    + intros cu Hcu. eapply romatch_free; eauto.
  }
  exists (vaextw _ _ _ H'). split.
  - constructor; cbn; auto.
    + rewrite (Mem.support_free m1 b lo hi m1'); eauto.
    + intros. red in Hptr; cbn in Hptr.
      destruct (eq_block b0 b); subst.
      * inv Hptr. inv H6. unfold inj_of_bc in H7. rewrite H2 in H7. discriminate.
      * eapply Mem.loadbytes_free_2; eauto.
  - constructor; auto.
Qed.

Lemma vaext_wf_inj se bc m:
  vaext_wf se bc m ->
  Mem.inject (inj_of_bc bc) m m.
Proof.
  destruct 1.
  eapply mmatch_inj; eauto.
  eapply mmatch_below; eauto.
Qed.

Ltac dest_inj_of_bc :=
  repeat
    match goal with
    | H: inj_of_bc _ _ = Some _ |- _ =>
      apply inj_of_bc_inv in H; destruct H as (? & ? & ?)
    end.

(** Load *)
Next Obligation.
  intros _ chunk _ _ [se bc m1 m2 H Hm] p p' Hp.
  assert (p = p') as Hp' by (eapply coreflexivity; rauto). destruct Hp'.
  destruct p as [b ofs]. cbn.
  destruct (Mem.load chunk m1) as [v1 | ] eqn:Hv1; [ | constructor].
  exploit vaext_wf_inj; eauto. intros Hm1.
  inv Hp. cbn in *.
  assert (delta = 0) by omega. subst delta.

  assert (Hinj: Mem.inject (inj_of_bc bc) m1 m2).
  { eapply Mem.inject_extends_compose; eauto. }
  clear Hm1.
  edestruct Mem.load_inject as (v2 & Hv2 & Hvinj); eauto.

  rewrite Hv2. constructor.
  assumption.
Qed.

(** Store *)
Next Obligation.
  intros sew chunk m1 m2 Hm p p' Hptr v1 v2 Hv.
  assert (p = p') as Hp' by (eapply coreflexivity; rauto). destruct Hp'.
  destruct p as [b ofs]. cbn.
  destruct (Mem.store chunk m1) as [m1' | ] eqn:Hm1'; try rauto.
  inv Hm. inv Hptr.
  assert (delta = 0) by omega. subst delta.
  unfold k1.

  exploit vaext_wf_inj; eauto. intros Hm1.
  assert (Hinj: Mem.inject (inj_of_bc bc) m1 m2).
  { eapply Mem.inject_extends_compose; eauto. }
  clear Hm1.
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hvinj); eauto.

  rewrite Hm2'.
  constructor.
  unfold klr_diam.

  assert (H' : vaext_wf se bc m1').
  {
    destruct H.
    constructor; auto.
    - eapply mmatch_inj_top; eauto.
    - intros cu Hcu. eapply romatch_store; eauto.
  }

  exists (vaextw _ _ _ H'). split.
  - constructor; cbn; auto.
    + apply Mem.support_store in Hm1'. rewrite Hm1'. eauto.
    + intros.
      destruct (eq_block b0 b); subst.
      * dest_inj_of_bc. cbn in H2. contradiction.
      * rewrite <- H7. symmetry.
        eapply Mem.loadbytes_store_other; eauto.
  - constructor; auto.
    assert (Hlessdef: Val.lessdef v1 v2).
    { unfold klr_pullw in Hv. cbn in Hv.
      rewrite <- val_inject_id.
      eapply Values.val_inject_incr.
      apply inj_of_bc_id. eassumption.
    }
    edestruct Mem.store_within_extends as (m2'' & Hm2'' & Hext); eauto.
    congruence.
Qed.

(** Loadbytes *)
Next Obligation.
  intros sew m1 m2 Hm [b ofs] [b2 ofs2] Hptr n. inv Hm.
  inv Hptr.

  generalize H2.
  dest_inj_of_bc.
  subst b2 delta.
  intros Hbc.

  unfold k1. cbn.
  destruct (Mem.loadbytes m1 b ofs n) as [bytes1 | ] eqn:Hbytes1; [ | constructor].
  exploit vaext_wf_inj; eauto. intros Hm1.
  assert (Hinj: Mem.inject (inj_of_bc bc) m1 m2).
  { eapply Mem.inject_extends_compose; eauto. }
  clear Hm1.
  edestruct Mem.loadbytes_inject as (bytes2 & Hbytes2 & Hinjbytes); eauto.
  rewrite Hbytes2.
  constructor.
  apply list_forall2_rel. assumption.
Qed.

(** Storebytes *)
Next Obligation.
  intros vaw m1 m2 Hm p p' Hptr bytes1 bytes2 Hbytes. inv Hm. cbn.
  assert (p = p') as Hp' by (eapply coreflexivity; rauto). destruct Hp'.
  destruct p as [b ofs]. cbn.
  destruct (Mem.storebytes m1 b ofs bytes1) as [m1' | ] eqn:Hm1'; [|constructor].
  unfold k1.

  exploit vaext_wf_inj; eauto. intros Hm1.
  assert (Hinj: Mem.inject (inj_of_bc bc) m1 m2).
  { eapply Mem.inject_extends_compose; eauto. }
  clear Hm1.

  unfold k1, klr_pullw in Hbytes.
  cbn in Hbytes.
  apply list_rel_forall2 in Hbytes.
  assert (Hbc: inj_of_bc bc b = Some (b, 0)).
  { destruct Hptr as [Hptr | Hptr].
    - inv Hptr. cbn in H2.
      replace delta with 0 in H2 by omega. auto.
    - inv Hptr.
      rewrite H1 in H2.
      inv H3. cbn in H5.
      inv H1. inv H2.
      unfold inj_of_bc in H5. unfold inj_of_bc.
      destruct (bc b); inv H5; reflexivity.
  }
  edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hinj'); eauto.
  rewrite Z.add_0_r in Hm2'. rewrite Hm2'.
  constructor.

  assert (H' : vaext_wf se bc m1').
  {
    destruct H.
    constructor; auto.
    - eapply mmatch_inj_top; eauto.
    - intros cu Hcu. eapply romatch_storebytes; eauto.
  }

  exists (vaextw _ _ _ H'). split.
  - constructor; cbn; auto.
    + apply Mem.support_storebytes in Hm1'. rewrite Hm1'. eauto.
    + intros.
      destruct (eq_block b0 b); subst.
      * dest_inj_of_bc. contradiction.
      * rewrite <- H5. symmetry.
        eapply Mem.loadbytes_storebytes_other; eauto.
  - constructor; auto.
    assert (Hlessdef: list_forall2 memval_lessdef bytes1 bytes2).
    { eapply list_forall2_imply. eassumption.
      intros v1 v2 Hv1 Hv2 Hvinj.
      eapply memval_inject_incr; eauto.
      apply inj_of_bc_id.
    }
    edestruct Mem.storebytes_within_extends as (m2'' & Hm2'' & Hext); eauto.
    congruence.
Qed.

(** Perm *)
Next Obligation.
  intros sew m1 m2 Hm. inv Hm.
  intros p p' Hptr P perm.
  assert (p = p') as Hp' by (eapply coreflexivity; rauto). destruct Hp'.
  destruct p as [b ofs].
  exact (Mem.perm_extends _ _ _ _ _ _ H4).
Qed.

(** Valid block *)
Next Obligation.
  intros sew m1 m2 Hm. inv Hm.
  intros b b' Hb.
  assert (b = b') as Hb' by (eapply coreflexivity; rauto). destruct Hb'.
  apply Mem.valid_block_extends.
  auto.
Qed.

(** No overlap *)
Next Obligation.
  inv H.
  cbn.
  left.
  dest_inj_of_bc. congruence.
Qed.

(** Representable *)
Next Obligation.
  inv H.
  dest_inj_of_bc. omega.
Qed.

(** Aligned *)
Next Obligation.
  inv H.
  dest_inj_of_bc.
  subst delta.
  rewrite Z.add_0_r.
  assumption.
Qed.

(** Disjoint or Equal *)
Next Obligation.
  inv H.
  dest_inj_of_bc.
  destruct H5 as [Hb | Hofs]; [left | right]. congruence.
  destruct Hofs as [Hofs | Hofs]; [left | right]. congruence.
  destruct Hofs as [Hofs | Hofs]; [left | right]. omega.
  omega.
Qed.

(** Perm inv *)
Next Obligation.
  inv H.
  inv H0.
  dest_inj_of_bc. subst. rewrite Z.add_0_r in H1.
  cbn in H.
  eapply Mem.mext_perm_inv in H1; eauto.
Qed.

(** sup include *)
Next Obligation.
  inv H. destruct H0 as (?&?&?). inv H0.
  inv H6. inv H9. rewrite mext_sup, mext_sup0. reflexivity.
Qed.

(** * Other properties *)

(** ** Connection with [vamatch] *)

Require Import Invariant.

Lemma vmatch_list_inj_top bc vargs1 vargs2 v:
  Val.inject_list (inj_of_bc bc) vargs1 vargs2 ->
  In v vargs1 ->
  vmatch bc v Vtop.
Proof.
  induction 1; destruct 1; eauto.
  subst. eapply vmatch_inj_top; eauto.
Qed.

Lemma val_inject_lessdef_list_compose f v1 v2 v3:
  Val.inject_list f v1 v2 ->
  Val.lessdef_list v2 v3 ->
  Val.inject_list f v1 v3.
Proof.
  intros Hv12. revert v3.
  induction Hv12; inversion 1; subst; constructor; eauto.
  eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

Lemma vaext_va_ext:
  cceqv (cc_c vaext) (vamatch @ cc_c ext).
Proof.
  split.
  - intros w se1 se2 q1 q2 Hse Hq.
    destruct Hq. destruct Hse. cbn in * |- . inv H1. destruct H12.
    exists (se, vaw se bc m1, tt). cbn. repeat apply conj; auto using rel_inv_intro.
    + eexists; split; constructor; cbn; auto.
      * constructor; eauto using vmatch_list_inj_top, vmatch_inj_top.
      * eapply val_inject_incr. apply inj_of_bc_id. eauto.
      * eapply val_inject_list_incr. apply inj_of_bc_id. eauto.
    + intros r1 r2 (ri & Hr1i & Hri2). destruct Hr1i, Hri2 as ([ ] & _ & ?).
      destruct H1. inv H5. cbn in *.
      assert (Hw' : vaext_wf se bc' m') by (constructor; auto).
      exists (vaextw se bc' m' Hw'). split.
      * constructor; auto.
      * constructor; cbn; auto.
        -- apply val_inject_id in H18.
           eapply Mem.val_inject_lessdef_compose; eauto.
           eapply vmatch_inj; eauto.
        -- constructor; auto.
  - intros [[se1 w] [ ]] se se2 q1 q2 [Hse1i Hsei2] (qi & Hq1i & Hqi2).
    destruct Hse1i. destruct Hsei2. destruct Hqi2. inv Hq1i. cbn in * |- .
    destruct w as [xse bc xm]. cbn in * |- . inv H4.
    assert (Hw: vaext_wf se bc m1) by (constructor; auto).
    exists (vaextw _ _ _ Hw). cbn. repeat apply conj.
    + constructor; auto.
    + constructor; cbn; auto.
      * apply val_inject_id in H0.
        eapply Mem.val_inject_lessdef_compose; eauto.
        eapply vmatch_inj; eauto.
      * apply val_inject_list_lessdef in H1.
        eapply val_inject_lessdef_list_compose; eauto.
        clear - H11.
        induction vargs1; constructor; eauto.
        -- eapply vmatch_inj. eapply H11. cbn. auto.
        -- eapply IHvargs1. intros. eapply H11. cbn. auto.
      * constructor; auto.
    + intros r1 r2 ([se' bc' m1' Hwf] & Hw' & Hr). destruct Hw'; cbn in *. subst se'.
      inv Hr. inv H4. destruct Hwf. cbn in *.
      eexists. split.
      * constructor. econstructor; eauto.
        eapply vmatch_inj_top; eauto.
      * exists tt. split; constructor.
        -- eapply val_inject_incr. apply inj_of_bc_id. eauto.
        -- cbn. auto.
Qed.
