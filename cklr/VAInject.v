Require Import Axioms.
Require Import Events.
Require Import CallconvAlgebra.
Require Import Invariant.
Require Import CKLR.
Require Import Inject.
Require Import ValueAnalysis.
Require Import ValueDomain.

Unset Program Cases.


(** * Preliminaries *)

Program Definition bc_of_symtbl (se: Genv.symtbl) :=
  {|
    bc_img b :=
      match Genv.invert_symbol se b with
        | Some id => BCglob id
        | None => BCinvalid
      end
  |}.
Next Obligation.
  destruct Genv.invert_symbol; discriminate.
Qed.
Next Obligation.
  destruct (Genv.invert_symbol se b1) eqn:Hb1; inv H.
  destruct (Genv.invert_symbol se b2) eqn:Hb2; inv H0.
  apply Genv.invert_find_symbol in Hb1.
  apply Genv.invert_find_symbol in Hb2.
  congruence.
Qed.

Lemma bc_of_symtbl_below se thr:
  Mem.sup_include (Genv.genv_sup se) thr ->
  bc_below (bc_of_symtbl se) thr.
Proof.
  intros Hthr b. cbn.
  destruct Genv.invert_symbol eqn:Hb; try congruence. intros _.
  eapply Mem.sup_include_trans; eauto.
  apply Genv.invert_find_symbol in Hb.
  eapply Genv.genv_symb_range; eauto.
Qed.


(** * CKLR definition *)

Inductive vainj_mem : klr (Genv.symtbl * world inj) mem mem :=
  vainj_mem_intro se w m1 m2:
    Mem.sup_include (Genv.genv_sup se) (Mem.support m1) ->
    romatch_all se (bc_of_symtbl se) m1 ->
    match_mem inj w m1 m2 ->
    vainj_mem (se, w) m1 m2.

Program Definition vainj :=
  {|
    world := Genv.symtbl * world inj;
    wacc := eq * wacc inj;
    mi '(se, w) := mi inj w;
    match_stbls '(se, w) se1 se2 := se = se1 /\ match_stbls inj w se1 se2;
    match_mem := vainj_mem;
  |}.

(** Monotonicity of injections *)
Next Obligation.
  intros [se w] [se' w'] [Hse' Hw]. cbn in *. destruct Hse'. rauto.
Qed.

(** Acc separated *)
Next Obligation.
  intros b1 b2 delta Hw Hw'.
  inv H.
  destruct H0 as [eq_s Hinj]. cbn in eq_s, Hinj. subst s0.
  inv Hinj. inv H7. cbn in *.
  eapply H0; eauto.
Qed.

(** Symbol table stuff *)
Next Obligation.
  intros [se w] [se' w'] [Hse' Hw]. cbn in *. destruct Hse'.
  intros se1 se2 [Hse1 Hse]. split; auto. rauto.
Qed.
Next Obligation.
  intros se1 se2 [Hse1 ?]. subst.
  eapply (match_stbls_proj inj); auto.
Qed.
Next Obligation.
  inv H0.
  eapply (match_stbls_support inj); eauto.
Qed.

(** Alloc *)
Next Obligation.
  intros x m1 m2 H lo hi. inv H.
  edestruct (cklr_alloc inj w m1 m2 H2) as (w' & Hw' & Hm' & Hb).
  exists (se, w'). split; [cbn; rauto | ].
  repeat apply conj; eauto. constructor; eauto.
  - intros cu Hcu.
    eapply romatch_alloc; eauto using surjective_pairing, bc_of_symtbl_below.
Qed.

(** Free *)
Next Obligation.
  intros x m1 m2 H [[b1 lo1] hi1] [[b2 lo2] hi2] Hptr. inv H. cbn. rstep.
  destruct (Mem.free m1) as [m1' | ] eqn:Hm1'; try constructor.
  generalize Hm1'. transport Hm1'. intro. rewrite H. repeat rstep.
  exists (se, w'). split; auto. rauto.
  constructor; eauto.
  - erewrite (Mem.support_free _ _ _ _ m1'); eauto.
  - intros cu Hcu.
    eapply romatch_free; eauto.
Qed.

(** Load *)
Next Obligation.
  intros sew chunk m1 m2 Hm. inv Hm.
  eapply (cklr_load inj); eauto.
Qed.

(** Store *)
Next Obligation.
  intros sew chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv. inv Hm. cbn.
  destruct (Mem.store chunk m1) as [m1' | ] eqn:Hm1'; try rauto.
  generalize Hm1'. transport Hm1'. intro. rewrite H2. constructor.
  exists (se, w'). split; [rauto | ].
  constructor; eauto.
  - erewrite Mem.support_store; eauto.
  - intros cu Hcu.
    eapply romatch_store; eauto.
Qed.

(** Loadbytes *)
Next Obligation.
  intros sew m1 m2 Hm. inv Hm.
  eapply (cklr_loadbytes inj); eauto.
Qed.

(** Storebytes *)
Next Obligation.
  intros vaw m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr bytes1 bytes2 Hbytes. inv Hm. cbn.
  destruct (Mem.storebytes m1 b1 ofs1 bytes1) as [m1' | ] eqn:Hm1'; try rauto.
  generalize Hm1'. transport Hm1'. intro. rewrite H2. constructor.
  exists (se, w'). split; [rauto | ].
  constructor; eauto.
  - erewrite Mem.support_storebytes; eauto.
  - intros cu Hcu.
    eapply romatch_storebytes; eauto.
Qed.

(** Perm *)
Next Obligation.
  intros sew m1 m2 Hm. inv Hm.
  eapply (cklr_perm inj); eauto.
Qed.

(** Valid block *)
Next Obligation.
  intros sew m1 m2 Hm. inv Hm.
  eapply (cklr_valid_block inj); eauto.
Qed.

(** No overlap *)
Next Obligation.
  inv H. eapply (cklr_no_overlap inj); eauto.
Qed.

(** Representable *)
Next Obligation.
  inv H. eapply (cklr_representable inj); eauto.
Qed.

(** *)
Next Obligation.
  inv H. eapply (cklr_aligned_area_inject inj); eauto.
Qed.

(** *)
Next Obligation.
  inv H. eapply (cklr_disjoint_or_equal_inject inj); eauto.
Qed.

(** *)
Next Obligation.
  inv H. eapply (cklr_perm_inv inj); eauto.
Qed.

Next Obligation.
  inv H. eapply (cklr_sup_include inj); eauto.
  destruct H0 as (w' & Hw' & Hm). inv Hm.
  eexists. split. apply Hw'. auto.
Qed.

(** * Correspondance with [vamatch] *)

(** ** Block classification for an injection *)

Program Definition bc_of_inj (f: meminj) (se: Genv.symtbl) :=
  {|
    bc_img b :=
      if f b then
        match Genv.invert_symbol se b with
        | Some id => BCglob id
        | None => BCother
        end
      else
        BCinvalid
  |}.
Next Obligation.
  destruct (f b1); try discriminate.
  destruct Genv.invert_symbol; discriminate.
Qed.
Next Obligation.
  destruct (f b1); try discriminate.
  destruct (f b2); try discriminate.
  destruct (Genv.invert_symbol se b1) eqn:Hb1; inv H.
  destruct (Genv.invert_symbol se b2) eqn:Hb2; inv H0.
  apply Genv.invert_find_symbol in Hb1.
  apply Genv.invert_find_symbol in Hb2.
  congruence.
Qed.

Lemma bc_of_symtbl_inj f se1 se2:
  Genv.match_stbls f se1 se2 ->
  bc_incr (bc_of_symtbl se1) (bc_of_inj f se1).
Proof.
  intros Hse b Hb. cbn in *.
  destruct Genv.invert_symbol eqn:H; try congruence.
  apply Genv.invert_find_symbol in H.
  edestruct @Genv.find_symbol_match as (tb & Htb & _); eauto.
  rewrite Htb. auto.
Qed.

Lemma bc_of_symtbl_inj_glob f se b id:
  bc_of_inj f se b = BCglob id ->
  bc_of_symtbl se b = BCglob id.
Proof.
  unfold bc_of_inj, bc_of_symtbl; cbn.
  destruct f; try discriminate.
  destruct Genv.invert_symbol; congruence.
Qed.

Lemma bc_of_inj_genv_match f se1 se2:
  Genv.match_stbls f se1 se2 ->
  genv_match (bc_of_inj f se1) se1.
Proof.
  intros Hse. split.
  - intros id b1. split.
    + intros Hb1.
      edestruct @Genv.find_symbol_match as (b2 & Hb12 & Hb2); eauto.
      apply Genv.find_invert_symbol in Hb1. cbn.
      rewrite Hb12, Hb1. auto.
    + cbn.
      destruct (f b1) eqn:Hb; try discriminate.
      destruct Genv.invert_symbol eqn:Hid; try discriminate.
      intro. apply Genv.invert_find_symbol. congruence.
  - intros b1 Hb1. cbn.
    eapply Genv.mge_dom in Hb1 as [b2 Hb]; eauto. rewrite Hb.
    destruct Genv.invert_symbol; split; discriminate.
Qed.

Lemma bc_of_inj_pmatch f se1 b1 ofs1 v2:
  Val.inject f (Vptr b1 ofs1) v2 ->
  pmatch (bc_of_inj f se1) b1 ofs1 Ptop.
Proof.
  inversion 1; subst.
  constructor. cbn.
  rewrite H2.
  destruct Genv.invert_symbol; discriminate.
Qed.

Lemma bc_of_inj_vmatch f se1 v1 v2:
  Val.inject f v1 v2 ->
  vmatch (bc_of_inj f se1) v1 Vtop.
Proof.
  destruct v1; constructor.
  eapply bc_of_inj_pmatch; eauto.
Qed.

Lemma bc_of_inj_args_vmatch f se1 vargs1 vargs2:
  Val.inject_list f vargs1 vargs2 ->
  forall v, In v vargs1 -> vmatch (bc_of_inj f se1) v Vtop.
Proof.
  induction 1 as [ | v1 v2 vargs1 vargs2 Hv IH]; cbn.
  - contradiction.
  - intros v1' [Hv1' | Hv1']; auto. subst v1'.
    eapply bc_of_inj_vmatch; eauto.
Qed.

Lemma bc_of_inj_smatch f se1 m1 m2 b1 b2 delta:
  Mem.inject f m1 m2 ->
  f b1 = Some (b2, delta) ->
  smatch (bc_of_inj f se1) m1 b1 Ptop.
Proof.
  intros Hm Hb.
  split.
  + intros chunk ofs v1 Hv1.
    edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
    eapply bc_of_inj_vmatch; eauto.
  + intros ofs1 b1' ofs1' q i H.
    edestruct Mem.loadbytes_inject as (bytes2 & Hbytes2 & Hv'); eauto.
    inv Hv'. inv H4. inv H2.
    eapply bc_of_inj_pmatch; eauto.
Qed.

Lemma bc_of_inj_mmatch f se1 m1 m2:
  Mem.inject f m1 m2 ->
  mmatch (bc_of_inj f se1) m1 mtop.
Proof.
  intros Hm. split.
  - intros b1 Hb1. cbn in *.
    destruct (f b1) as [[b2 delta] | ]; try discriminate.
    destruct Genv.invert_symbol; discriminate.
  - intros id ab b1 Hb1 H. cbn in *.
    rewrite Maps.PTree.gempty in H. discriminate.
  - intros b1 Hb1stk Hb1inv. cbn in *.
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply bc_of_inj_smatch; eauto.
  - intros b1 Hb1. cbn in *.
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply bc_of_inj_smatch; eauto.
  - intros b1 Hb1. cbn in *.    
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma bc_of_inj_nostack f se1:
  bc_nostack (bc_of_inj f se1).
Proof.
  intros b. cbn.
  destruct f; try congruence.
  destruct Genv.invert_symbol; congruence.
Qed.

(** ** Expanding [vainj] *)

(** Note: this only works in this direction; in the other there is no
  guarantee that the block classification used by [vamatch] and the
  injection used by [cc_c inj] are consistent. *)

Lemma vainj_va_inj:
  ccref (cc_c vainj) (vamatch @ cc_c inj).
Proof.
  intros sew se1 se2 q1 q2 Hse Hq.
  destruct Hq. inv H1. inv H5. destruct Hse. subst. cbn in * |- .
  eexists (se1, vaw se1 (bc_of_inj f se1) m1, injw f _ _). cbn.
  repeat apply conj; eauto 10 using rel_inv_intro.
  - eexists. split.
    + inv H6. cbn in *.
      constructor. constructor.
      * eapply bc_of_inj_genv_match; eauto.
      * eapply bc_of_inj_vmatch; eauto.
      * eapply bc_of_inj_args_vmatch; eauto.
      * eapply bc_of_inj_mmatch; eauto.
      * eapply bc_of_inj_nostack; eauto.
      * intros cu Hcu b id ab Hid Hab.
        edestruct H4 as (? & ? & ?); eauto using bc_of_symtbl_inj_glob.
        intuition auto.
        eapply bmatch_incr; eauto using bc_of_symtbl_inj.
    + constructor; cbn; auto.
  - intros r1 r2 (ri & Hr1i & w' & Hw' & Hri2).
    exists (se1, w'). split.
    + constructor; auto.
    + destruct Hr1i. destruct Hri2. inv Hw'. inv H5. inv H8. cbn in *.
      constructor; cbn; auto.
      constructor; cbn; auto.
      * eauto.
      * clear - H11 H18 H17 H6. inv H6. cbn in *.
        intros cu Hcu. eapply romatch_exten; eauto. intros b id.
        destruct H17 as [Hglob Hdef]. rewrite <- Hglob. cbn. clear.
        split.
        ++ intros H. destruct Genv.invert_symbol eqn:Hb; inv H.
           apply Genv.invert_find_symbol; auto.
        ++ intros Hb. apply Genv.find_invert_symbol in Hb. rewrite Hb.
           reflexivity.
Qed.


(** * Other properties *)

Require Import CKLRAlgebra.

Lemma vainj_vainj:
  subcklr vainj (vainj @ vainj).
Proof.
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [xse1 w m1 m2 Hnb Hro Hm].
  destruct Hse as [? Hse]. subst.
  destruct Hm as [f m1 m2 Hm].
  exists ((se1, injw (meminj_dom f) (Mem.support m1) (Mem.support m1)),
          (se1, injw f (Mem.support m1) (Mem.support m2))); simpl.
  repeat apply conj.
  - exists se1. repeat apply conj; eauto.
    inv Hse. econstructor; auto. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; constructor; cbn; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [[? w12'] [? w23']] m1' m3' (m2' & H12' & H23') [[? Hw12'] [? Hw23']].
    cbn in *. subst s s0.
    inversion H12' as [? w12'' ? ? ? ? H12'']; clear H12'; subst.
    destruct H12'' as [f12' m1' m2' Hm12'].
    inversion H23' as [? w23'' ? ? ? ? H23'']; clear H23'; subst.
    inversion H23'' as [f23' xm2' xm3' Hm23']. clear H23''; subst.
    inversion Hw12' as [? ? ? ? ? ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    eexists (se1, injw (compose_meminj f12' f23') _ _).
    repeat apply conj; cbn; auto.
    + constructor; auto. constructor; auto. eapply Mem.inject_compose; eauto.
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
Qed.

Lemma vainj_inj:
  subcklr vainj (vainj @ inj).
Proof.
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [xse1 w m1 m2 Hnb Hro Hm].
  destruct Hse as [? Hse]. subst.
  destruct Hm as [f m1 m2 Hm].
  exists ((se1, injw (meminj_dom f) (Mem.support m1) (Mem.support m1)),
          (injw f (Mem.support m1) (Mem.support m2))); simpl.
  repeat apply conj.
  - exists se1. repeat apply conj; eauto.
    inv Hse. econstructor; auto. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; constructor; cbn; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [[? w12'] w23'] m1' m3' (m2' & H12' & H23') [[? Hw12'] Hw23'].
    cbn in *. subst s.
    inversion H12' as [? w12'' ? ? ? ? H12'']; clear H12'; subst.
    destruct H12'' as [f12' m1' m2' Hm12'].
    inversion H23' as [f23' xm2' xm3' Hm23']. clear H23'; subst.
    inversion Hw12' as [? ? ? ? ? ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    eexists (se1, injw (compose_meminj f12' f23') _ _).
    repeat apply conj; cbn; auto.
    + constructor; auto. constructor; auto. eapply Mem.inject_compose; eauto.
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
Qed.
