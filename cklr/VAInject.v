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

