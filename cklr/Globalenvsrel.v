Require Import Maps.
Require Import Valuesrel.
Require Import CKLR.
Require Export Globalenvs.


(** * Injections and global environements *)

Definition genv_valid {F V} R w (ge: Genv.t F V) :=
  meminj_wf (mi R w).

Lemma genv_valid_find_symbol {F V} R w (ge: Genv.t F V) i b:
  genv_valid R w ge ->
  Genv.find_symbol ge i = Some b ->
  block_inject_sameofs (mi R w) b b.
Proof.
  intros Hge H.
  unfold Genv.find_symbol in H.
  destruct (Genv.genv_defs ge)!i; inv H.
  apply Hge.
  unfold Mem.flat_inj.
  destruct Block.lt_dec; eauto.
  elim n; eapply Block.lt_glob_init.
Qed.

Lemma genv_valid_funct_ptr {F V} R w (ge: Genv.t F V) b f:
  genv_valid R w ge ->
  Genv.find_funct_ptr ge b = Some f ->
  block_inject_sameofs (mi R w) b b.
Proof.
  intros Hge Hf.
  unfold Genv.find_funct_ptr, Genv.find_def in Hf.
  destruct Block.ident_of eqn:Hb; try discriminate.
  apply Block.ident_of_inv in Hb. subst.
  apply Hge.
  unfold Mem.flat_inj.
  destruct Block.lt_dec; eauto.
  elim n; eapply Block.lt_glob_init.
Qed.

Lemma genv_valid_block_inject_eq {F V} R w (ge: Genv.t F V) b1 b2 f:
  genv_valid R w ge ->
  block_inject (mi R w) b1 b2 ->
  Genv.find_funct_ptr ge b1 = Some f ->
  b2 = b1.
Proof.
  intros Hge Hb H.
  eapply genv_valid_funct_ptr in H; eauto.
  red in H. destruct Hb. congruence.
Qed.

Lemma find_funct_ptr_transport {F V} R w (ge: Genv.t F V) b1 b2 f:
  genv_valid R w ge ->
  block_inject (mi R w) b1 b2 ->
  Genv.find_funct_ptr ge b1 = Some f ->
  Genv.find_funct_ptr ge b2 = Some f.
Proof.
  intros Hge Hb H.
  cut (b2 = b1); try congruence.
  eapply genv_valid_block_inject_eq; eauto.
Qed.

Global Instance find_funct_transfer {F V} R w (ge1 ge2: Genv.t F V) v1 v2 f:
  Transport
    (psat (genv_valid R w) * Val.inject (mi R w))%rel
    (ge1, v1)
    (ge2, v2)
    (Genv.find_funct ge1 v1 = Some f)
    (Genv.find_funct ge2 v2 = Some f /\
     exists b, v1 = Vptr b Ptrofs.zero).
Proof.
  repeat red.
  intros [Hge Hv].
  simpl in Hge, Hv.
  destruct Hge as [Hge].
  intros H.
  inversion Hv; subst; try discriminate. simpl in *.
  destruct (Ptrofs.eq_dec _ _); try discriminate. subst.
  rewrite Ptrofs.add_zero_l.
  assert (b2 = b1) by eauto using genv_valid_block_inject_eq; subst.
  pose proof (genv_valid_funct_ptr _ _ _ _ _ Hge H) as Hb. red in Hb.
  assert (delta = 0) by congruence; subst.
  change (Ptrofs.repr 0) with Ptrofs.zero.
  destruct Ptrofs.eq_dec; try congruence.
  eauto.
Qed.
