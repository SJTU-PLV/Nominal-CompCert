Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import ZArith.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Values Memdata Memtype.
Require Import Asmgenproof0 Conventions1.

Lemma nextinstr_nf_pc: forall sz rs, nextinstr_nf sz rs PC = Val.offset_ptr (rs PC) sz.
Proof.
  unfold nextinstr_nf. simpl.
  intros. rewrite Asmgenproof0.nextinstr_pc. f_equal.
Qed.

Lemma nextinstr_rsp:
  forall sz rs,
    nextinstr sz rs RSP = rs RSP.
Proof.
  unfold nextinstr.
  intros; rewrite Pregmap.gso; congruence.
Qed.

Lemma nextinstr_nf_rsp:
  forall sz rs,
    nextinstr_nf sz rs RSP = rs RSP.
Proof.
  unfold nextinstr_nf.
  intros. rewrite nextinstr_rsp.
  rewrite Asmgenproof0.undef_regs_other; auto.
  simpl; intuition subst; congruence.
Qed.

Ltac simpl_regs_in H :=
  repeat first [ rewrite Pregmap.gso in H by congruence
               | rewrite Pregmap.gss in H
               | rewrite Asmgenproof0.nextinstr_pc in H
               | rewrite nextinstr_rsp in H
               | rewrite nextinstr_nf_rsp in H
               | rewrite nextinstr_nf_pc in H
               | rewrite Asmgenproof0.nextinstr_inv in H by congruence
               ].

Ltac simpl_regs :=
  repeat first [ rewrite Pregmap.gso by congruence
               | rewrite Pregmap.gss
               | rewrite Asmgenproof0.nextinstr_pc
               | rewrite nextinstr_rsp
               | rewrite nextinstr_nf_rsp
               | rewrite nextinstr_nf_pc
               | rewrite Asmgenproof0.nextinstr_inv by congruence
               ].


Lemma mod_divides:
  forall a b c,
    c <> 0 ->
    (a | c) ->
    (a | b) ->
    (a | b mod c).
Proof.
  intros.
  rewrite Zmod_eq_full.
  apply Z.divide_sub_r. auto.
  apply Z.divide_mul_r. auto. auto.
Qed.


Lemma div_unsigned_repr:
  forall a c,
    (c | a) ->
    (c | Ptrofs.modulus) ->
    (c | (Ptrofs.unsigned (Ptrofs.repr a))).
Proof.
  intros.
  rewrite Ptrofs.unsigned_repr_eq.
  apply mod_divides. vm_compute. congruence.
  auto. auto.
Qed.

Lemma div_ptr_add:
  forall a b c,
    (c | Ptrofs.unsigned a) ->
    (c | Ptrofs.unsigned b) ->
    (c | Ptrofs.modulus) ->
    (c | (Ptrofs.unsigned (Ptrofs.add a b))).
Proof.
  intros. apply div_unsigned_repr.
  apply Z.divide_add_r; auto. auto.
Qed.

Lemma align_Mptr_stack_limit:
  (align_chunk Mptr | Memory.max_stacksize).
Proof.
  transitivity 8.
  - unfold Mptr. destr; simpl. exists 1; lia. exists 2; lia.
  - unfold Memory.max_stacksize. econstructor. instantiate (1:=512). lia.
Qed.

Lemma align_Mptr_align8 z:
  (align_chunk Mptr | align z 8).
Proof.
  transitivity 8.
  - unfold Mptr. destr; simpl. exists 1; lia. exists 2; lia.
  - apply align_divides. lia.
Qed.

Lemma align_Mptr_modulus:
  (align_chunk Mptr | Ptrofs.modulus).
Proof.
  unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize, Mptr.
  apply Z.divide_gcd_iff. destr; simpl; lia.
  destr; simpl; vm_compute.
Qed.

Lemma nextinstr_eq:
  forall sz rs rs' r,
    rs r = rs' r ->
      nextinstr sz rs r = nextinstr sz rs' r.
Proof.
  unfold nextinstr. intros.
  setoid_rewrite Pregmap.gsspec. destr.
Qed.

Lemma set_reg_eq:
  forall (rs rs': regset) r dst,
    (r <> dst -> rs r = rs' r) ->
    forall v v' (EQ: v = v'),
      (rs # dst <- v) r = (rs' # dst <- v') r.
Proof.
  intros.
  setoid_rewrite Pregmap.gsspec. destr.
Qed.

Lemma undef_regs_eq:
  forall l (rs rs': regset) r,
    (~ In r l -> rs r = rs' r) ->
    undef_regs l rs r = undef_regs l rs' r.
Proof.
  induction l; simpl; intros; eauto.
  apply IHl. intros; apply set_reg_eq. intros; apply H. intuition. auto.
Qed.

Lemma nextinstr_nf_eq:
  forall sz rs rs' r,
    rs r = rs' r ->
    nextinstr_nf sz rs r = nextinstr_nf sz rs' r.
Proof.
  unfold nextinstr_nf. intros.
  apply nextinstr_eq.
  intros; apply undef_regs_eq. auto.
Qed.

Lemma set_res_eq:
  forall res rs rs' r,
    rs r = rs' r ->
    forall vres,
      set_res res vres rs r = set_res res vres rs' r.
Proof.
  induction res; simpl; intros; eauto.
  apply set_reg_eq; auto.
Qed.

Lemma set_pair_eq:
  forall res r rs rs',
    (~ In r (regs_of_rpair res) -> rs r = rs' r) ->
    forall vres,
      set_pair res vres rs r = set_pair res vres rs' r.
Proof.
  destruct res; simpl; intros; eauto.
  apply set_reg_eq; auto.
  intros; eapply H. intros [A|A]; congruence.
  intros; apply set_reg_eq; auto.
  intros; apply set_reg_eq; auto.
  intros; apply H. intuition congruence.
Qed.
(*
Lemma set_pair_no_rsp:
  forall p res rs,
    no_rsp_pair p ->
    set_pair p res rs RSP = rs RSP.
Proof.
  destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition.
Qed.
*)
Lemma preg_of_not_rsp:
  forall m x,
    preg_of m = x ->
    x <> RSP.
Proof.
  unfold preg_of. intros; subst.
  destruct m; congruence.
Qed.

Lemma rsp_not_destroyed_at_call:
  Asmgenproof0.preg_notin RSP destroyed_at_call.
Proof.
  unfold destroyed_at_call. apply Asmgenproof0.preg_notin_charact.
  intros. intro EQ; symmetry in EQ.
  apply  preg_of_not_rsp in EQ. congruence.
Qed.

Lemma pc_not_destroyed_builtin ef:
  Asmgenproof0.preg_notin PC (destroyed_by_builtin ef).
Proof.
  apply Asmgenproof0.preg_notin_charact.
  intros. unfold preg_of. destr.
Qed.

Lemma no_rsp_loc_external_result sg:
  no_rsp_pair (loc_external_result sg).
Proof.
  unfold loc_external_result.
  generalize (loc_result sg).
  induction r; simpl; intros; try split; apply Asmgenproof0.preg_of_not_SP.
Qed.

Lemma set_res_other:
  forall res vres rs r,
    ~ in_builtin_res res r ->
    set_res res vres rs r = rs r.
Proof.
  induction res; simpl; intros; eauto.
  rewrite Pregmap.gso; auto.
  rewrite IHres2. apply IHres1. intuition. intuition.
Qed.

Ltac regs_eq :=
  repeat
    match goal with
    | |- nextinstr _ _ ?r = nextinstr _ _ ?r => apply nextinstr_eq
    | |- nextinstr_nf _ _ ?r = nextinstr_nf _ _?r => apply nextinstr_nf_eq
    | |- undef_regs _ _ ?r = undef_regs _ _ ?r => apply undef_regs_eq; intros; eauto
    | |- _ # ?r0 <- ?v ?r = _ # ?r0 <- ?v' ?r => apply set_reg_eq; intros; eauto
    | H: forall r: preg, r <> RA -> ?rs1 r = ?rs2 r |- ?rs1 _ = ?rs2 _ => apply H; auto; congruence
    | |- _ => unfold compare_ints, compare_longs, compare_floats, compare_floats32
    end.
