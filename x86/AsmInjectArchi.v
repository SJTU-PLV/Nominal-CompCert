(** * Properties about Injections at the Asm Level *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm AsmInject (* AsmFacts *).
Require Import LocalLib.
Import ListNotations.

(* Injection lemmas dependent to architecture *)

  Lemma val_inject_nextinstr_nf:
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr_nf sz rs1 r) (nextinstr_nf sz rs2 r).
  Proof.
    unfold nextinstr_nf.
    intros.
    apply val_inject_nextinstr; auto.
    intros.
    apply val_inject_undef_regs; auto.
  Qed.

Lemma nextinstr_nf_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr_nf sz rs1) (nextinstr_nf sz rs2).
Proof.
  intros. apply nextinstr_pres_inject.
  apply undef_regs_pres_inject. auto.
Qed.


Lemma compare_floats_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' ->
    regset_inject j (compare_floats v1 v2 rs) (compare_floats v1' v2' rs').
Proof.
  intros. unfold compare_floats, Asm.compare_floats.
  destruct v1, v2, v1', v2'; try solve_regset_inject.
Qed.

Lemma compare_floats32_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' ->
    regset_inject j (compare_floats32 v1 v2 rs) (compare_floats32 v1' v2' rs').
Proof.
  intros. unfold compare_floats32, Asm.compare_floats32.
  destruct v1, v2, v1', v2'; try solve_regset_inject.
Qed.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    Val.opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.


Lemma compare_ints_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j m m' ->
    regset_inject j rs rs' ->
    regset_inject j (compare_ints v1 v2 rs m) (compare_ints v1' v2' rs' m').
Proof.
  intros. unfold compare_ints, Asm.compare_ints.
  repeat apply regset_inject_expand; auto.
  - apply cmpu_inject; auto.
  - apply cmpu_inject; auto.
  - apply val_negative_inject. apply Val.sub_inject; auto.
  - apply sub_overflow_inject; auto.
Qed.

Lemma compare_longs_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j m m' ->
    regset_inject j rs rs' ->
    regset_inject j (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
Proof.
  intros. unfold compare_longs, Asm.compare_longs.
  repeat apply regset_inject_expand; auto.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Ceq); eauto. intros.
    inversion H3; subst.
    + simpl. auto.
    + simpl. apply Val.vofbool_inject.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Clt); eauto. intros.
    inversion H3; subst.
    + simpl. auto.
    + simpl. apply Val.vofbool_inject.
  - apply val_negativel_inject. apply Val.subl_inject; auto.
  - apply subl_overflow_inject; auto.
Qed.
