Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Valuesrel.
Require Import CKLR.
Require Import Ctypes.
Require Archi.
Require Import LogicalRelations.
Require Import OptionRel.
Require Export Cop.

(** * Relational properties *)

Global Instance bool_val_match R w:
  Monotonic
    (@Cop.bool_val)
    (Val.inject (mi R w) ++> - ==> match_mem R w ++> option_le eq).
Proof.
  unfold bool_val. rauto.
Qed.

Global Instance sem_switch_arg_inject f:
  Monotonic
    (@Cop.sem_switch_arg)
    (Val.inject f ++> - ==> option_le eq).
Proof.
  unfold Cop.sem_switch_arg. rauto.
Qed.

Global Instance sem_unary_operation_match R w:
  Monotonic
    (@Cop.sem_unary_operation)
    (- ==> Val.inject (mi R w) ++> - ==> match_mem R w ==>
     option_le (Val.inject (mi R w))).
Proof.
  unfold Cop.sem_unary_operation.
  unfold
    Cop.sem_notbool,
    Cop.sem_notint,
    Cop.sem_absfloat,
    Cop.sem_neg.
  repeat rstep.
  congruence.
Qed.

Global Instance sem_cast_match R w:
  Monotonic
    (@Cop.sem_cast)
    (Val.inject (mi R w) ++> - ==> - ==> match_mem R w ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold Cop.sem_cast. rauto.
Qed.

Global Instance sem_binarith_match R w:
  Monotonic
    (@Cop.sem_binarith)
    ((- ==> - ==> - ==> option_le (Val.inject (mi R w))) ++>
     (- ==> - ==> - ==> option_le (Val.inject (mi R w))) ++>
     (- ==> - ==> option_le (Val.inject (mi R w))) ++>
     (- ==> - ==> option_le (Val.inject (mi R w))) ++>
     Val.inject (mi R w) ++> - ==>
     Val.inject (mi R w) ++> - ==>
     match_mem R w ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold Cop.sem_binarith. rauto.
Qed.

Global Instance cmp_ptr_match R w:
  Related
    (@Cop.cmp_ptr)
    (@Cop.cmp_ptr)
    (match_mem R w ++> - ==> Val.inject (mi R w) ++> Val.inject (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold cmp_ptr. rauto.
Qed.

Global Instance sem_cmp_match R w:
  Monotonic
   (@Cop.sem_cmp)
   (- ==>
    Val.inject (mi R w) ++> - ==>
    Val.inject (mi R w) ++> - ==>
    match_mem R w ++>
    option_le (Val.inject (mi R w))).
Proof.
  unfold sem_cmp. rauto.
Qed.

Global Instance sem_shift_match R w:
  Monotonic
    (@Cop.sem_shift)
    (- ==>
     - ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject (mi R w) ++> - ==>
     option_le (Val.inject (mi R w))).
Proof.
  unfold Cop.sem_shift. rauto.
Qed.

Global Instance sem_binary_operation_match R w:
  Monotonic
    (@Cop.sem_binary_operation)
    (- ==> - ==>
     Val.inject (mi R w) ++> - ==>
     Val.inject (mi R w) ++> - ==>
     match_mem R w ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold Cop.sem_binary_operation.
  unfold
    Cop.sem_add,
    Cop.sem_add_ptr_int,
    Cop.sem_add_ptr_long,
    Cop.sem_sub,
    Cop.sem_mul,
    Cop.sem_div,
    Cop.sem_mod,
    Cop.sem_and,
    Cop.sem_or,
    Cop.sem_xor,
    Cop.sem_shl,
    Cop.sem_shr.
  repeat rstep; auto using ptrbits_inject_shift, ptrbits_inject_shift_sub.
  - destruct b4; try rauto.
    assert (Ptrofs.sub ofs1 ofs0 = Ptrofs.sub ofs2 ofs3).
    {
      subst.
      inv H2; inv H3.
      replace delta0 with delta in * by congruence.
      symmetry.
      apply Ptrofs.sub_shifted.
    }
    repeat rstep; congruence.
Qed.
