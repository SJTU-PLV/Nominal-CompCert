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
  unfold Cop.sem_cast. repeat rstep; try
  (destruct ident_eq; repeat rstep).
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

Global Instance load_bitfield_match R w:
  Monotonic
    (@load_bitfield)
    (- ==> - ==> - ==> - ==> - ==> match_mem R w ++> Val.inject (mi R w) ++>
     set_le (Val.inject (mi R w))).
Proof.
  repeat rstep.
  intros v Hv.
  destruct Hv as [sz sg1 attr sg pos width m v' ? Hpos Hwidth Hpw Hsg1 Hload].
  transport Hload. inv H2.
  eexists; split; eauto.
  constructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @load_bitfield : typeclass_instances.

Global Instance store_bitfield_match R:
  Monotonic
    (@store_bitfield)
    (- ==> - ==> - ==> - ==> - ==>
     |= match_mem R ++> Val.inject @@[mi R] ++> Val.inject @@[mi R] ++>
     % k1 set_le (<> match_mem R * Val.inject @@ [mi R])).
Proof.
  repeat rstep.
  intros [v m] Hv.
  destruct Hv as [sz sg1 attr sg pos width m addr v n m' Hpos Hw Hpw Hsg1 Hload Hstore]. inv H1.
  transport Hload. inv H2.
  transport Hstore.
  eexists (_, _). cbn. split; [ | rauto].
  econstructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @store_bitfield : typeclass_instances.
