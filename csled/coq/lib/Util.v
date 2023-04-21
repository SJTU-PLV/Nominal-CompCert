Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Import ListNotations.
Import Hex lib.Bits.


Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.




Lemma byte_eq_true: forall (A : Type) (x : byte) (a b : A),
    (if Byte.eq_dec x x then a else b) = a.
Proof.
  intros. destruct (Byte.eq_dec x x) eqn:EQ.
  - auto.
  - inversion EQ. elim n. auto.
Qed.

Lemma byte_eq_false: forall (A : Type) (x y : byte) (a b : A),
    x <> y -> (if Byte.eq_dec x y then a else b) = b.
Proof.
  intros. destruct (Byte.eq_dec x y) eqn:EQ.
  - rewrite e in H. elim H. auto.
  - auto.
Qed.


Ltac prove_byte_neq :=
  let EQ := fresh "EQ" in (
    match goal with
    | [ |- Byte.repr ?a <> Byte.repr ?b ] =>
      now (intro EQ; inversion EQ)
    end).

Ltac branch_byte_eq :=
  match goal with
  | [ |- context G [if Byte.eq_dec _ _ then _ else _]] =>
    idtac G;
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
    rewrite byte_eq_true
  end.


(* Ltac branch_byte_eq := *)
(*     match goal with *)
(*     | [ |- (if Byte.eq_dec _ _ then _ else _) = OK _] => *)
(*       repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]); *)
(*       rewrite byte_eq_true *)
(*     end. *)

(* Ltac prove_byte_and_neq := *)
(*   now (unfold Byte.and; *)
(*        repeat (rewrite Byte.unsigned_repr; [ |unfold Byte.max_unsigned; simpl; omega]); *)
(*        simpl; *)
(*        prove_byte_neq). *)

(* Ltac prove_opcode_neq := *)
(*   match goal with *)
(*   | [ EQ: encode_ireg ?rd = OK _ |- _ ] => *)
(*     now (case rd eqn:EQR; unfold encode_ireg in EQ; inversion EQ; simpl; unfold not; intros H; inversion H) *)
(*   end. *)

(* Ltac branch_byte_eq' := *)
(*   match goal with *)
(*   | |- (if Byte.eq_dec (Byte.and _ _) (Byte.repr _) then _ else _) = OK _ => *)
(*     rewrite byte_eq_false; [ branch_byte_eq' | prove_byte_and_neq ]     *)
(*   | |- (if Byte.eq_dec _ _ then _ else _) = OK _ => *)
(*     rewrite byte_eq_false; [ branch_byte_eq' | try prove_byte_neq; prove_opcode_neq ] *)
(*   | |- (if Byte.eq_dec ?a ?a then _ else _) = OK _ => *)
(*     rewrite byte_eq_true *)
(*   | _ => idtac *)
(*   end. *)

