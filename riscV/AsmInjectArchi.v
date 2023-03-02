(** * Properties about Injections at the Asm Level *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm AsmInject.
Require Import LocalLib.
Import ListNotations.

(* Injection lemmas dependent to architecture *)

Lemma get0w_inject : forall rs1 rs2 r j,
    regset_inject j rs1 rs2 ->
    Val.inject j (get0w rs1 r) (get0w rs2 r).
Proof.
  intros. unfold get0w.
  destruct r;auto.
Qed.


Lemma get0l_inject : forall rs1 rs2 r j,
    regset_inject j rs1 rs2 ->
    Val.inject j (get0l rs1 r) (get0l rs2 r).
Proof.
  intros. unfold get0l.
  destruct r;auto.
Qed.
