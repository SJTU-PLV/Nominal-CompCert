Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Require Import Util Encode.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
(* Require Import Intersection. *)
Require Import Coq.Logic.Eqdep_dec.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Lemma len_exists: forall {A} l n,
    length l = S n
    ->exists (b:A) tail, l = b::tail /\ length tail = n.
Proof.
  intros. destruct l eqn:Hl.
  - simpl in H. congruence.
  - exists a,l0. auto.
Qed.

Ltac destr_list l :=
  let b:= fresh "b" in
  let tail := fresh "tail" in
  let HCons := fresh "HCons" in
  let HLTail := fresh "HLTail" in
  match goal with
  |[H: length l = 0 |- _] =>
   apply length_zero_iff_nil in H;
   subst l
  |[H: length l = ?n |- _]
   => generalize (len_exists l _ H);
     intros (b & tail & HCons & HLTail);
     subst l; try clear H;
     destr_list tail
  end.



Ltac destr_all_lists:=
  match goal with
  |[H: length ?x = _ |- context G[?x]]
   => destr_list x;try clear H
  end.

Lemma list_length1_destruct: forall A (l:list A),
    length l = 1 ->
    exists  b1, l=[b1].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length2_destruct: forall A (l:list A),
    length l = 2 ->
    exists  b1 b2, l=[b1;b2].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length3_destruct: forall A (l:list A),
    length l = 3 ->
    exists  b1 b2 b3, l=[b1;b2;b3].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length4_destruct: forall A (l:list A),
    length l = 4 ->
    exists  b1 b2 b3 b4, l=[b1;b2;b3;b4].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length5_destruct: forall A (l:list A),
    length l = 5 ->
    exists  b1 b2 b3 b4 b5, l=[b1;b2;b3;b4;b5].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length6_destruct: forall A (l:list A),
    length l = 6 ->
    exists  b1 b2 b3 b4 b5 b6, l=[b1;b2;b3;b4;b5;b6].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length7_destruct: forall A (l:list A),
    length l = 7 ->
    exists  b1 b2 b3 b4 b5 b6 b7, l=[b1;b2;b3;b4;b5;b6;b7].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length8_destruct: forall A (l:list A),
    length l = 8 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8, l=[b1;b2;b3;b4;b5;b6;b7;b8].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length9_destruct: forall A (l:list A),
    length l = 9 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length10_destruct: forall A (l:list A),
    length l = 10 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length11_destruct: forall A (l:list A),
    length l = 11 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length12_destruct: forall A (l:list A),
    length l = 12 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length13_destruct: forall A (l:list A),
    length l = 13 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length14_destruct: forall A (l:list A),
    length l = 14 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length15_destruct: forall A (l:list A),
    length l = 15 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length16_destruct: forall A (l:list A),
    length l = 16 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length17_destruct: forall A (l:list A),
    length l = 17 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length18_destruct: forall A (l:list A),
    length l = 18 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length19_destruct: forall A (l:list A),
    length l = 19 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length20_destruct: forall A (l:list A),
    length l = 20 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length21_destruct: forall A (l:list A),
    length l = 21 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length22_destruct: forall A (l:list A),
    length l = 22 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length23_destruct: forall A (l:list A),
    length l = 23 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length24_destruct: forall A (l:list A),
    length l = 24 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length25_destruct: forall A (l:list A),
    length l = 25 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length26_destruct: forall A (l:list A),
    length l = 26 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length27_destruct: forall A (l:list A),
    length l = 27 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length28_destruct: forall A (l:list A),
    length l = 28 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27;b28].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length29_destruct: forall A (l:list A),
    length l = 29 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27;b28;b29].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length30_destruct: forall A (l:list A),
    length l = 30 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27;b28;b29;b30].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length31_destruct: forall A (l:list A),
    length l = 31 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27;b28;b29;b30;b31].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
Lemma list_length32_destruct: forall A (l:list A),
    length l = 32 ->
    exists  b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32, l=[b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23;b24;b25;b26;b27;b28;b29;b30;b31;b32].
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.
