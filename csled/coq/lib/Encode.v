Require Import ZArith Integers Values.
Require Import Memdata Lists.List.
Require Import Ascii String.
Import ListNotations.

Definition encode_int_big (n:nat) (i: Z) : list byte :=
  rev (bytes_of_int n i).

Definition encode_int_little (n:nat) (i: Z) : list byte :=
  bytes_of_int n i.

Definition encode_int64 (i:Z) : list byte :=
  encode_int 8 i.

Definition encode_int32 (i:Z) : list byte :=
  encode_int 4 i.

Definition encode_int16 (i:Z) : list byte :=
  encode_int 2 i.

Definition zero_bytes (n:nat) : list byte :=
  List.map (fun _ => Byte.zero) (seq 1 n).

Definition ascii_to_byte (c: ascii) : byte :=
  Byte.repr (Z.of_nat (nat_of_ascii c)).

Fixpoint string_to_bytes (s:string) : list byte :=
  match s with
  | EmptyString => []
  | String c s' => (ascii_to_byte c) :: string_to_bytes s'
  end.

Notation "CB[ c ]" := (ascii_to_byte c) (right associativity) : string_byte_scope.
Notation "SB[ str ]" := (string_to_bytes str) (right associativity) : string_byte_scope.

Definition decode_int32 (lb: list byte) : Z :=
  decode_int lb.

Definition decode_int16 (lb: list byte) : Z :=
  decode_int lb.

Lemma decode_encode_int32 z :
  (decode_int32 (encode_int32 z) = z mod two_p (Z.of_nat 32))%Z.
Proof.
  unfold decode_int32, encode_int32.
  rewrite decode_encode_int. reflexivity.
Qed.

Lemma decode_encode_int16 z :
  (decode_int16 (encode_int16 z) = z mod two_p (Z.of_nat 16))%Z.
Proof.
  unfold decode_int16, encode_int16.
  rewrite decode_encode_int. reflexivity.
Qed.

Require Import Coqlib Errors List.
Local Open Scope error_monad_scope.
(* Local Open Scope hex_scope. *)
(* Local Open Scope bits_scope. *)



Fixpoint take_drop {A} n (l: list A) : res (list A * list A) :=
  match n, l with
  | O, l => OK ([], l)
  | S n, a::r =>
    do (a1,b1) <- take_drop n r ;
    OK (a::a1, b1)
  | S n, [] => Error (msg "take_drop: list too short")
  end.

Lemma take_drop_encode_int sz x l:
  take_drop sz (encode_int sz x ++ l) = OK (encode_int sz x, l).
Proof.
  generalize (encode_int_length sz x).
  generalize (encode_int sz x).
  induction sz; simpl; intros; eauto.
  - destruct l0; simpl in *; try congruence.
  - destruct l0; simpl in *; try congruence.
    rewrite IHsz. simpl. auto. congruence.
Qed.

Lemma take_drop_cons {A} x (l: list A):
  take_drop 1 (x :: l) = OK ([x], l).
Proof.
  reflexivity.
Qed.


Lemma take_drop_length {A} sz (l: list A):
  length l = sz ->
  take_drop sz l = OK (l, []).
Proof.
  revert l.
  induction sz; simpl; intros; eauto.
  - destruct l; simpl in *; try congruence.
  - destruct l; simpl in *; try congruence.
    rewrite IHsz. simpl. auto. congruence.
Qed.


Lemma take_drop_length_app {A} sz (l1 l2: list A):
  length l1 = sz ->
  take_drop sz (l1 ++ l2) = OK (l1, l2).
Proof.
  revert l1 l2.
  induction sz; simpl; intros; eauto.
  - destruct l1; simpl in *; try congruence.
  - destruct l1; simpl in *; try congruence.
    rewrite IHsz. simpl. auto. congruence.
Qed.


Lemma take_drop_length_2 :
  forall {A} z (l: list A) l1 l2,
    (z > 0)%nat ->
    take_drop z l = OK (l1, l2) ->
    (length l2 < length l)%nat.
Proof.
  induction z; simpl; intros; eauto. lia.
  destr_in H0. monadInv H0.
  destruct z.  simpl in *. inv EQ.  lia.
  apply IHz in EQ. simpl. lia. lia.
Qed.

