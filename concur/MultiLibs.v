Require Import Coqlib.
Require Import Integers.
Require Import Values Maps Memory AST.
Require Import Conventions1.
Module NatIndexed.
    Definition t := nat.

    Definition index (n : nat) : positive :=
      match n with
      |O => 1%positive
      |_ => 1 + Pos.of_nat n
      end.

    Definition index_rev (p:positive) : nat :=
      match p with
      |xH => O
      |_ => Pos.to_nat p -1
    end.

    Lemma t_positive_t : forall (n:nat), index_rev (index n) = n.
    Proof.
      intros.
      destruct (index n) eqn:Hn; unfold index_rev; destruct n; unfold index in *; lia.
    Qed.

    Lemma positive_t_positive : forall (p:positive), index(index_rev p) = p.
    Proof.
      intros. destruct (index_rev p) eqn:Hp; unfold index; destruct p; unfold index_rev in *; lia.
    Qed.

    Lemma index_inj : forall (x y : nat), index x = index y -> x = y.
    Proof.
      destruct x; destruct y; unfold index in *; lia.
    Qed.
    
    Definition eq := Nat.eq_dec.
End NatIndexed.

Module NatMap := IRMap(NatIndexed).

 (** * Definitions about the primitive pthread_create *)

Definition pthread_create_id := 1002%positive.
  

(* TODO: not quite sure to use Tlong or Tany64 here, we used Tlong for function pointer in the Client-Server example *)
(** int pthread_create (int * thread, void * (*start_routine) (void*), void* arg) *)
Definition pthread_create_sig := mksignature (Tlong :: Tlong :: Tlong :: nil) Tint cc_default.

  
Definition start_routine_sig := mksignature (Tlong :: nil) Tlong cc_default.


Axiom not_win : Archi.win64 = false.
  
(* the ptr to start_routine is in RSI, the pointer to its argument is in RDX *)
Lemma pthread_create_locs :
  loc_arguments pthread_create_sig = One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: One (Locations.R Machregs.DX) :: nil.
Proof.
  simpl. unfold pthread_create_sig. unfold loc_arguments.
  replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. simpl. reflexivity.
Qed.

(* the pointer to the arg of start_routine should be placed in RDI for new thread regs *)
Theorem start_routine_loc :
  loc_arguments start_routine_sig = One (Locations.R Machregs.DI) :: nil.
Proof.
  simpl.  simpl. unfold pthread_create_sig. unfold loc_arguments.
  replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. simpl. reflexivity.
Qed.

(* trans between Vint and nat *)

Definition int_to_nat (i : int) := Z.to_nat (Int.intval i).
  
Program Definition nat_to_int (n : nat) (nmax: (n < 1000)%nat) : int := Int.mkint (Z.of_nat n) _.
Next Obligation.
  change Int.modulus with 4294967296.
  split. lia. lia.
Qed.

(** * Definitions about the primitive yield *)

Definition yield_id := 1001%positive.
Definition yield_sig := mksignature nil Tvoid cc_default.
  

(** * Definitions about the primitive join *)

Definition pthread_join_id := 1003%positive.
(** int pthread_join (int * thread, void ** value_ptr) *)
Definition pthread_join_sig := mksignature (Tint :: Tlong :: nil) Tint cc_default.

Theorem pthread_join_locs :
  loc_arguments pthread_join_sig = One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: nil.
Proof.
  simpl. unfold pthread_create_sig. unfold loc_arguments.
  replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. simpl. reflexivity.
Qed.
