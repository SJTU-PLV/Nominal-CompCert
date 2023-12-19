Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import RustlightBase.

Definition paths := list place.

Lemma is_prefix_refl: forall p, is_prefix p p = true.
Admitted.


Lemma is_prefix_trans: forall p1 p2 p3, is_prefix p1 p2 = true -> is_prefix p2 p3 = true -> is_prefix p1 p3 = true.
Admitted.


Module LPaths <: SEMILATTICE.

  Definition t := paths.

  Definition bot : t := @nil place.
  
  Definition ge (l1 l2: t) : Prop :=
    forall p, In p l2 -> exists p', In p' l1 /\ is_prefix p' p = true.

  Definition eq (l1 l2: t) : Prop :=
    ge l1 l2 /\ ge l2 l1.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. 
    intros. red in H. intuition.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    intros. red in *. 
    intros. apply H0 in H1.
    destruct H1 as (p' & In' & Pre').
    apply H in In'.
    destruct In' as (p'' & In'' & Pre'').
    exists p''. split. auto.
    eapply is_prefix_trans;eauto.
  Qed.
        
  Lemma eq_refl: forall x, eq x x.
  Proof.
    intros. split;red;intros.
    - exists p. split;auto. apply is_prefix_refl.
    - exists p. split;auto. apply is_prefix_refl.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    intros. red in *. intuition.
  Qed.  

  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros. red in *. 
    destruct H, H0.
    split. 
    - eapply ge_trans;eauto.
    - eapply ge_trans;eauto.
  Qed.

  Definition exists_prefix (p: place) (l: t) :=
    filter (fun p' => is_prefix p' p) l.

  Fixpoint bge' (l1 l2: t) : bool :=
    match l2 with
    | nil => true
    | p :: l2' =>
        match exists_prefix p l1 with
        | nil => false
        | _ => bge' l1 l2'
        end
    end.
    
  Definition bge (l1 l2: t) : bool := bge' l1 l2.

  Lemma bge_correct: forall x y, bge x y = true -> ge x y.
    Admitted.

  Definition beq (l1 l2: t) : bool := bge l1 l2 && bge l2 l1.
 
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros. red. unfold beq in H.
    apply andb_true_iff in H. destruct H.
    split;apply bge_correct;auto.
  Qed.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    intros. red. unfold bot.
    intros. inversion H.
  Qed.

  Definition lub (l1 l2 : t) :=
    l1 ++ l2.
    
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    red. unfold lub. intros.
    exists p. split.
    eapply in_app. auto.
    apply is_prefix_refl.
  Qed.
    
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    red. unfold lub. intros.
    exists p. split.
    eapply in_app. auto.
    apply is_prefix_refl.
  Qed.
  
End LPaths.

Module PathMap := LPMap1(LPaths).
