Require Import Coqlib.
Require Export Maps.

Require Import LogicalRelations.
Require Import OptionRel.


(** * Trees *)

Module TreeRel (T: TREE).

  (** The relator for trees takes any relation on [option _] as a parameter.
    Most likely, the source relation will have been constructed with
    [option_rel] or [option_le], depending on the desired behavior. *)

  Definition r {A B} (R: rel (option A) (option B)): rel (T.t A) (T.t B) :=
    fun t1 t2 => forall i, R (T.get i t1) (T.get i t2).

  Global Instance r_subrel A B:
    Monotonic (@r A B) (subrel ++> subrel).
  Proof.
    firstorder.
  Qed.

  Global Instance r_subrel_params:
    Params (@r) 3.

  (** Note that for empty trees to be related, the source relation has
    to contain ([@None A], [@None B]). To express this, we formulate
    the relational property of [T.empty] in terms of [option_rel ⊥]
    (the smallest relation which satisfies this criterion), and let
    the [subrel] infrastructure do the rest. *)

  Global Instance empty_rel:
    Monotonic (@T.empty) (forallr A B : ⊤, r (option_rel (@rel_bot A B))).
  Proof.
    intros A B _ i.
    rewrite !T.gempty.
    rauto.
  Qed.

  Global Instance get_rel:
    Monotonic (@T.get) (forallr R, - ==> r R ++> R).
  Proof.
    repeat rstep. eauto.
  Qed.

  Global Instance set_rel:
    Monotonic (@T.set) (forallr R, - ==> R @@ Some ++> r R ++> r R).
  Proof.
    intros A B R i x1 x2 Hx t1 t2 Ht j.
    destruct (T.elt_eq i j) as [Hij|Hij].
    - subst. rewrite !T.gss; eauto.
    - rewrite !T.gso; eauto.
  Qed.

  (** For [T.remove], we hit a similar issue as for [T.empty]: since
    [T.remove] will introduce a new [None], the codomain relation
    needs to be weakened. *)

  Global Instance remove_rel:
    Monotonic (@T.remove) (forallr R, - ==> r R ++> r (R \/ option_rel ⊥)).
  Proof.
    intros A B R i t1 t2 Ht j.
    destruct (T.elt_eq i j).
    - subst. rewrite !T.grs. rauto.
    - rewrite !T.gro by eauto. rauto.
  Qed.

  (** For [T.map], the [None] vs. [Some] situation is too complicated,
    so we provide properties hardcoded for [option_rel] and [option_le]. *)

  Global Instance map_option_rel:
    Monotonic
      (@T.map)
      (forallr RA, forallr RB,
        (- ==> RA ++> RB) ++> r (option_rel RA) ++> r (option_rel RB)).
  Proof.
    intros A1 A2 RA B1 B2 RB f g Hfg t1 t2 Ht i.
    rewrite !T.gmap.
    rauto.
  Qed.

  Global Instance map_option_le:
    Monotonic
      (@T.map)
      (forallr RA, forallr RB,
        (- ==> RA ++> RB) ++> r (option_le RA) ++> r (option_le RB)).
  Proof.
    intros A1 A2 RA B1 B2 RB f g Hfg t1 t2 Ht i.
    rewrite !T.gmap.
    rauto.
  Qed.

  (** For [T.combine], the requirement of [T.gcombine] that the
    function used should map [None]s to [None] can be expressed as the
    (perhaps somewhat obscure) relational property
    [option_rel ⊥ ++> option_rel ⊥ ++> option_rel ⊥]. *)

  Global Instance combine_rel:
    Monotonic
      (@T.combine)
      (forallr RA, forallr RB, forallr RC,
        ((RA ++> RB ++> RC) /\
         (option_rel ⊥ ++> option_rel ⊥ ++> option_rel ⊥)) ++>
        r RA ++> r RB ++> r RC).
  Proof.
    intros A1 A2 RA B1 B2 RB C1 C2 RC f g [Hfgb Hfg] tA1 tA2 HtA tB1 tB2 HtB i.
    assert (option_rel ⊥ (f None None) (g None None)) by rauto.
    rewrite !T.gcombine.
    - rauto.
    - destruct H; firstorder.
    - destruct H; firstorder.
  Qed.

End TreeRel.

Module PTreeRel := TreeRel(PTree).

(** This property for [elements] is derived from [elements_canonical_order],
  which is specific to [PTree]s. *)

Global Instance ptree_elements_rel:
  Monotonic
    (@PTree.elements)
    (forallr R, PTreeRel.r (option_rel R) ++> list_rel (eq * R)).
Proof.
  intros A B R tA tB Ht.
  cut (list_forall2 (eq * R)%rel (PTree.elements tA) (PTree.elements tB)).
  {
    induction 1; constructor; eauto.
  }
  eapply PTree.elements_canonical_order.
  - intros. transport H. eauto.
  - intros.
    assert (option_rel R (tA!i) (tB!i)) as Hi by rauto.
    destruct Hi; inv H. eauto.
Qed.


(** * Maps *)

Module MapRel (M: MAP).

  Definition r {A B} (R: rel A B): rel (M.t A) (M.t B) :=
    fun m1 m2 => forall i, R (M.get i m1) (M.get i m2).

  Global Instance r_subrel A B:
    Monotonic (@r A B) (subrel ++> subrel).
  Proof.
    firstorder.
  Qed.

  Global Instance r_subrel_params:
    Params (@r) 3.

  Global Instance init_rel:
    Monotonic (@M.init) (forallr R, R ++> r R).
  Proof.
    intros A B R x y H i.
    rewrite !M.gi.
    assumption.
  Qed.

  Global Instance get_rel:
    Monotonic (@M.get) (forallr R, - ==> r R ++> R).
  Proof.
    repeat rstep. eauto.
  Qed.

  Global Instance set_rel:
    Monotonic (@M.set) (forallr R, - ==> R ++> r R ++> r R).
  Proof.
    intros A B R i x y Hxy m1 m2 Hm j.
    destruct (M.elt_eq j i).
    - subst. rewrite !M.gss. assumption.
    - rewrite !M.gso by auto. eauto.
  Qed.

  Global Instance map_rel:
    Monotonic (@M.map) (forallr RA, forallr RB, (RA ++> RB) ++> r RA ++> r RB).
  Proof.
    intros A1 A2 RA B1 B2 RB f g Hfg m1 m2 Hm i.
    rewrite !M.gmap. rauto.
  Qed.
End MapRel.
