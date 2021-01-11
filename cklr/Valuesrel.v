Require Export LogicalRelations.
Require Export KLR.
Require Export OptionRel.
Require Export BoolRel.

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Export Values.
Require Export Memdata.


(** * Injection relations *)

(** ** Coqrel support for [inject_incr] *)

(** CompCert's [inject_incr] can be expressed as [- ==> option_le eq]
  in coqrel, as illustrated by the following instance. *)

Global Instance inject_incr_option_le:
  Related inject_incr (- ==> option_le eq)%rel subrel.
Proof.
  intros f g Hfg b.
  destruct (f b) as [[b' ofs] | ] eqn:Hb; try constructor.
  apply Hfg in Hb.
  rewrite Hb. rauto.
Qed.

(** Note that the instance above is not sufficient to ensure that
  [inject_incr] properties can be used by the monotonicity
  tactic. This is because [subrel] is only looped in after [RElim] has
  been performed, but we only know how to do that with
  [(- ==> option_le eq)]. Hence the following instance: *)

Lemma inject_incr_relim (f g: meminj) (b1 b2: block) P Q:
  RElim (option_le eq) (f b1) (g b2) P Q ->
  RElim inject_incr f g (b1 = b2 /\ P) Q.
Proof.
  intros H Hfg [Hb HP].
  apply inject_incr_option_le in Hfg.
  relim Hfg; eauto.
Qed.

Hint Extern 1 (RElim inject_incr _ _ _ _) =>
  eapply inject_incr_relim : typeclass_instances.

Lemma inject_incr_rintro f g:
  RIntro (forall b, option_le eq (f b) (g b)) inject_incr f g.
Proof.
  intros H b b1' delta1 Hb1.
  specialize (H b).
  transport Hb1.
  congruence.
Qed.

(** ** Properties of existing relations *)

Global Instance val_inject_incr:
  Monotonic (@Val.inject) (inject_incr ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; econstructor; eauto.
Qed.

Global Instance memval_inject_incr:
  Monotonic (@memval_inject) (inject_incr ++> subrel).
Proof.
  intros w w' Hw x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.

Global Instance val_inject_refl:
  Reflexive (Val.inject inject_id).
Proof.
  intros v. destruct v; econstructor.
  - reflexivity.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

(** XXX normalization in coqrel would be best because it would make it
  possible for this to work in both directions. *)
Global Instance list_inject_subrel f:
  Related (list_rel (Val.inject f)) (Val.inject_list f) subrel.
Proof.
  induction 1; constructor; eauto.
Qed.

(** ** Complementary relations *)

(** *** Abstract pointers *)

(** Compcert usually passes pointers around as separate block and
  offset arguments. Since we can't relate those independently
  (because the offset shift is specific to each block), we instead
  relate (block, offset) pairs and use [rel_curry] to construct our
  [Monotonicity] relations.

  Relating pointers is complicated because of the interaction
  between the abstract [Z] offsets that are used by the memory model
  and the [ptrofs] concrete machine representations that are used to
  build [val]ues. The basic relation [ptr_inject] relates abstract
  pointers in the obvious way, while [ptrbits_inject] relates
  concrete pointers as is done in [Val.inject]. *)

Inductive ptr_inject (f: meminj): relation (block * Z) :=
  ptr_inject_intro b1 ofs1 b2 delta:
    f b1 = Some (b2, delta) ->
    ptr_inject f (b1, ofs1) (b2, ofs1 + delta).

Hint Constructors ptr_inject.

Global Instance ptr_inject_incr:
  Monotonic (@ptr_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
  transport Hb; subst.
  constructor; eauto.
Qed.

(** *** Machine pointers *)

(** For the machine integer version, we also make sure we can destruct
  [Val.inject] in terms of [ptrbits_inject]. *)

Inductive ptrbits_inject (f: meminj): relation (block * ptrofs) :=
  ptrbits_inject_intro b1 ofs1 b2 delta:
    f b1 = Some (b2, delta) ->
    ptrbits_inject f (b1, ofs1) (b2, Ptrofs.add ofs1 (Ptrofs.repr delta)).

Hint Constructors ptrbits_inject.

Global Instance ptrbits_inject_incr:
  Monotonic (@ptrbits_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 delta Hb].
  transport Hb; subst.
  constructor; eauto.
Qed.

Global Instance val_inject_rdestruct f:
  RDestruct
    (Val.inject f)
    (fun P =>
       (forall n, P (Vint n) (Vint n)) /\
       (forall n, P (Vlong n) (Vlong n)) /\
       (forall x, P (Vfloat x) (Vfloat x)) /\
       (forall x, P (Vsingle x) (Vsingle x)) /\
       (forall b1 ofs1 b2 ofs2,
         ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
         P (Vptr b1 ofs1) (Vptr b2 ofs2)) /\
       (forall v, P Vundef v)).
Proof.
  intros v1 v2 Hv P (Hint & Hlong & Hfloat & Hsingle & Hptr & Hundef).
  destruct Hv; eauto.
  eapply Hptr.
  subst.
  constructor; eauto.
Qed.

(** *** Address ranges *)

(** For [Mem.free] we need to relate a whole range of abstract
  pointers in the form of an [(ofs, lo, hi)] triple. *)

Inductive ptrrange_inject (f: meminj): relation (block * Z * Z) :=
  ptrrange_inject_intro b1 ofs1 b2 ofs2 sz:
    RIntro
      (ptr_inject f (b1, ofs1) (b2, ofs2))
      (ptrrange_inject f) (b1, ofs1, ofs1+sz) (b2, ofs2, ofs2+sz).

Hint Constructors ptrrange_inject.
Global Existing Instance ptrrange_inject_intro.

Global Instance ptrrange_inject_incr:
  Monotonic (@ptrrange_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp ptr1 ptr2 Hptr.
  destruct Hptr as [b1 ofs1 b2 ofs2 sz Hb].
  constructor; eauto.
  revert Hb.
  apply ptr_inject_incr.
  assumption.
Qed.

(** *** Blocks *)

(** For operations that manipulate blocks, we can use the two
  relations below: the weaker [match_block] relates two blocks
  according to [cklr_meminj], no matter what the offset shift
  is. The stronger [match_block_sameofs] only relates blocks that
  correspond to one another with no shift in offset. *)

Definition block_inject (f: meminj) b1 b2 :=
  exists delta, f b1 = Some (b2, delta).

Definition block_inject_sameofs (f: meminj) b1 b2 :=
  f b1 = Some (b2, 0%Z).

Hint Unfold block_inject.
Hint Unfold block_inject_sameofs.

Global Instance block_inject_incr:
  Monotonic (@block_inject) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 [delta Hb].
  transport Hb; subst.
  eexists; eauto.
Qed.

Global Instance block_inject_sameofs_incr:
  Monotonic (@block_inject_sameofs) (inject_incr ++> subrel).
Proof.
  intros p1 p2 Hp b1 b2 Hb.
  transport Hb; subst.
  eauto.
Qed.

(** *** Representable pointers *)

(* When going from [Z] to [ptrofs] (using [Ptrofs.repr]), there is no
  problem going also from [ptr_inject] to [ptrbits_inject]. However,
  when converting from machine pointer related by [ptrbits_inject]
  to abstract pointers with [Z] offsets (using [Ptrofs.unsigned]),
  we cannot easily establish that the results are related by
  [ptr_inject], since there may in fact be a discrepency of k·2^n
  between the correct target pointer obtained by adding [delta] and
  that obtained through [Ptrofs.unsigned].

  The compiler proofs deal with this through a property of memory
  injections, which ensures that representable, valid pointers in the
  source memory correspond to representable target pointers as well.
  Whenever a memory operation succeeds on a pointer retreived from a
  machine value, we can then deduce that a corresponding target
  machine pointer will be the correct one.

  We introduce are relation [rptr_inject] 

  In the relational framework we integrate this approach by defining a
  third relation [rptr_inject], which asserts that two (abtract, [Z])
  pointer are related by a memory injection, *under the condition*
  that the memory injection preserve the representability of the
  source pointer. *)

Definition ptrbits_unsigned: block * ptrofs -> block * Z :=
  fun '(b, ofs) => (b, Ptrofs.unsigned ofs).

Definition rptr_inject (f: meminj): relation (block * Z) :=
  ptr_inject f \/ (ptrbits_inject f) !! ptrbits_unsigned.

Global Instance rptr_inject_incr:
  Monotonic (@rptr_inject) (inject_incr ++> subrel).
Proof.
  unfold rptr_inject.
  assert (Params (@rel_push) 3) by constructor.
  rauto.
Qed.

(** ** Relationships between injection relations *)

(** We call each lemma [foo_bar_inject] that establishes [bar_inject]
  from a [foo_inject] premise. When this can be done in several ways,
  we add a suffix to disambiguate. *)

(** *** Consequences of [ptr_inject] *)

Lemma add_repr ofs1 delta:
  Ptrofs.repr (ofs1 + delta) =
  Ptrofs.add (Ptrofs.repr ofs1) (Ptrofs.repr delta).
Proof.
    rewrite Ptrofs.add_unsigned.
    auto using Ptrofs.eqm_samerepr,
    Ptrofs.eqm_add, Ptrofs.eqm_unsigned_repr.
Qed.    

Lemma ptr_ptrbits_inject_repr f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  ptrbits_inject f (b1, Ptrofs.repr ofs1) (b2, Ptrofs.repr ofs2).
Proof.
  inversion 1; subst.
  rewrite add_repr.
  constructor.
  assumption.
Qed.

Lemma ptr_ptrbits_inject_unsigned f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2) ->
  ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros H.
  rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2).
  apply ptr_ptrbits_inject_repr; eauto.
Qed.

Lemma ptr_ptrrange_inject f b1 lo1 hi1 b2 lo2 hi2:
  RExists
    (ptr_inject f (b1, lo1) (b2, lo2) /\ hi1 - lo1 = hi2 - lo2)
    (ptrrange_inject f) (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros [Hlo Hhi].
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  replace hi2 with (lo2 + (hi1 - lo1))%Z by omega.
  constructor; eauto.
Qed.

Hint Extern 0 (RExists _ (ptrrange_inject _) _ _) =>
  eapply ptr_ptrrange_inject : typeclass_instances.

Lemma ptr_block_inject f b1 ofs1 b2 ofs2:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  block_inject f b1 b2.
Proof.
  inversion 1.
  eauto.
Qed.

Lemma ptr_block_sameofs_inject f b1 b2 ofs:
  ptr_inject f (b1, ofs) (b2, ofs) ->
  block_inject_sameofs f b1 b2.
Proof.
  inversion 1.
  assert (delta = 0) by omega.
  red.
  congruence.
Qed.

Global Instance ptr_rptr_inject_incr:
  Related (@ptr_inject) (@rptr_inject) (inject_incr ++> subrel).
Proof.
  unfold rptr_inject. rauto.
Qed.

(** *** Consequences of [ptrbits_inject] *)

Lemma ptrbits_block_inject f b1 ofs1 b2 ofs2:
  ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
  block_inject f b1 b2.
Proof.
  inversion 1.
  eauto.
Qed.

Lemma ptrbits_rptr_inject_unsigned f b1 ofs1 b2 ofs2:
  RIntro
    (ptrbits_inject f (b1, ofs1) (b2, ofs2))
    (rptr_inject f) (b1, Ptrofs.unsigned ofs1) (b2, Ptrofs.unsigned ofs2).
Proof.
  intros H.
  fold (ptrbits_unsigned (b1, ofs1)).
  fold (ptrbits_unsigned (b2, ofs2)).
  unfold rptr_inject. rauto.
Qed.

Hint Extern 1 (RIntro _ (rptr_inject _) (_, Ptrofs.unsigned _) _) =>
  eapply ptrbits_rptr_inject_unsigned : typeclass_instances.

Hint Extern 1 (RIntro _ (rptr_inject _) _ (_, Ptrofs.unsigned _)) =>
  eapply ptrbits_rptr_inject_unsigned : typeclass_instances.

(** *** Consequences of [ptrrange_inject] *)

Lemma ptrrange_ptr_inject f ptr1 hi1 ptr2 hi2:
  ptrrange_inject f (ptr1, hi1) (ptr2, hi2) ->
  ptr_inject f ptr1 ptr2.
Proof.
  inversion 1.
  assumption.
Qed.

(** *** Consequences of [block_inject] *)

Lemma block_ptr_inject f b1 b2 ofs1:
  block_inject f b1 b2 ->
  exists ofs2, ptr_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (ofs1 + delta)%Z.
  constructor; eauto.
Qed.

Lemma block_ptrbits_inject f b1 b2 ofs1:
  block_inject f b1 b2 ->
  exists ofs2, ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  intros [delta H].
  exists (Ptrofs.add ofs1 (Ptrofs.repr delta)).
  constructor; eauto.
Qed.

Lemma block_ptrrange_inject f b1 b2 lo1 hi1:
  block_inject f b1 b2 ->
  exists lo2 hi2, ptrrange_inject f (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros [delta H].
  exists (lo1 + delta)%Z, ((lo1 + delta) + (hi1 - lo1))%Z.
  pattern hi1 at 1.
  replace hi1 with (lo1 + (hi1 - lo1))%Z by omega.
  constructor.
  constructor.
  assumption.
Qed.

(** *** Consequences of [block_inject_sameofs] *)

Lemma block_sameofs_ptr_inject f b1 ofs1 b2 ofs2:
  RExists
    (block_inject_sameofs f b1 b2 /\ ofs1 = ofs2)
    (ptr_inject f) (b1, ofs1) (b2, ofs2).
Proof.
  intros [Hb Hofs].
  red in Hb.
  destruct Hofs.
  pattern ofs1 at 2.
  replace ofs1 with (ofs1 + 0)%Z by omega.
  constructor; eauto.
Qed.

Hint Extern 0 (RExists _ (ptr_inject _) _ _) =>
  eapply block_sameofs_ptr_inject : typeclass_instances.

Lemma block_sameofs_ptrbits_inject f b1 ofs1 b2 ofs2:
  RExists
    (block_inject_sameofs f b1 b2 /\ ofs1 = ofs2)
    (ptrbits_inject f) (b1, ofs1) (b2, ofs2).
Proof.
  intros [Hb Hofs].
  red in Hb.
  destruct Hofs.
  pattern ofs1 at 2.
  replace ofs1 with (Ptrofs.add ofs1 (Ptrofs.repr 0%Z)).
  - constructor; eauto.
  - change (Ptrofs.repr 0) with Ptrofs.zero.
    apply Ptrofs.add_zero.
Qed.

Hint Extern 0 (RExists _ (ptrbits_inject _) _ _) =>
  eapply block_sameofs_ptrbits_inject : typeclass_instances.

Lemma block_sameofs_ptrrange_inject f b1 lo1 hi1 b2 lo2 hi2:
  RExists
    (block_inject_sameofs f b1 b2 /\ lo1 = lo2 /\ hi1 = hi2)
    (ptrrange_inject f) (b1, lo1, hi1) (b2, lo2, hi2).
Proof.
  intros (Hb & Hlo & Hhi).
  red in Hb.
  subst.
  eapply ptr_ptrrange_inject; split; eauto.
  eapply block_sameofs_ptr_inject; eauto.
Qed.

Hint Extern 0 (RExists _ (ptrrange_inject _) _ _) =>
  eapply block_sameofs_ptrrange_inject : typeclass_instances.

Global Instance block_sameofs_block_inject:
  Related (@block_inject_sameofs) (@block_inject) (inject_incr ++> subrel).
Proof.
  repeat rstep.
  transitivity (block_inject x); [ | rauto]; clear.
  inversion 1.
  red.
  eauto.
Qed.

(** ** Other properties *)

(** *** Functionality *)

Lemma ptr_inject_functional f ptr ptr1 ptr2:
  ptr_inject f ptr ptr1 ->
  ptr_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma ptrbits_inject_functional f ptr ptr1 ptr2:
  ptrbits_inject f ptr ptr1 ->
  ptrbits_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros [b ofs b1 delta1 Hb1] Hb2'.
  inversion Hb2' as [xb xofs b2 delta2 Hb2]; clear Hb2'; subst.
  congruence.
Qed.

Lemma ptrrange_inject_functional f ptr ptr1 ptr2:
  ptrrange_inject f ptr ptr1 ->
  ptrrange_inject f ptr ptr2 ->
  ptr1 = ptr2.
Proof.
  intros Hptr1 Hptr2.
  destruct Hptr1 as [b ofs b1 ofs1 sz1 H1].
  inversion Hptr2 as [xb xofs b2 ofs2 sz2]; clear Hptr2; subst.
  pose proof (ptr_inject_functional f (b, ofs) (b1, ofs1) (b2, ofs2) H1 H).
  assert (sz1 = sz2).
  {
    eapply Z.add_reg_l; eauto.
  }
  congruence.
Qed.

Lemma block_inject_functional f b b1 b2:
  block_inject f b b1 ->
  block_inject f b b2 ->
  b1 = b2.
Proof.
  intros [d1 Hb1] [d2 Hb2].
  congruence.
Qed.

Lemma block_sameofs_inject_functional f b b1 b2:
  block_inject_sameofs f b b1 ->
  block_inject_sameofs f b b2 ->
  b1 = b2.
Proof.
  unfold block_inject_sameofs.
  congruence.
Qed.

(** *** Shift-invariance *)

Lemma ptr_inject_shift f b1 ofs1 b2 ofs2 delta:
  ptr_inject f (b1, ofs1) (b2, ofs2) ->
  ptr_inject f (b1, ofs1 + delta)%Z (b2, ofs2 + delta)%Z.
Proof.
  inversion 1; subst.
  rewrite <- Z.add_assoc.
  rewrite (Z.add_comm delta0 delta).
  rewrite Z.add_assoc.
  constructor; eauto.
Qed.

Lemma ptrbits_inject_shift f b1 ofs1 b2 ofs2 delta:
  ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
  ptrbits_inject f (b1, Ptrofs.add ofs1 delta) (b2, Ptrofs.add ofs2 delta).
Proof.
  inversion 1; subst.
  rewrite Ptrofs.add_assoc.
  rewrite (Ptrofs.add_commut (Ptrofs.repr _)).
  rewrite <- Ptrofs.add_assoc.
  constructor; eauto.
Qed.

Lemma ptrbits_inject_shift_sub f b1 ofs1 b2 ofs2 delta:
  ptrbits_inject f (b1, ofs1) (b2, ofs2) ->
  ptrbits_inject f (b1, Ptrofs.sub ofs1 delta) (b2, Ptrofs.sub ofs2 delta).
Proof.
  rewrite !Ptrofs.sub_add_opp.
  apply ptrbits_inject_shift.
Qed.

Lemma ptrrange_inject_shift f b1 ofs1 sz1 b2 ofs2 sz2 delta:
  ptrrange_inject f (b1, ofs1, sz1) (b2, ofs2, sz2) ->
  ptrrange_inject f (b1, ofs1 + delta, sz1)%Z (b2, ofs2 + delta, sz2)%Z.
Proof.
  inversion 1; subst.
  replace (ofs1 + sz)%Z with ((ofs1 + delta) + (sz - delta))%Z by omega.
  replace (ofs2 + sz)%Z with ((ofs2 + delta) + (sz - delta))%Z by omega.
  constructor.
  eapply ptr_inject_shift; eauto.
Qed.

(** See also [val_offset_ptr_inject] below. *)


(** * Relational properties *)

(** ** Basic value constructors *)

Global Instance Vundef_inject f v:
  Related (@Vundef) v (Val.inject f).
Proof.
  constructor.
Qed.

Global Instance Vint_inject mi:
  Monotonic Vint (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vlong_inject mi:
  Monotonic Vlong (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vfloat_inject mi:
  Monotonic Vfloat (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vsingle_inject mi:
  Monotonic Vsingle (- ==> Val.inject mi).
Proof.
  constructor.
Qed.

Global Instance Vptr_inject f:
  Monotonic (@Vptr) (% ptrbits_inject f ++> Val.inject f).
Proof.
  intros _ _ [b1 ofs1 b2 delta].
  econstructor; eauto.
Qed.

Global Instance Vzero_inject f:
  Monotonic (@Vzero) (Val.inject f).
Proof.
  unfold Vzero; rauto.
Qed.

Global Instance Vone_inject f:
  Monotonic (@Vone) (Val.inject f).
Proof.
  unfold Vone; rauto.
Qed.

Global Instance Vmone_inject f:
  Monotonic (@Vmone) (Val.inject f).
Proof.
  unfold Vmone; rauto.
Qed.

Global Instance Vtrue_inject f:
  Monotonic (@Vtrue) (Val.inject f).
Proof.
  unfold Vtrue; rauto.
Qed.

Global Instance Vfalse_inject f:
  Monotonic (@Vfalse) (Val.inject f).
Proof.
  unfold Vfalse; rauto.
Qed.

Global Instance Vnullptr_inject f:
  Monotonic Vnullptr (Val.inject f).
Proof.
  unfold Vnullptr; rauto.
Qed.

Global Instance Vptrofs_inject f:
  Monotonic Vptrofs (- ==> Val.inject f).
Proof.
  unfold Vptrofs; rauto.
Qed.

(** ** Typing predicates *)

Global Instance val_has_type_inject f:
  Monotonic (@Val.has_type) (Val.inject f --> - ==> impl).
Proof.
  unfold Val.has_type.
  intros x y Hxy ty H.
  destruct Hxy, ty; tauto.
Qed.

Global Instance val_has_type_list_inject f:
  Monotonic (@Val.has_type_list) (Val.inject_list f --> - ==> impl).
Proof.
  induction 1; simpl; rauto.
Qed.

Global Instance val_has_opttype_inject f:
  Monotonic (@Val.has_opttype) (Val.inject f --> option_le eq ++> impl).
Proof.
  unfold Val.has_opttype; repeat rstep.
  intros Hx; subst.
  inversion H; subst.
  destruct y1; constructor.
Qed.

(** ** Interpretation as a boolean *)

Global Instance val_bool_of_val_inject f:
  Monotonic (@Val.bool_of_val) (Val.inject f ++> set_le Bool.leb).
Proof.
  intros v1 v2 Hv b1 Hb1.
  destruct Hb1. inv Hv. eexists. split; [constructor|].
  rauto.
Qed.

(** ** Arithmetic operations *)

Global Instance val_neg_match f:
  Monotonic (@Val.neg) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.neg. rauto.
Qed.

Global Instance val_negf_inject f:
  Monotonic (@Val.negf) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negf. rauto.
Qed.

Global Instance val_absf_inject f:
  Monotonic (@Val.absf) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.absf. rauto.
Qed.

Global Instance val_negfs_inject f:
  Monotonic (@Val.negfs) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negfs. rauto.
Qed.

Global Instance val_absfs_inject f:
  Monotonic (@Val.absfs) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.absfs. rauto.
Qed.

Global Instance val_maketotal_inject f:
  Monotonic (@Val.maketotal) (option_le (Val.inject f) ++> Val.inject f).
Proof.
  unfold Val.maketotal. rauto.
Qed.

Global Instance val_intoffloat_inject f:
  Monotonic (@Val.intoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intoffloat. rauto.
Qed.

Global Instance val_intuoffloat_inject f:
  Monotonic (@Val.intuoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intuoffloat. rauto.
Qed.

Global Instance val_floatofint_inject f:
  Monotonic (@Val.floatofint) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatofint. rauto.
Qed.

Global Instance val_floatofintu_inject f:
  Monotonic (@Val.floatofintu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatofintu. rauto.
Qed.

Global Instance val_intofsingle_inject f:
  Monotonic (@Val.intofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intofsingle. rauto.
Qed.

Global Instance val_intuofsingle_inject f:
  Monotonic (@Val.intuofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.intuofsingle. rauto.
Qed.

Global Instance val_singleofint_inject f:
  Monotonic (@Val.singleofint) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleofint. rauto.
Qed.

Global Instance val_singleofintu_inject f:
  Monotonic (@Val.singleofintu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleofintu. rauto.
Qed.

Global Instance val_negint_inject f:
  Monotonic (@Val.negint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negint. rauto.
Qed.

Global Instance val_notint_inject f:
  Monotonic (@Val.notint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notint. rauto.
Qed.

Global Instance val_of_bool_inject f:
  Monotonic (@Val.of_bool) (- ==> Val.inject f).
Proof.
  unfold Val.of_bool. rauto.
Qed.

Global Instance val_boolval_inject f:
  Monotonic (@Val.boolval) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.boolval. rauto.
Qed.

Global Instance val_notbool_inject f:
  Monotonic (@Val.notbool) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notbool. rauto.
Qed.

Global Instance val_zero_ext_inject f:
  Monotonic (@Val.zero_ext) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.zero_ext. rauto.
Qed.

Global Instance val_sign_ext_inject f:
  Monotonic (@Val.sign_ext) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.sign_ext. rauto.
Qed.

Global Instance val_singleoffloat_inject f:
  Monotonic (@Val.singleoffloat) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.singleoffloat. rauto.
Qed.

Global Instance val_floatofsingle_inject f:
  Monotonic (@Val.floatofsingle) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.floatofsingle. rauto.
Qed.

Global Instance val_add_inject f:
  Monotonic (@Val.add) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.add_inject; eauto.
Qed.

Global Instance val_sub_inject f:
  Monotonic (@Val.sub) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.sub_inject; eauto.
Qed.

Global Instance val_mul_inject f:
  Monotonic (@Val.mul) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mul. rauto.
Qed.

Global Instance val_mulhs_inject f:
  Monotonic (@Val.mulhs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulhs. rauto.
Qed.

Global Instance val_mulhu_inject f:
  Monotonic (@Val.mulhu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulhu. rauto.
Qed.

Global Instance val_divs_inject f:
  Monotonic
    (@Val.divs)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divs. rauto.
Qed.

Global Instance val_mods_inject f:
  Monotonic
    (@Val.mods)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.mods. rauto.
Qed.

Global Instance val_divu_inject f:
  Monotonic
    (@Val.divu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divu. rauto.
Qed.

Global Instance val_modu_inject f:
  Monotonic
    (@Val.modu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modu. rauto.
Qed.

Global Instance val_add_carry f:
  Monotonic
    (@Val.add_carry)
    (Val.inject f ++> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.add_carry. rauto.
Qed.

Global Instance val_sub_overflow_inject f:
  Monotonic
    (@Val.sub_overflow)
    (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.sub_overflow. rauto.
Qed.

Global Instance val_negative_inject f:
  Monotonic (@Val.negative) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negative. rauto.
Qed.

Global Instance val_and_inject f:
  Monotonic (@Val.and) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.and. rauto.
Qed.

Global Instance val_or_inject f:
  Monotonic (@Val.or) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.or. rauto.
Qed.

Global Instance val_xor_inject f:
  Monotonic (@Val.xor) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.xor. rauto.
Qed.

Global Instance val_shl_inject f:
  Monotonic (@Val.shl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shl. rauto.
Qed.

Global Instance val_shr_inject f:
  Monotonic (@Val.shr) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shr. rauto.
Qed.

Global Instance val_shr_carry_inject f:
  Monotonic (@Val.shr_carry) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shr_carry. rauto.
Qed.

Global Instance val_shrx_inject f:
  Monotonic
    (@Val.shrx)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.shrx. rauto.
Qed.

Global Instance val_shru_inject f:
  Monotonic (@Val.shru) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shru. rauto.
Qed.

Global Instance val_rolm_inject f:
  Monotonic (@Val.rolm) (Val.inject f ++> - ==> - ==> Val.inject f).
Proof.
  unfold Val.rolm. rauto.
Qed.

Global Instance val_ror_inject f:
  Monotonic (@Val.ror) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.ror. rauto.
Qed.

Global Instance val_addf_inject f:
  Monotonic (@Val.addf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.addf. rauto.
Qed.

Global Instance val_subf_inject f:
  Monotonic (@Val.subf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.subf. rauto.
Qed.

Global Instance val_mulf_inject f:
  Monotonic (@Val.mulf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulf. rauto.
Qed.

Global Instance val_divf_inject f:
  Monotonic (@Val.divf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.divf. rauto.
Qed.

Global Instance val_floatofwords_inject f:
  Monotonic
    (@Val.floatofwords)
    (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.floatofwords. rauto.
Qed.

Global Instance val_addfs_inject f:
  Monotonic (@Val.addfs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.addfs. rauto.
Qed.

Global Instance val_subfs_inject f:
  Monotonic (@Val.subfs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.subfs. rauto.
Qed.

Global Instance val_mulfs_inject f:
  Monotonic (@Val.mulfs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mulfs. rauto.
Qed.

Global Instance val_divfs_inject f:
  Monotonic (@Val.divfs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.divfs. rauto.
Qed.

(** ** Operations on 64-bit integers *)

Global Instance val_longofwords_inject f:
  Monotonic (@Val.longofwords) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofwords. rauto.
Qed.

Global Instance val_loword_inject f:
  Monotonic (@Val.loword) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.loword. rauto.
Qed.

Global Instance val_hiword_inject f:
  Monotonic (@Val.hiword) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.hiword. rauto.
Qed.

Global Instance val_negl_inject f:
  Monotonic (@Val.negl) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negl. rauto.
Qed.

Global Instance val_notl_inject f:
  Monotonic (@Val.notl) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.notl. rauto.
Qed.

Global Instance val_longofint_inject f:
  Monotonic (@Val.longofint) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofint. rauto.
Qed.

Global Instance val_longofintu_inject f:
  Monotonic (@Val.longofintu) (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.longofintu. rauto.
Qed.

Global Instance val_longoffloat_inject f:
  Monotonic (@Val.longoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longoffloat. rauto.
Qed.

Global Instance val_longuoffloat_inject f:
  Monotonic (@Val.longuoffloat) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longuoffloat. rauto.
Qed.

Global Instance val_longofsingle_inject f:
  Monotonic (@Val.longofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longofsingle. rauto.
Qed.

Global Instance val_longuofsingle_inject f:
  Monotonic (@Val.longuofsingle) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.longuofsingle. rauto.
Qed.

Global Instance val_floatoflong_inject f:
  Monotonic (@Val.floatoflong) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatoflong. rauto.
Qed.

Global Instance val_floatoflongu_inject f:
  Monotonic (@Val.floatoflongu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.floatoflongu. rauto.
Qed.

Global Instance val_singleoflong_inject f:
  Monotonic (@Val.singleoflong) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleoflong. rauto.
Qed.

Global Instance val_singleoflongu_inject f:
  Monotonic (@Val.singleoflongu) (Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.singleoflongu. rauto.
Qed.

Global Instance val_addl_inject f:
  Monotonic (@Val.addl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.addl_inject; eauto.
Qed.

Global Instance val_subl_inject f:
  Monotonic (@Val.subl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  repeat intro; apply Val.subl_inject; eauto.
Qed.

Global Instance val_mull_inject f:
  Monotonic (@Val.mull) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mull. rauto.
Qed.

Global Instance val_mull'_inject f:
  Monotonic (@Val.mull') (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mull'. rauto.
Qed.

Global Instance val_mullhs_inject f:
  Monotonic (@Val.mullhs) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mullhs. rauto.
Qed.

Global Instance val_mullhu_match f:
  Monotonic (@Val.mullhu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.mullhu. rauto.
Qed.

Global Instance val_divls_inject f:
  Monotonic
    (@Val.divls)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divls. rauto.
Qed.

Global Instance val_modls_inject f:
  Monotonic
    (@Val.modls)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modls. rauto.
Qed.

Global Instance val_divlu_inject f:
  Monotonic
    (@Val.divlu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.divlu. rauto.
Qed.

Global Instance val_modlu_inject f:
  Monotonic
    (@Val.modlu)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.modlu. rauto.
Qed.

Global Instance val_andl_inject f:
  Monotonic (@Val.andl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.andl. rauto.
Qed.

Global Instance val_orl_inject f:
  Monotonic (@Val.orl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.orl. rauto.
Qed.

Global Instance val_xorl_inject f:
  Monotonic (@Val.xorl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.xorl. rauto.
Qed.

Global Instance val_shll_inject f:
  Monotonic (@Val.shll) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shll. rauto.
Qed.

Global Instance val_shrl_inject f:
  Monotonic (@Val.shrl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shrl. rauto.
Qed.

Global Instance val_shrlu_inject f:
  Monotonic (@Val.shrlu) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shrlu. rauto.
Qed.

Global Instance val_shrxl_inject f:
  Monotonic
    (@Val.shrxl)
    (Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.shrxl. rauto.
Qed.

Global Instance val_shrl_carry_inject f:
  Monotonic (@Val.shrl_carry) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.shrl_carry. rauto.
Qed.

Global Instance val_roll_inject f:
  Monotonic (@Val.roll) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.roll. rauto.
Qed.

Global Instance val_rorl_inject f:
  Monotonic (@Val.rorl) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.rorl. rauto.
Qed.

Global Instance val_rolml_inject f:
  Monotonic (@Val.rolml) (Val.inject f ++> - ==> - ==> Val.inject f).
Proof.
  unfold Val.rolml. rauto.
Qed.

(** ** Comparisons *)

(** Note: the relational properties for unsigned integer comparisons
  (which potentially involve pointers) are defined in CKLR.v because
  the properties depend in [Mem.valid_pointer] and the like. *)

Global Instance val_cmp_bool_inject f:
  Monotonic
    Val.cmp_bool
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmp_bool. rauto.
Qed.

Global Instance val_cmpf_bool_inject f:
  Monotonic
    (@Val.cmpf_bool)
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmpf_bool. rauto.
Qed.

Global Instance val_cmpfs_bool_inject f:
  Monotonic
    (@Val.cmpfs_bool)
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmpfs_bool. rauto.
Qed.

Global Instance val_cmpl_bool_inject f:
  Monotonic
    (@Val.cmpl_bool)
    (- ==> Val.inject f ++> Val.inject f ++> option_le eq).
Proof.
  unfold Val.cmpl_bool. rauto.
Qed.

Global Instance val_of_optbool_inject f:
  Monotonic (@Val.of_optbool) (option_le eq ++> Val.inject f).
Proof.
  unfold Val.of_optbool. rauto.
Qed.

Global Instance val_cmp_inject f:
  Monotonic (@Val.cmp) (- ==> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.cmp. rauto.
Qed.

Global Instance val_cmpf_inject f:
  Monotonic (@Val.cmpf) (- ==> Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.cmpf. rauto.
Qed.

Global Instance val_cmpl_inject f:
  Monotonic
    (@Val.cmpl)
    (- ==> Val.inject f ++> Val.inject f ++> option_le (Val.inject f)).
Proof.
  unfold Val.cmpl. rauto.
Qed.

Global Instance val_maskzero_bool_inject f:
  Monotonic
    Val.maskzero_bool
    (Val.inject f ++> - ==> option_le eq).
Proof.
  unfold Val.maskzero_bool. rauto.
Qed.

Global Instance val_offset_ptr_inject f:
  Monotonic
    Val.offset_ptr
    (Val.inject f ++> - ==> Val.inject f).
Proof.
  unfold Val.offset_ptr. repeat rstep.
  eauto using ptrbits_inject_shift.
Qed.

Global Instance val_normalize_inject f:
  Monotonic
    (@Val.normalize)
    (Val.inject f ++> - ==> Val.inject f).
Proof.
  unfold Val.normalize. rauto.
Qed.

Global Instance val_select_inject f:
  Monotonic
    (@Val.select)
    (option_le eq ++> Val.inject f ++> Val.inject f ++> - ==> Val.inject f).
Proof.
  unfold Val.select. rauto.
Qed.

Global Instance val_load_result_inject f:
  Monotonic (@Val.load_result) (- ==> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.load_result. rauto.
Qed.

Global Instance val_negativel_inject f:
  Monotonic Val.negativel (Val.inject f ++> Val.inject f).
Proof.
  unfold Val.negativel. rauto.
Qed.
Global Instance val_subl_overflow_inject f:
  Monotonic Val.subl_overflow (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold Val.subl_overflow. rauto.
Qed.
