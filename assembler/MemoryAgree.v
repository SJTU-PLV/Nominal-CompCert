Require Import Coqlib Errors Maps.
Require Import Integers Floats.
Require Import Values Memory Events Globalenvs.
Require Import LocalLib AsmInject Asm.
Import ListNotations.


(** *A new injection: remove the perm_inv from Memory.inject *)
Record magree (f: meminj) (m1 m2: mem) : Prop :=
  mk_magree {
    ma_inj:
      Mem.mem_inj f m1 m2;
    ma_freeblocks:
      forall b, ~(Mem.valid_block m1 b) -> f b = None;
    ma_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> Mem.valid_block m2 b';
    ma_no_overlap:
      Mem.meminj_no_overlap f m1;
    ma_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned
  }.

(** Assumption about external calls.
    These should be merged into common properties about external calls later. *)
Axiom external_call_inject : forall ge j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    j = Mem.flat_inj (Mem.support m1) ->
    Val.inject_list j vargs1 vargs2 ->
    magree j m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef ge vargs2 m2 t vres2 m2' /\
      Val.inject j' vres1 vres2 /\ magree j' m1' m2' /\
      inject_incr j j' /\
      inject_separated j j' m1 m2 /\
      j' = Mem.flat_inj (Mem.support m1').


Axiom  external_call_valid_block: forall ef ge vargs m1 t vres m2 b,
    external_call ef ge vargs m1 t vres m2 -> Mem.valid_block m1 b -> Mem.valid_block m2 b.

(* copy from Memory *)

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  magree f m1 m2 ->
  Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit ma_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  magree f m1 m2 ->
  Mem.valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). lia.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  magree f m1 m2 ->
  Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite Mem.weak_valid_pointer_spec in H0.
  rewrite ! Mem.valid_pointer_nonempty_perm in H0.
  exploit ma_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite Ptrofs.unsigned_repr; lia.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  magree f m1 m2 ->
  Mem.valid_access m1 chunk b1 ofs p ->
  Mem.valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply Mem.valid_access_inj; eauto. apply ma_inj; auto.
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  magree f m1 m2 ->
  Mem.valid_pointer m1 b1 ofs = true ->
  Mem.valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite Mem.valid_pointer_valid_access in H1.
  rewrite Mem.valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  magree f m1 m2 ->
  Mem.weak_valid_pointer m1 b1 ofs = true ->
  Mem.weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold Mem.weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
  intros []; eauto using valid_pointer_inject.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  magree f m1 m2 ->
  Mem.valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite Mem.valid_pointer_valid_access in H0. eauto.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  magree f m1 m2 ->
  Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite Mem.weak_valid_pointer_spec in H0.
  rewrite ! Mem.valid_pointer_nonempty_perm in H0.
  exploit ma_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
Qed.

(* copy from Asminject *)
(** Injection for cmpu_bool and cmplu_bool *)
Lemma valid_ptr_inj : forall j m m',
    magree j m m' ->
    forall b i b' delta,                                  
      j b = Some (b', delta) ->
      Mem.valid_pointer m b (Ptrofs.unsigned i) = true ->
      Mem.valid_pointer m' b' (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply valid_pointer_inject_val; eauto.
Qed.


Lemma weak_valid_ptr_inj: forall j m m',
  magree j m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply weak_valid_pointer_inject_val; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  magree j m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  magree f m m' ->
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite Mem.valid_pointer_valid_access in H1.
  rewrite Mem.valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply ma_no_overlap; eauto.
  apply Mem.perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
  apply Mem.perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  magree j m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: magree j m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j m m' ->
    Val.opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: magree j m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j m m' ->
    Val.opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.


Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j  m m' ->
    Val.opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply Val.vofbool_inject.
Qed.
(* end of copy *)


(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  magree f m1 m2 ->
  Mem.load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, Mem.load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply Mem.load_inj; eauto.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  magree f m1 m2 ->
  Mem.loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, Mem.loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold Mem.loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  magree f m1 m2 ->
  Mem.loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, Mem.loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply Mem.loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  magree f m1 m2 ->
  Mem.store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ magree f n1 n2.
Proof.
  intros. inversion H.
  exploit Mem.store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply ma_representable; try eassumption.
  destruct H4; eauto with mem.
Qed.


Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  magree f m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ magree f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold Mem.storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.


(* Preservaiton of allocation *)
Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  magree f m1 m2 ->
  Mem.alloc m1 lo hi = (m1', b1) ->
  Mem.valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, Mem.perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> Mem.perm m2 b2 (ofs + delta) k p) ->
  Mem.inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   Mem.perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     magree f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (Mem.mem_inj f' m1 m2).
    inversion ma_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0).
      eapply Mem.perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply Mem.alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit Mem.perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit Mem.perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
   exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). lia.
  eapply ma_representable0; try eassumption.
  destruct H10; eauto using Mem.perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  magree f m1 m2 ->
  Mem.alloc m2 lo hi = (m2', b2) ->
  magree f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply Mem.alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  magree f m1 m2 ->
  Mem.alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  Mem.alloc m2 lo2 hi2 = (m2', b2)
  /\ magree f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (Mem.alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
  auto.
  intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. lia.
  red; intros. apply Z.divide_0_r.
  intros. apply (Mem.valid_not_valid_diff m2 b2 b2).
  (* cannot solve by mem *)
  eapply ma_mappedblocks;eauto.
  eapply  Mem.fresh_block_alloc;eauto.
  auto.
 
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** *End of A new injection *)

