Require Export LogicalRelations.
Require Export KLR.
Require Export OptionRel.
Require Export BoolRel.

Require Export Coqlib.
Require Export Integers.
Require Export AST.
Require Export Valuesrel.
Require Export Memory.
Require Export Globalenvs.
Require Export Events.


(** * Compcert Kripke simulation relations *)

(** ** Definition *)

(** A CompCert KLR specifies a set for worlds, a transitive
  accessibility relation between them, and world-indexed relations for
  all the basic ingredients CompCert states are built out of: values,
  memory states, etc. From these components, it is possible to build
  up simulation relations for complex types such as [Clight.state] or
  [Asm.state] in a uniform way over all possible KLRs, and
  compositionally prove very general relational parametricity
  properties for the functions that manipulate them.

  The relations on values are all derived from the memory injection
  [mi w] associated to a world [w]. In addition, the KLR specifies a
  relation [match_mem] over memory states, which may be much richer
  than the usual memory extension and injection relations. While
  "peripheral" relations ([match_val], etc.) will be monotonic in the
  world (so that existing relationaships between environments,
  register maps, etc. can be carried along when we transition to a
  successor world), this is not necessarily the case for the relation
  on memories: the memory state is expected to be the core of all
  states and to drive the transitions between worlds.

  The basic relation components should be compatible with the basic
  memory operations, so that they satisfy the relational properties
  enumerated below. *)

Record cklr :=
  {
    world: Type;
    wacc: relation world;

    cklr_kf : KripkeFrame unit world := {| acc w := wacc; |};

    mi: world -> meminj;
    match_mem: klr world mem mem;
    match_stbls: klr world Genv.symtbl Genv.symtbl;

    acc_preorder:
      PreOrder wacc;

    mi_acc:
      Monotonic mi (wacc ++> inject_incr);
    mi_acc_separated w w' m1 m2:
      match_mem w m1 m2 ->
      wacc w w' ->
      inject_separated (mi w) (mi w') m1 m2;

    match_stbls_acc:
      Monotonic match_stbls (wacc ++> subrel);
    match_stbls_proj w:
      Related (match_stbls w) (Genv.match_stbls (mi w)) subrel;
    match_stbls_support w se1 se2 m1 m2:
      match_stbls w se1 se2 ->
      match_mem w m1 m2 ->
      Mem.sup_include (Genv.genv_sup se1) (Mem.support m1) ->
      Mem.sup_include (Genv.genv_sup se2) (Mem.support m2);

    cklr_alloc:
      Monotonic
        (@Mem.alloc)
        (|= match_mem ++> - ==> - ==>
         <> match_mem * block_inject_sameofs @@ [mi]);

    cklr_free:
      Monotonic
        (@Mem.free)
        (|= match_mem ++> %% ptrrange_inject @@ [mi] ++>
         k1 option_le (<> match_mem));

    cklr_load:
      Monotonic
        (@Mem.load)
        (|= - ==> match_mem ++> % ptr_inject @@ [mi] ++>
         k1 option_le (Val.inject @@ [mi]));

    cklr_store:
      Monotonic
        (@Mem.store)
        (|= - ==> match_mem ++> % ptr_inject @@ [mi] ++> Val.inject @@ [mi] ++>
         k1 option_le (<> match_mem));

    cklr_loadbytes:
      Monotonic
        (@Mem.loadbytes)
        (|= match_mem ++> % ptr_inject @@ [mi] ++> - ==>
         k1 option_le (k1 list_rel (memval_inject @@ [mi])));

    cklr_storebytes:
      Monotonic
        (@Mem.storebytes)
        (|= match_mem ++> % rptr_inject @@ [mi] ++>
         k1 list_rel (memval_inject @@ [mi]) ++>
         k1 option_le (<> match_mem));

    cklr_perm:
      Monotonic
        (@Mem.perm)
        (|= match_mem ++> % ptr_inject @@ [mi] ++> - ==> - ==> k impl);

    cklr_valid_block:
      Monotonic
        (@Mem.valid_block)
        (|= match_mem ++> block_inject @@ [mi] ++> k iff);

    cklr_no_overlap w m1 m2:
      match_mem w m1 m2 ->
      Mem.meminj_no_overlap (mi w) m1;

    cklr_representable w m1 m2 b1 ofs1 b2 delta:
      match_mem w m1 m2 ->
      Mem.perm m1 b1 ofs1 Max Nonempty \/
      Mem.perm m1 b1 (ofs1 - 1) Max Nonempty ->
      mi w b1 = Some (b2, delta) ->
      0 <= ofs1 <= Ptrofs.max_unsigned ->
      delta >= 0 /\ 0 <= ofs1 + delta <= Ptrofs.max_unsigned;

    (* similar to Mem.aligned_area_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_aligned_area_inject:
      forall w m m' b ofs al sz b' delta,
        match_mem w m m' ->
        (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) ->
        sz > 0 ->
        (al | sz) ->
        Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
        (al | ofs) ->
        mi w b = Some (b', delta) ->
        (al | ofs + delta);

    (* similar to Mem.disjoint_or_equal_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_disjoint_or_equal_inject:
      forall w m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
        match_mem w m m' ->
        mi w b1 = Some (b1', delta1) ->
        mi w b2 = Some (b2', delta2) ->
        Mem.range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
        Mem.range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
        sz > 0 ->
        b1 <> b2 \/
        ofs1 = ofs2 \/
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
        b1' <> b2' \/
        (ofs1 + delta1 = ofs2 + delta2)%Z \/
        ofs1 + delta1 + sz <= ofs2 + delta2 \/
        ofs2 + delta2 + sz <= ofs1 + delta1;

    cklr_perm_inv w m1 m2 b1 ofs1 b2 ofs2 k p:
      match_mem w m1 m2 ->
      ptr_inject (mi w) (b1, ofs1) (b2, ofs2) ->
      Mem.perm m2 b2 ofs2 k p ->
      Mem.perm m1 b1 ofs1 k p \/ ~Mem.perm m1 b1 ofs1 Max Nonempty;

    cklr_sup_include w m1 m2 m1' m2':
      match_mem w m1 m2 ->
      (<> match_mem)%klr w m1' m2' ->
      Mem.sup_include (Mem.support m1) (Mem.support m1') <->
      Mem.sup_include (Mem.support m2) (Mem.support m2');

  }.

Global Existing Instance cklr_kf.
Global Existing Instance acc_preorder.
Global Existing Instance mi_acc.
Global Instance mi_acc_params: Params (@mi) 2.
Global Existing Instance match_stbls_acc.
Global Instance match_stbls_params: Params (@match_stbls) 3.

Global Existing Instances cklr_alloc.
Local Existing Instances cklr_free.
Local Existing Instances cklr_load.
Local Existing Instances cklr_store.
Local Existing Instances cklr_loadbytes.
Global Existing Instances cklr_storebytes.
Local Existing Instances cklr_perm.
Global Existing Instances cklr_valid_block.

(** *** Machine pointers *)

(** When comparing two weakly valid pointers of the same block
  using Val.cmpu, we need to compare their offsets, and so
  comparing the injected offsets must have the same result. To
  this end, it is necessary to show that all weakly valid
  pointers be shifted by the same mathematical (not machine)
  integer amount. *)

Lemma cklr_weak_valid_pointer_address_inject:
  forall R w m1 m2 b1 b2 delta ofs1,
    match_mem R w m1 m2 ->
    mi R w b1 = Some (b2, delta) ->
    Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
    Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  pose proof (Ptrofs.unsigned_range_2 ofs1).
  edestruct (cklr_representable R w m1 m2 b1 (Ptrofs.unsigned ofs1)); eauto.
  {
    rewrite !Mem.weak_valid_pointer_spec, !Mem.valid_pointer_nonempty_perm in H1.
    intuition eauto using Mem.perm_cur_max.
  }
  rewrite Ptrofs.add_unsigned.
  rewrite !Ptrofs.unsigned_repr.
  - reflexivity.
  - extlia.
  - rewrite Ptrofs.unsigned_repr by extlia.
    assumption.
Qed.

(* Similar to [Mem.address_inject]; needed by Clight assign_of
  (By_copy), memcpy, and likely other places. *)

Lemma cklr_address_inject R w m1 m2 b1 ofs1 b2 delta pe:
  match_mem R w m1 m2 ->
  Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur pe ->
  mi R w b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
  Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  eapply cklr_weak_valid_pointer_address_inject; eauto.
  apply Mem.valid_pointer_implies.
  apply Mem.valid_pointer_nonempty_perm.
  eapply Mem.perm_implies; eauto.
  constructor.
Qed.

Lemma ptrbits_ptr_inject R w m1 m2 b1 o1 b2 o2 pe:
  match_mem R w m1 m2 ->
  ptrbits_inject (mi R w) (b1, o1) (b2, o2) ->
  Mem.perm m1 b1 (Ptrofs.unsigned o1) Cur pe ->
  ptr_inject (mi R w) (b1, Ptrofs.unsigned o1) (b2, Ptrofs.unsigned o2).
Proof.
  intros H H0 H1.
  inversion H0; subst.
  erewrite cklr_address_inject; eauto.
Qed.

(** *** Strengthening relations on pointers *)

(** If we have a valid pointer on the left-hand side, then [match_rptr]
  can be promoted to [match_ptr]. This is used below to strengthen the
  relational properties of most memory operations so that they only
  require [match_rptr] for ther hypotheses. *)

Lemma rptr_ptr_inject R w m1 m2 b1 ofs1 b2 ofs2 k pe:
  match_mem R w m1 m2 ->
  rptr_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  Mem.perm m1 b1 ofs1 k pe \/ Mem.perm m1 b1 (ofs1 - 1) k pe ->
  ptr_inject (mi R w) (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  destruct Hptr; eauto.
  inv H. destruct x as [xb1 obits1], y as [xb2 obits2].
  inv H0. inv H1. inv H2. unfold ptrbits_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.add _ _)) with (Ptrofs.unsigned obits1 + delta).
  - constructor; eauto.
  - pose proof (Ptrofs.unsigned_range_2 obits1).
    edestruct (cklr_representable R w m1 m2 b1 (Ptrofs.unsigned obits1)); eauto.
    + destruct k;
      intuition eauto using Mem.perm_implies, Mem.perm_cur_max, perm_any_N.
    + rewrite Ptrofs.add_unsigned.
      rewrite (Ptrofs.unsigned_repr delta) by extlia.
      rewrite Ptrofs.unsigned_repr by extlia.
      reflexivity.
Qed.

Lemma rptr_ptr_inject_weak_valid_pointer R w m1 m2 b1 ofs1 b2 ofs2:
  match_mem R w m1 m2 ->
  rptr_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  Mem.weak_valid_pointer m1 b1 ofs1 = true ->
  ptr_inject (mi R w) (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  apply Mem.weak_valid_pointer_spec in Hptr1.
  rewrite !Mem.valid_pointer_nonempty_perm in Hptr1.
  eapply rptr_ptr_inject; eauto.
Qed.

Lemma rptr_ptr_inject_valid_access R w m1 m2 b1 ofs1 b2 ofs2 chunk pe:
  match_mem R w m1 m2 ->
  rptr_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  Mem.valid_access m1 chunk b1 ofs1 pe ->
  ptr_inject (mi R w) (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  eapply rptr_ptr_inject; eauto.
  eapply Mem.valid_access_perm with (k := Cur) in Hptr1.
  eauto.
Qed.

Lemma rptr_ptr_inject_perm R w m1 m2 b1 ofs1 b2 ofs2 pe k:
  match_mem R w m1 m2 ->
  rptr_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  Mem.perm m1 b1 ofs1 k pe ->
  ptr_inject (mi R w) (b1, ofs1) (b2, ofs2).
Proof.
  intros Hm Hptr Hptr1.
  eapply rptr_ptr_inject; eauto.
Qed.

(** ** Properties of derived memory operations *)

Global Instance cklr_loadv R:
  Monotonic
    (@Mem.loadv)
    (|= - ==> match_mem R ++> Val.inject @@ [mi R] ++>
     k1 option_le (Val.inject @@ [mi R])).
Proof.
  repeat red.
  intros w a x y H x0 y0 H0.
  inversion H0; subst; simpl; try now constructor.
  destruct (Mem.load a x _ (Ptrofs.unsigned _)) eqn:LOAD; try now constructor.
  rewrite <- LOAD.
  repeat rstep.
  eapply ptrbits_ptr_inject; eauto.
  eapply Mem.load_valid_access; eauto.
  generalize (size_chunk_pos a); omega.
Qed.

Global Instance cklr_storev R:
  Monotonic
    (@Mem.storev)
    (|= - ==> match_mem R ++> Val.inject @@ [mi R] ++> Val.inject @@ [mi R] ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w a x y H x0 y0 H0 x1 y1 H1.
  destruct (Mem.storev a x _ _) eqn:STORE; [ | rauto ].
  rewrite <- STORE.
  inversion H0; subst; simpl; try rauto.
  simpl in STORE.
  repeat rstep.
  eapply ptrbits_ptr_inject; eauto.
  eapply Mem.store_valid_access_3; eauto.
  generalize (size_chunk_pos a); omega.
Qed.

(** Maybe it's possible to prove [cklr_storebytes] from [cklr_store]
  as well. But if it is, it's tricky. *)

Global Instance cklr_free_list R:
  Monotonic
    (@Mem.free_list)
    (|= match_mem R ++> k1 list_rel (ptrrange_inject @@ [mi R]) ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w m1 m2 Hm l1 l2 Hl.
  revert w l2 Hl m1 m2 Hm.
  induction l1; inversion 1; subst; simpl Mem.free_list; intros.
  - rauto.
  - rstep.
    rstep; rstep.
    rstep; rstep.
    + destruct H4 as (w' & Hw' & H4).
      destruct (IHl1 w' y0 rauto x y1 rauto) as [? ? (w'' & Hw'' & H) | ];
      rauto.
    + rauto.
Qed.

Local Instance mem_valid_pointer_match R w:
  Monotonic
    (@Mem.valid_pointer)
    (match_mem R w ++> % ptr_inject (mi R w) ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
  simpl.
  destruct (Mem.valid_pointer m1 b1 ofs1) eqn:Hp1; simpl; eauto.
  revert Hp1.
  rewrite !Mem.valid_pointer_nonempty_perm.
  repeat rstep.
Qed.

Local Instance mem_weak_valid_pointer_match R w:
  Monotonic
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % ptr_inject (mi R w) ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hp.
  simpl.
  unfold Mem.weak_valid_pointer.
  repeat rstep.
  apply ptr_inject_shift.
  assumption.
Qed.

(** ** Strengthened properties for memory operations *)

Definition ptrrange_perm m k p: relation _ :=
  lsat (fun r => match r with (b, lo, hi) => Mem.range_perm m b lo hi k p end).

Global Instance cklr_free_perm R w:
  Monotonic
    (@Mem.free)
    (forallr m1 m2 : match_mem R w,
       %% rel_impl (ptrrange_perm m1 Cur Freeable) (ptrrange_inject (mi R w)) ++>
       option_le ((<> match_mem R)%klr w)).
Proof.
  rstep.
  repeat rstep.
  destruct x as [[b1 lo1] hi1], y as [[b2 lo2] hi2]; simpl.
  destruct (Mem.free v1 b1 lo1 hi1) eqn:Hfree; repeat rstep.
  assert (ptrrange_perm v1 Cur Freeable (b1, lo1, hi1) (b2, lo2, hi2)).
  {
    eapply Mem.free_range_perm.
    eassumption.
  }
  rewrite <- Hfree.
  rauto.
Qed.

(** We can restate the monotonicity properties for most memory
  operations using [match_rptr] instead of [match_ptr]. *)

Global Instance cklr_perm_rptr R w:
  Monotonic
    (@Mem.perm)
    (match_mem R w ++> % rptr_inject (mi R w) ++> - ==> - ==> impl).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr k p.
  simpl. intros H. generalize H. repeat rstep.
  eapply rptr_ptr_inject_perm; eauto.
Qed.

Global Instance cklr_load_rptr R:
  Monotonic
    (@Mem.load)
    (|= - ==> match_mem R ++> % rptr_inject @@ [mi R] ++>
     k1 option_le (Val.inject @@ [mi R])).
Proof.
  intros w chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1 | ] eqn:Hload; try rauto.
  rewrite <- Hload.
  eapply rptr_ptr_inject_valid_access in Hptr; eauto with mem.
  rauto.
Qed.

Global Instance cklr_store_rptr R:
  Monotonic
    (@Mem.store)
    (|= - ==> match_mem R ++> % rptr_inject @@[mi R] ++> Val.inject @@[mi R] ++>
     k1 option_le (<> match_mem R)).
Proof.
  intros w chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv.
  simpl.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1' | ] eqn:Hm1'; [ | rauto].
  rewrite <- Hm1'.
  eapply rptr_ptr_inject_valid_access in Hptr; eauto with mem.
  rauto.
Qed.

Global Instance cklr_loadbytes_rptr R:
  Monotonic
    (@Mem.loadbytes)
    (|= match_mem R ++> % rptr_inject @@ [mi R] ++> - ==>
     k1 option_le (k1 list_rel (memval_inject @@ [mi R]))).
Proof.
  intros w m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr sz.
  simpl.
  assert (sz <= 0 \/ 0 < sz) as [Hsz | Hsz] by extlia.
  - rewrite !Mem.loadbytes_empty by assumption.
    rauto.
  - destruct (Mem.loadbytes m1 b1 ofs1 sz) eqn:H; [ | rauto].
    rewrite <- H.
    apply Mem.loadbytes_range_perm in H.
    eapply rptr_ptr_inject_valid_access in Hptr; eauto.
    + rauto.
    + split.
      * instantiate (2 := Mint8unsigned). simpl.
        intros ofs Hofs. eapply H. extlia.
      * simpl.
        apply Z.divide_1_l.
Qed.

Global Instance valid_pointer_match R w:
  Monotonic
    (@Mem.valid_pointer)
    (match_mem R w ++> % rptr_inject (mi R w) ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl.
  destruct (Mem.valid_pointer m1 _ _) eqn:H1.
  - eapply rptr_ptr_inject_weak_valid_pointer in Hptr;
      eauto using Mem.valid_pointer_implies.
    transport H1.
    rewrite H1.
    reflexivity.
  - rauto.
Qed.

Global Instance weak_valid_pointer_match R w:
  Monotonic
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % rptr_inject (mi R w) ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
  simpl.
  destruct (Mem.weak_valid_pointer m1 _ _) eqn:Hwvp1.
  - eapply rptr_ptr_inject_weak_valid_pointer in Hptr; eauto.
    transport Hwvp1.
    rewrite Hwvp1.
    reflexivity.
  - rauto.
Qed.

Global Instance valid_pointer_weaken_match R w:
  Related
    (@Mem.valid_pointer)
    (@Mem.weak_valid_pointer)
    (match_mem R w ++> % rptr_inject (mi R w) ++> Bool.leb).
Proof.
  intros m1 m2 Hm [b1 ofs1] [b2 ofs2] H.
  simpl.
  transitivity (Mem.weak_valid_pointer m1 b1 ofs1).
  - unfold Mem.weak_valid_pointer.
    destruct (Mem.valid_pointer m1 b1 ofs1); simpl; eauto.
  - rauto.
Qed.


(** * Pointer comparisons *)

(** ** Preliminaries *)

(* Machine pointer version of [cklr_no_overlap]. This is similar to
  [Mem.different_pointers_inject], and is necessary for comparing
  valid pointers of different memory blocks that inject into the same
  block. *)

Lemma cklr_different_pointers_inject R w:
  forall m m' b1 ofs1 b2 ofs2 b1' ofs1' b2' ofs2',
    match_mem R w m m' ->
    b1 <> b2 ->
    Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    ptrbits_inject (mi R w) (b1, ofs1) (b1', ofs1') ->
    ptrbits_inject (mi R w) (b2, ofs2) (b2', ofs2') ->
    b1' <> b2' \/ ofs1' <> ofs2'.
Proof.
  intros until ofs2'.
  intros Hm Hb Hptr1 Hptr2 Hptr1' Hptr2'.
  eapply ptrbits_rptr_inject_unsigned, rptr_ptr_inject_weak_valid_pointer in Hptr1';
    eauto using Mem.valid_pointer_implies.
  eapply ptrbits_rptr_inject_unsigned, rptr_ptr_inject_weak_valid_pointer in Hptr2';
    eauto using Mem.valid_pointer_implies.
  eapply Mem.valid_pointer_nonempty_perm in Hptr1.
  eapply Mem.valid_pointer_nonempty_perm in Hptr2.
  inv Hptr1'. inv Hptr2'.
  edestruct cklr_no_overlap; eauto using Mem.perm_implies, Mem.perm_cur_max.
  right.
  congruence.
Qed.

(** Comparisons involving pointers are tricky. This is because the
  result may be true, false, or undefined depending on whether the
  pointers being compared are valid, and whether they're in the same
  block. In case we actually end up comparing offsets of related
  pointers, we have to handle the complications introduced by
  modular arithmetic. *)

(** *** Comparing blocks *)

(* XXX: introduces uninstantiated existentials *)
Global Instance match_ptrbits_block_rstep f b1 b2 ofs1 ofs2:
  RStep
    (ptrbits_inject f (b1, ofs1) (b2, ofs2))
    (block_inject f b1 b2) | 100.
Proof.
  red.
  apply ptrbits_block_inject.
Qed.

Global Instance eq_block_rel f:
  Monotonic
    (@eq_block)
    (forallr b1 b1' : block_inject f,
     forallr b2 b2' : block_inject f,
     sumbool_le).
Proof.
  intros b1 b2 Hb b1' b2' Hb'.
  destruct (eq_block b1 b1'); repeat rstep.
  destruct (eq_block b2 b2'); repeat rstep.
  elim n.
  subst.
  eapply block_inject_functional; eauto.
Qed.

(** *** Comparing offsets *)

Lemma ptrofs_eq_Z_eqb x y:
  Ptrofs.eq x y = Z.eqb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
Proof.
  apply eq_iff_eq_true.
  rewrite Z.eqb_eq.
  unfold Ptrofs.eq.
  clear; destruct (zeq _ _); intuition congruence.
Qed.

Lemma Z_eqb_shift x y d:
  Z.eqb (x + d) (y + d) = Z.eqb x y.
Proof.
  apply eq_iff_eq_true.
  repeat rewrite Z.eqb_eq.
  omega.
Qed.

Lemma ptrofs_ltu_Z_ltb x y:
  Ptrofs.ltu x y = Z.ltb (Ptrofs.unsigned x) (Ptrofs.unsigned y).
Proof.
  apply eq_iff_eq_true.
  rewrite Z.ltb_lt.
  unfold Ptrofs.ltu.
  clear; destruct (zlt _ _); intuition congruence.
Qed.

Lemma Z_ltb_shift x y d:
  Z.ltb (x + d) (y + d) = Z.ltb x y.
Proof.
  apply eq_iff_eq_true.
  repeat rewrite Z.ltb_lt.
  omega.
Qed.

Definition Z_cmpb c :=
  match c with
    | Ceq => Z.eqb
    | Cle => fun x y => negb (Z.ltb y x)
    | Cgt => fun x y => Z.ltb y x
    | Cge => fun x y => negb (Z.ltb x y)
    | Cne => fun x y => negb (Z.eqb x y)
    | Clt => Z.ltb
  end.

Lemma ptrofs_cmpu_Z_cmpb c u v:
  Ptrofs.cmpu c u v = Z_cmpb c (Ptrofs.unsigned u) (Ptrofs.unsigned v).
Proof.
  destruct c; simpl;
  rewrite ?ptrofs_eq_Z_eqb, ?ptrofs_ltu_Z_ltb;
  reflexivity.
Qed.

Lemma Z_cmpb_shift c x y d:
  Z_cmpb c (x + d) (y + d) = Z_cmpb c x y.
Proof.
  destruct c;
  simpl;
  rewrite ?Z_eqb_shift, ?Z_ltb_shift;
  reflexivity.
Qed.

Global Instance ptrofs_eq_rintro f xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (ptrbits_inject f (xb1, xofs1) (xb2, xofs2) /\
     ptrbits_inject f (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1)
    eq
    (Ptrofs.eq xofs1 yofs1)
    (Ptrofs.eq xofs2 yofs2).
Proof.
  intros (Hx & Hy & Hb).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  rewrite Ptrofs.translate_eq.
  reflexivity.
Qed.

Global Instance ptrofs_ltu_rintro R w m1 m2 xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (match_mem R w m1 m2 /\
     ptrbits_inject (mi R w) (xb1, xofs1) (xb2, xofs2) /\
     ptrbits_inject (mi R w) (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1 /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
    eq
    (Ptrofs.ltu xofs1 yofs1)
    (Ptrofs.ltu xofs2 yofs2).
Proof.
  intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  rewrite !ptrofs_ltu_Z_ltb.
  erewrite !cklr_weak_valid_pointer_address_inject by eauto.
  rewrite Z_ltb_shift.
  reflexivity.
Qed.

Global Instance ptrofs_cmpu_rintro R w m1 m2 c xb1 xb2 xofs1 xofs2 yb1 yb2 yofs1 yofs2:
  RIntro
    (match_mem R w m1 m2 /\
     ptrbits_inject (mi R w) (xb1, xofs1) (xb2, xofs2) /\
     ptrbits_inject (mi R w) (yb1, yofs1) (yb2, yofs2) /\
     xb1 = yb1 /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned xofs1) = true /\
     Mem.weak_valid_pointer m1 xb1 (Ptrofs.unsigned yofs1) = true)
    eq
    (Ptrofs.cmpu c xofs1 yofs1)
    (Ptrofs.cmpu c xofs2 yofs2).
Proof.
  intros (Hm & Hx & Hy & Hb & Hxv & Hyv).
  inversion Hx.
  inversion Hy.
  subst.
  assert (delta0 = delta) by congruence; subst.
  rewrite !ptrofs_cmpu_Z_cmpb.
  erewrite !cklr_weak_valid_pointer_address_inject by eauto.
  rewrite Z_cmpb_shift.
  reflexivity.
Qed.

(** *** Folding [Mem.weak_valid_pointer] *)

(** One last complication is that [Val.cmpu] and [Val.cmplu] can
  formally accept an arbitrary [valid_pointer] predicate, but our
  proof relies on the fact that they are actually passed
  [Mem.valid_pointer] applied to related memories. Thankfully, we
  can express this constraint with the relation
  [(match_mem R p) !! Mem.valid_pointer]. We also use the following
  instance of [RStep] to automatically fold the derived
  [weak_valid_pointer] into the actual [Mem.weak_valid_pointer] that
  we know things about. *)

Lemma fold_weak_valid_pointer_rstep Rb m1 m2 b1 b2 ofs1 ofs2:
  RStep
    (Rb (Mem.weak_valid_pointer m1 b1 ofs1)
        (Mem.weak_valid_pointer m2 b2 ofs2))
    (Rb (Mem.valid_pointer m1 b1 ofs1 || Mem.valid_pointer m1 b1 (ofs1 - 1))
        (Mem.valid_pointer m2 b2 ofs2 || Mem.valid_pointer m2 b2 (ofs2 - 1))).
Proof.
  intros H.
  exact H.
Qed.

Hint Extern 1
  (RStep _ (_ (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _)
              (Mem.valid_pointer _ _ _ || Mem.valid_pointer _ _ _))) =>
  eapply fold_weak_valid_pointer_rstep : typeclass_instances.

(** ** Relational properties *)

(** With this we can finally prove the relational properties we want
  for comparison operators involving unsigned integers. *)

Global Instance val_cmpu_bool_inject R w:
  Monotonic
    (@Val.cmpu_bool)
    ((match_mem R w) !! Mem.valid_pointer ++> - ==>
     Val.inject (mi R w) ++> Val.inject (mi R w) ++> option_le eq).
Proof.
  intros ? ? H.
  destruct H.
  unfold Val.cmpu_bool.

  repeat rstep.
  - destruct b4.
    + rdestruct_remember.
      repeat rstep;
      subst;
      repeat match goal with
        | H: _ && _ = true |- _ =>
          apply andb_true_iff in H;
          destruct H
      end;
      assumption.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in n; eauto.
          destruct n; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.

  - destruct b4.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs3 <> ofs2).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in H7; eauto.
          destruct H7; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.
    + repeat rstep.
Qed.

Global Instance val_cmplu_bool_inject R w:
  Monotonic
    (@Val.cmplu_bool)
    ((match_mem R w) !! Mem.valid_pointer ++> - ==>
     Val.inject (mi R w) ++> Val.inject (mi R w) ++> option_le eq).
Proof.
  intros ? ? H.
  destruct H.
  unfold Val.cmplu_bool.

  repeat rstep.
  - destruct b4.
    + rdestruct_remember.
      repeat rstep;
      subst;
      repeat match goal with
        | H: _ && _ = true |- _ =>
          apply andb_true_iff in H;
          destruct H
      end;
      assumption.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in n; try eassumption.
          destruct n; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.

  - destruct b4.
    + subst.
      destruct (Mem.valid_pointer x b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer x b0 (Ptrofs.unsigned ofs0)) eqn:Hvp.
      * generalize Hvp.
        transport Hvp.
        intros Hvp'.
        setoid_rewrite Hvp.
        assert (ofs2 <> ofs3).
        {
          apply andb_prop in Hvp.
          apply andb_prop in Hvp'.
          destruct Hvp, Hvp'.
          eapply (cklr_different_pointers_inject R w) in H6; try eassumption.
          destruct H6; try congruence.
        }
        destruct x0; simpl; repeat rstep;
        rewrite Ptrofs.eq_false; eauto.
      * rauto.
    + repeat rstep.
Qed.

Global Instance val_cmpu_inject R w:
  Monotonic
    (@Val.cmpu)
    ((match_mem R w) !! Mem.valid_pointer ++>
     - ==> Val.inject (mi R w) ++> Val.inject (mi R w) ++> Val.inject (mi R w)).
Proof.
  unfold Val.cmpu. rauto.
Qed.

Global Instance val_cmplu_inject R w:
  Monotonic
    Val.cmplu
    ((match_mem R w) !! Mem.valid_pointer ++> - ==> Val.inject (mi R w) ++>
     Val.inject (mi R w) ++> option_le (Val.inject (mi R w))).
Proof.
  unfold Val.cmplu. rauto.
Qed.


(** * Tactics *)

(** Here we define some tactics which may be useful when building up
  on our simulation relation tookits. *)

(* Inverse hypothese for some relations when the left-hand side has a
  specific form. For now, we use an ad-hoc tactic, but maybe we could
  find a way to strengthen the relators associated with [nil], [cons],
  [Vint], [Vptr], etc. to express the properties used here. *)

Ltac inverse_hyps :=
  repeat
    lazymatch goal with
      | H: list_rel ?R (?x :: ?xs) ?yl |- _ =>
        inversion H; clear H; subst
      | H: list_rel ?R nil ?yl |- _ =>
        inversion H; clear H; subst
      | H: Val.inject ?f (Vint _) ?y |- _ =>
        inversion H; clear H; subst
      | H: Val.inject ?f (Vlong _) ?y |- _ =>
        inversion H; clear H; subst
      | H: Val.inject ?f (Vfloat _) ?y |- _ =>
        inversion H; clear H; subst
      | H: Val.inject ?f (Vsingle _) ?y |- _ =>
        inversion H; clear H; subst
      | H: Val.inject ?f (Vptr _ _) ?y |- _ =>
        inversion H; clear H; subst
    end.

(** Another common need is to solve a goal which consists in [set_rel]
  used in conjunction with an inductive type. The [deconstruct] tactic
  destructs a hypothesis [H], and for each generated subgoal passes
  the corresponding constructor to the continuation k. *)

Ltac head m :=
  lazymatch m with
    | ?x _ => head x
    | ?x => constr:(x)
  end.

Ltac deconstruct H k :=
  let HH := fresh in
  destruct H eqn:HH;
  lazymatch type of HH with
    | _ = ?cc =>
      let c := head cc in
      clear HH; k c
  end.

(** We can use that to build a systematic way to solve goals which
  related two elements of an inductive type with [set_rel]. Namely,
  destruct the hypothesis which states the left-hand side is in the
  set, then for each branch transport all of the premises and apply
  the same constructor again. *)

Ltac solve_set_rel :=
  lazymatch goal with
    | |- set_le _ _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eexists; split; [eapply c; eauto | repeat rstep]) in
      intros ? H;
      deconstruct H reconstruct
    | |- impl _ _ =>
      let H := fresh in
      let reconstruct c :=
        idtac "Using constructor" c;
        clear H;
        split_hyps;
        inverse_hyps;
        transport_hyps;
        try (eapply c; eauto) in
      intros H;
      deconstruct H reconstruct
    | |- _ =>
      intro; solve_set_rel
  end.

(** This can be useful when [rel_curry] is involved *)
Ltac eexpair :=
  lazymatch goal with
    | |- @ex (prod ?T1 ?T2) _ =>
      let xv := fresh in evar (xv: T1);
      let x := eval red in xv in clear xv;
      let yv := fresh in evar (yv: T2);
      let y := eval red in yv in clear yv;
      exists (x, y); simpl
  end.

(** The following instances are useful as an interface between coqrel
  and Compcert. *)

Global Instance list_forall2_rel {A B} (R: rel A B):
  Related (list_forall2 R) (list_rel R) subrel.
Proof.
  induction 1; econstructor; eauto.
Qed.

Global Instance list_rel_forall2 {A B} (R: rel A B):
  Related (list_rel R) (list_forall2 R) subrel.
Proof.
  induction 1; econstructor; eauto.
Qed.

(** Translate relations expressed in terms of specific CKLRs to the
  corresponding CompCert definition. *)

Ltac uncklr :=
  autorewrite with cklr in *.
