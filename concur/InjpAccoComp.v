Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject InjectFootprint.

Require Import CallconvBig.

(** * The proof of injp ⊑ injp ⋅ injp starts from here *)


Lemma inject_implies_image_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_image_in f (Mem.support m2).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_2 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

(* Injection implies domain is in the support *)
Lemma inject_implies_dom_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_dom_in f (Mem.support m1).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_1 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

Lemma inject_dom_in_inv: forall f s b,
    inject_dom_in f s -> ~sup_In b s -> f b = None.
Proof.
  intros. destruct (f b) eqn:?. destruct p.
  apply H in Heqo. congruence. auto.
Qed.

(** * Step1: The Construction of meminj j1' j2' *)

(** meminj operations *)
Definition meminj_add (f:meminj) b1 r:=
  fun b => if (eq_block b b1) then Some r else f b.

Lemma meminj_add_new: forall f a b,
    meminj_add f a b a = Some b.
Proof.
  intros. unfold meminj_add. rewrite pred_dec_true; auto.
Qed.

Lemma meminj_add_diff: forall j a b a' ofs,
    a <> b ->
    meminj_add j a (a',ofs ) b = j b.
Proof.
  intros. unfold meminj_add. destruct eq_block; congruence.
Qed.

Lemma meminj_add_incr: forall f a b,
    f a = None -> inject_incr f (meminj_add f a b).
Proof.
  intros. intro. unfold meminj_add. intros.
  destruct eq_block. subst. congruence. eauto.
Qed.

Lemma meminj_add_compose : forall f1 f2 a b c o,
    (forall b0 z, ~ f1 b0 = Some (b,z)) ->
    compose_meminj (meminj_add f1 a (b,0)) (meminj_add f2 b (c,o)) =
    meminj_add (compose_meminj f1 f2) a (c,o).
Proof.
  intros. apply Axioms.extensionality. intro x.
  unfold compose_meminj, meminj_add.
  destruct (eq_block x a). rewrite pred_dec_true; eauto.
  destruct (f1 x) eqn: Hf1; eauto. destruct p.
  destruct (eq_block b0 b); eauto. subst. apply H in Hf1. inv Hf1.
Qed.

Definition fresh_block_tid (s : sup) (tid : nat) :=
  let pl := nth tid (Mem.stacks s) nil in (tid, Mem.fresh_pos pl).

Program Definition sup_incr_tid (s: sup) (tid : nat) :=
  let pl := nth tid (Mem.stacks s) nil in
  Mem.mksup (Mem.update_list tid (Mem.stacks s) (Mem.fresh_pos pl :: pl)) (Mem.tid s) _.
Next Obligation.
  rewrite Mem.update_list_length. destruct s. auto.
Qed.

(** Since the global blocks are the same, we do not bother to divide them from stack blocks here.
    So the valid assertion here allows tid to be 0, i.e. a global block *)
Definition valid_t_sup (s: sup) (tid : nat) := (0 <= tid < length (Mem.stacks s))%nat.

Theorem sup_incr_tid_in : forall b s t,
    valid_t_sup s t ->
    sup_In b (sup_incr_tid s t) <-> b = (fresh_block_tid s t) \/ sup_In b s.
Proof.
  intros b s t Hv. red in Hv. split.
  - destruct s. unfold sup_In, sup_incr_tid. simpl.
  intros. inv H. simpl in *. unfold fresh_block_tid.
  simpl.
  destruct (Nat.eq_dec t tid0).
    + subst.
      rewrite Mem.nth_error_update_list_same in H0; eauto. inv H0. destruct H1.
      left. subst. reflexivity.
      right. econstructor; eauto. simpl.
      erewrite nth_error_nth'; eauto.
      lia.
      lia.
    + right. econstructor. simpl.
      erewrite <- Mem.nth_error_update_list_diff; eauto. lia. auto.
  - intros. destruct H.
    destruct s. simpl in *. unfold sup_incr_tid. simpl.
    unfold fresh_block_tid in H. simpl in *. subst.
    econstructor; simpl; eauto.
    apply Mem.nth_error_update_list_same; eauto. lia.
    left. auto.
    destruct s. unfold sup_incr_tid. inv H. simpl.
    destruct (Nat.eq_dec t tid0).
    subst.
    econstructor; simpl.
    rewrite Mem.nth_error_update_list_same; eauto. simpl in Hv. lia. simpl in H0.
    erewrite nth_error_nth; eauto.
    right. auto.
    econstructor; simpl in *; eauto.
    erewrite Mem.nth_error_update_list_diff; eauto. lia.
Qed.

Theorem sup_incr_tid_in1 : forall s t, valid_t_sup s t -> sup_In (fresh_block_tid s t) (sup_incr_tid s t).
Proof. intros. apply sup_incr_tid_in; auto. Qed.
Theorem sup_incr_tid_in2 : forall s t, valid_t_sup s t -> Mem.sup_include s (sup_incr_tid s t).
Proof. intros. intro. intro. apply sup_incr_tid_in; auto. Qed.

Theorem freshness_tid : forall s t, ~sup_In (fresh_block_tid s t) s.
Proof.
  intros. destruct s as [stacks tid].
  intro. inv H. simpl in H2.
  erewrite nth_error_nth in H4; eauto.
  apply Mem.freshness_pos in H4. eauto.
Qed.
(*
Fixpoint update_meminj12_thread (tid: nat) (stack: list positive) (j1 j2 j' : meminj) (si2 : sup) :=
  match stack with
  |nil => (j1, j2, si2)
  |hd::tl =>
     let b1 := (tid,hd) in
     match compose_meminj j1 j2 b1, (j' b1) with
       | None , Some (b2,ofs) =>
           let b0 := fresh_block_tid si2 tid in
         update_meminj12_thread tid tl (meminj_add j1 b1 (b0,0) )
                         (meminj_add j2 b0 (b2,ofs))
                         j' (sup_incr_tid si2 tid)
       | _,_ => update_meminj12_thread tid tl j1 j2 j' si2
       end
  end.

Fixpoint update_meminj12_threads (stacks: list (list positive)) (tid: nat) (j1 j2 j' : meminj) (si2: sup) :=
  match stacks with
  |nil => (j1, j2, si2)
  |stack :: tl =>
     match update_meminj12_thread 1%nat stack j1 j2 j' si2 with
       | ((j1',j2'),si2')  =>
           update_meminj12_threads tl (S tid) j1' j2' j' si2'
     end
  end.


Definition update_meminj12 (s1 : sup) (j1 j2 j': meminj) (si2 : sup)  :=
  update_meminj12_threads (tl (Mem.stacks s1)) (1%nat) j1 j2 j' si2.
 *)

(** The constrution of memory injections *)

 Fixpoint update_meminj12 (sd1': list block) (j1 j2 j': meminj) (si1: sup) :=
  match sd1' with
    |nil => (j1,j2,si1)
    |hd::tl =>
       let tid := fst hd in
       match compose_meminj j1 j2 hd, (j' hd) with
       | None , Some (b2,ofs) =>
         let b0 := fresh_block_tid si1 tid in
         update_meminj12 tl (meminj_add j1 hd (b0,0) )
                         (meminj_add j2 b0 (b2,ofs))
                         j' (sup_incr_tid si1 tid)
       | _,_ => update_meminj12 tl j1 j2 j' si1
       end
  end.

(* results of update_meminj*)
Definition inject_incr_no_overlap' (j j' : meminj) : Prop :=
  forall b1 b2 b1' b2' delta1 delta2,
    b1 <> b2 -> j b1 = None -> j b2 = None ->
    j' b1 = Some (b1', delta1) -> j' b2 = Some (b2',delta2) ->
    b1' <> b2'.

Definition update_add_exists (j12 j12' j': meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) ->
    exists b3 ofs3, j' b1 = Some (b3,ofs3).

Definition update_add_zero (j12 j12' : meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) -> ofs2 = 0.

Definition update_add_same (j23 j23' j12': meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    exists b1, j12' b1 = Some (b2,0) /\
    (forall b1' d, j12' b1' = Some (b2,d) -> b1' = b1).

Definition update_add_same2 (j23 j23' : meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    forall b2' ofs2',
      j23' b2' = Some (b3,ofs2') -> b2 = b2'.

(* lemmas using sup_list for update_properties *)

Definition inject_dom_in_bl (f:meminj) (bl: list block) :=
  forall b b' o, f b = Some (b', o) -> In b bl.

Definition inject_incr_disjoint_bl1 (j j':meminj) (bl1: list block) (s2: sup) :=
  forall b b' o, j b = None -> j' b = Some (b',o) ->
            ~ In b bl1 /\ ~ sup_In b' s2.

Lemma inject_dom_in_eqv: forall f s,
    inject_dom_in_bl f (Mem.sup_list s) <-> inject_dom_in f s.
Proof.
  intros. split; intro; red; intros.
  erewrite Mem.sup_list_in; eauto.
  erewrite <- Mem.sup_list_in; eauto.
Qed.

Lemma inject_incr_disjoint_eqv : forall j j' s1 s2,
    inject_incr_disjoint_bl1 j j' (Mem.sup_list s1) s2 <-> inject_incr_disjoint j j' s1 s2.
Proof.
  intros. split; intro; red; intros.
  exploit H. eauto. eauto. intros [A B].
  erewrite <- Mem.sup_list_in in A. auto.
  exploit H. eauto. eauto. intros [A B].
  erewrite Mem.sup_list_in in A. auto.
Qed.

Definition valid_t_blocks  (s1 : list block) (s2: sup) :=
  forall b, In b s1 -> valid_t_sup s2 (fst b).

Lemma update_properties':
  forall s1' bl1 j1 j2 s2 s2' j1' j2' j' s3,
    update_meminj12 s1' j1 j2 j' s2 = (j1',j2',s2') ->
    valid_t_blocks s1' s2 ->
    Mem.meminj_thread_local j1 ->
    Mem.meminj_thread_local j2 ->
    Mem.meminj_thread_local j' ->
    inject_dom_in_bl j1 bl1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint_bl1 (compose_meminj j1 j2) j' bl1 s3 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include s2 s2'
    /\ inject_image_in j1' s2'
    /\ inject_dom_in j2' s2'
    /\ inject_incr_disjoint_bl1 j1 j1' bl1 s2
    /\ inject_incr_disjoint j2 j2' s2 s3
    /\ inject_incr_no_overlap' j1 j1'
    /\ update_add_exists j1 j1' j'
    /\ update_add_zero j1 j1'
    /\ update_add_same j2 j2' j1'
    /\ Mem.meminj_thread_local j1'
    /\ Mem.meminj_thread_local j2'
    /\ Mem.match_sup s2 s2'.
(*    /\ update_add_same2 j2 j2' . *)
Proof.
  induction s1'.
  - (*base*)
    intros; inv H. repeat apply conj; try congruence; eauto.
  - (*induction*)
    intros until s3. intros UPDATE Hva Htl1 Htl2 Htl' DOMIN12 IMGIN12 DOMIN23
           INCR13 INCRDISJ13. inv UPDATE.
    destruct (compose_meminj j1 j2 a) eqn: Hja. eapply IHs1'; eauto.
    red. intros. apply Hva. right. auto.
    destruct (j' a) as [[b z]|] eqn:Hj'a; eauto.
    exploit INCRDISJ13; eauto. intros [a_notin_sd1 b_notin_si2].
    (* facts *)
    assert (MIDINCR1: inject_incr j1 (meminj_add j1 a (fresh_block_tid s2 (fst a),0))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN12 in H. congruence.
    }
    assert (MIDINCR2: inject_incr j2 (meminj_add j2 (fresh_block_tid s2 (fst a)) (b,z))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN23 in H. subst. apply freshness_tid in H. inv H.
    }
    assert (MIDINCR3: inject_incr (meminj_add (compose_meminj j1 j2) a (b,z)) j').
    {
      red. intros b0 b' o INJ. unfold meminj_add in INJ.
      destruct (eq_block b0 a). congruence. eauto.
    }
    assert (Hvaa: valid_t_sup s2 (fst a)). {
      apply Hva. left. auto.
    }
    exploit IHs1'. eauto.
    (* rebuild preconditions for induction step *)
    + red. intros. red. simpl. rewrite Mem.update_list_length. eapply Hva. right. auto.
    + red. intros. unfold meminj_add in H. destruct eq_block in H. subst. simpl in H. inv H.
      reflexivity. eapply Htl1; eauto.
    + red. intros. unfold meminj_add in H. destruct eq_block in H. subst. simpl in H. inv H.
      exploit Htl'. eauto. intro. rewrite <- H. reflexivity.
      eapply Htl2; eauto.
    + auto.
    + instantiate (1:= (a :: bl1)).
      red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      left. auto. right. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply sup_incr_tid_in1; eauto. intro. eapply sup_incr_tid_in2; eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply sup_incr_tid_in1; eauto. intro. eapply sup_incr_tid_in2; eauto.
    + rewrite meminj_add_compose; eauto.
      intros. intro. apply IMGIN12 in H. eapply freshness_tid; eauto.
    + instantiate (1:= s3). rewrite meminj_add_compose.
      red. intros b0 b' o INJ1 INJ2. unfold meminj_add in INJ1. destruct (eq_block b0 a).
      congruence. exploit INCRDISJ13; eauto. intros [A B]. split.
      intros [H|H]; congruence.
      auto.
      intros. intro. apply IMGIN12 in H. eapply freshness_tid; eauto.
    +
    intros (incr1& incr2 & sinc & imagein1 & domin2 &
              disjoint1 & disjoint2 & no_overlap & add_exists & add_zero & add_same1
                   & thread_local1 & thread_local2 & match_sup).
    repeat apply conj; eauto.
    (*incr1*)
    eapply inject_incr_trans; eauto.
    (*incr2*)
    eapply inject_incr_trans; eauto.
    (*sup_include*)
    red. intros. apply sinc. eapply sup_incr_tid_in2; eauto.
    (*disjoint1*)
    {
    red. red in disjoint1. intros b0 b' delta INJ1 INJ2.
    destruct (eq_block b0 a).
    + subst. generalize (meminj_add_new j1 a (fresh_block_tid s2 (fst a),0)). intro INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd. split. auto. apply freshness_tid.
    + exploit disjoint1. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. right. auto. intro. apply B. apply sup_incr_tid_in2; auto.
    }
    (*disjoint2*)
    {
    red. red in disjoint2. intros b0 b' delta INJ1 INJ2. set (nb := fresh_block_tid s2 (fst a)).
    destruct (eq_block b0 nb).
    + subst. generalize (meminj_add_new j2 nb (b,z)). intro INJadd. apply incr2 in INJadd.
      rewrite INJ2 in INJadd. inv INJadd. split. apply freshness_tid. auto.
    + exploit disjoint2. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. apply sup_incr_tid_in2; auto. intro. apply B. auto.
    }
    (*new_no_overlap*)
    {
    red. red in no_overlap. intros b1 b2 b1' b2' delta1 delta2 Hneq NONE1 NONE2 INJ1 INJ2.
    destruct (eq_block b1 a); destruct (eq_block b2 a).
    + congruence.
    + subst. generalize (meminj_add_new j1 a (fresh_block_tid s2 (fst a),0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ1 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff; eauto. eauto. intros [A B].
      intro. subst. apply B. apply sup_incr_tid_in1; auto.
    + subst. generalize (meminj_add_new j1 a (fresh_block_tid s2 (fst a),0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff. apply NONE1. eauto. eauto. intros [A B].
      intro. subst. apply B. apply sup_incr_tid_in1; auto.
    + eapply no_overlap. apply Hneq. rewrite meminj_add_diff; eauto.
      rewrite meminj_add_diff; eauto. eauto. eauto.
    }
    (* add_exists*)
    {
    red. red in add_exists. intros. destruct (eq_block a b1).
    + subst. eauto.
    + eapply add_exists; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_zero. intros. destruct (eq_block a b1).
      subst. generalize (meminj_add_new j1 b1 (fresh_block_tid s2 (fst b1),0)). intros INJadd.
      apply incr1 in INJadd. rewrite H1 in INJadd. inv INJadd. auto.
      eapply add_zero; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_same1. intros. destruct (eq_block b2 (fresh_block_tid s2 (fst a))).
      - subst.
      generalize (meminj_add_new j1 a (fresh_block_tid s2 (fst a),0)). intros INJadd.
      apply incr1 in INJadd. eauto. exists a. split. auto.
      intros.
      destruct (meminj_add j1 a (fresh_block_tid s2 (fst a), 0) b1') as [[b2' d']|] eqn : Hj1add.
        + destruct (eq_block b1' a). subst. auto.
          apply incr1 in Hj1add as Hj1'.
          rewrite meminj_add_diff in Hj1add; eauto.
          apply IMGIN12 in Hj1add as FRESH.
          rewrite H2 in Hj1'. inv Hj1'.
          exfalso. eapply freshness_tid; eauto.
        + exploit disjoint1; eauto. intros [A B].
          exfalso. apply B. apply sup_incr_tid_in1; eauto.
      - eapply add_same1; eauto. rewrite meminj_add_diff; eauto.
    }
    inv match_sup. unfold sup_incr_tid in H. simpl in H. rewrite Mem.update_list_length in H. auto.
    inv match_sup. auto.
    + eapply IHs1'; eauto. red. intros. apply Hva. right. auto.
Qed.

(*
Lemma update_properties: forall s1' s1 j1 j2 s2 s2' j1' j2' j' s3,
    update_meminj12 s1' j1 j2 j' s2 = (j1',j2',s2') ->
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include s2 s2'
    /\ inject_image_in j1' s2'
    /\ inject_dom_in j2' s2'
    /\ inject_incr_disjoint j1 j1' s1 s2
    /\ inject_incr_disjoint j2 j2' s2 s3
    /\ inject_incr_no_overlap' j1 j1'
    /\ update_add_exists j1 j1' j'
    /\ update_add_zero j1 j1'
    /\ update_add_same j2 j2' j1'.
(*    /\ update_add_same2 j2 j2' . *)
Proof.
  intros. exploit update_properties'; eauto.
  (*instantiate (1:= Mem.sup_list s1).
  red. intros. exploit H0; eauto. apply Mem.sup_list_in.
  instantiate (1:= s3).
  red. intros. exploit H4; eauto. intros [A B].
  split. intro. apply A. apply Mem.sup_list_in. auto. auto.
  intros (A & B & C & D & E & F & G & I & J & K & L).
  repeat apply conj; eauto.
  red. intros. exploit F; eauto. intros [X Y].
  split. rewrite Mem.sup_list_in. auto. auto.*)
Qed.
 *)

(** Lemmas to prove j' = compose_meminj j1' j2' *)
Fixpoint update_meminj sd1' j j':=
  match sd1' with
    |nil => j
    |hd::tl => match j hd, j' hd with
              |None, Some (b,ofs) => update_meminj tl (meminj_add j hd (b,ofs)) j'
              |_,_ => update_meminj tl j j'
              end
  end.


Definition meminj_sub (j:meminj) (b:block) :=
  fun b0 => if (eq_block b b0) then None else j b0.

Lemma update_meminj_old: forall s j j' b b' ofs,
  j b = Some (b', ofs) ->
  update_meminj s j j' b = Some (b',ofs).
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja.
    eauto. destruct (j' a) eqn: Hj'a. destruct p.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto.
    eauto.
Qed.

Lemma update_meminj_diff1: forall s j j' a b a' ofs,
    a <> b ->
    update_meminj s j j' b =
    update_meminj s (meminj_add j a (a',ofs)) j' b.
Proof.
  induction s; intros.
  - simpl. unfold meminj_add. destruct (eq_block b a); congruence.
  - simpl.
    destruct (j a) eqn: Hja. eauto.
    + unfold meminj_add at 1. destruct eq_block.
      -- subst. eauto.
      -- rewrite Hja. eauto.
    + unfold meminj_add at 2. destruct eq_block.
      -- subst. destruct (j' a0). destruct p.
         erewrite <- IHs; eauto.
         erewrite <- IHs; eauto.
      -- rewrite Hja. destruct (j' a). destruct p.
         destruct (eq_block a b).
         ++ subst. erewrite update_meminj_old. 2: apply meminj_add_new.
            erewrite update_meminj_old. 2: apply meminj_add_new. auto.
         ++ erewrite <- IHs; eauto.
         erewrite <- IHs with (j := (meminj_add j a0 (a', ofs))); eauto.
         ++ erewrite <- IHs; eauto.
Qed.

Lemma update_meminj_diff: forall s j j' a b,
    a <> b ->
    update_meminj s j (meminj_sub j' a) b =
    update_meminj s j j' b.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja. eauto.
    destruct (eq_block a0 a).
    + subst. unfold meminj_sub. rewrite pred_dec_true; eauto.
      (* replace (fun b0 : Block.block => if eq_block a b0 then None else j' b0) with (meminj_sub j' a); eauto. *)
      setoid_rewrite IHs. destruct (j' a).
      -- destruct p. erewrite update_meminj_diff1; eauto.
      -- auto.
      -- auto.
    + unfold meminj_sub. rewrite pred_dec_false; eauto.
      destruct (j' a). destruct p. eauto.
      eauto.
Qed.

Lemma inject_dom_in_sub: forall j a s,
    inject_dom_in_bl j (a::s) ->
    inject_dom_in_bl (meminj_sub j a) s.
Proof.
  intros.
  red. red in H. intros. unfold meminj_sub in H0.
  destruct eq_block in H0. congruence. exploit H; eauto.
  intros [A|A]. congruence. auto.
Qed.


Lemma meminj_sub_diff: forall j a b,
    a <> b -> meminj_sub j a b = j b.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma meminj_sub_none : forall j a,
    meminj_sub j a a = None.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma update_meminj_new: forall s j j' b b' ofs,
  j b = None ->
  j' b = Some (b',ofs) ->
  inject_dom_in_bl j' s ->
  update_meminj s j j' b = j' b.
Proof.
  induction s; intros.
  - simpl. apply H1 in H0. inv H0.
  - simpl.
    destruct (j a) as [[a' ofs']|]eqn:Hja.
    + (*here we know a <> b by j a <> j b*)
      generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false; congruence.
      apply inject_dom_in_sub; eauto.
      intro IH.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto. congruence. congruence.
    + destruct (eq_block a b).
      -- subst. rewrite H0. erewrite update_meminj_old. eauto.
         apply meminj_add_new.
      -- generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false.
      auto. congruence. apply inject_dom_in_sub; eauto. intro IH.
      destruct (j' a). destruct p. erewrite <- update_meminj_diff1; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
Qed.

Lemma update_meminj_none: forall s j j' b,
  j b = None ->
  j' b = None ->
  update_meminj s j j' b = None.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) as [[a' ofs']|]eqn:Hja.
    eauto. destruct (j' a) as [[a' ofs']|]eqn:Hj'a.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto. auto. eauto.
Qed.

Lemma update_meminj_eq: forall sd1' j j',
    inject_dom_in_bl j' sd1' ->
    inject_incr j j' ->
    update_meminj sd1' j j' = j'.
Proof.
  intros. apply Axioms.extensionality.
  intro x.
  destruct (j x) as [[y ofs]|] eqn: Hj.
  - erewrite update_meminj_old; eauto.
    apply H0 in Hj. congruence.
  - destruct (j' x) as [[y ofs]|] eqn: Hj'.
    erewrite update_meminj_new; eauto.
    erewrite update_meminj_none; eauto.
Qed.

Lemma update_compose_meminj : forall sd1' j1 j2 j' si1 si1' j1' j2',
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    valid_t_blocks sd1' si1 ->
    inject_image_in j1 si1 ->
    update_meminj sd1' (compose_meminj j1 j2) j' = (compose_meminj j1' j2').
Proof.
  induction sd1'; intros until j2'; intros H Hv H0.
  - inv H. simpl. auto.
  - inv H. simpl. destruct (compose_meminj) eqn : Hja.
    + eapply IHsd1'; eauto. red. intros. apply Hv. right. auto.
    + destruct (j' a) eqn: Hj'a.
      -- destruct p.
         apply IHsd1' in H2.
         rewrite <- H2. f_equal. apply Axioms.extensionality.
         intro x.
         destruct (compose_meminj j1 j2 x) eqn: Hjx.
         ++ destruct (eq_block a x).
            * congruence.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness_tid; eauto.
              ** auto.
         ++ destruct (eq_block a x).
            * subst. rewrite meminj_add_new.
              unfold compose_meminj.
              rewrite meminj_add_new. rewrite meminj_add_new. eauto.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness_tid; eauto.
              ** auto.
         ++ red. intros. red. simpl. rewrite Mem.update_list_length. eapply Hv. right. auto.
         ++ red. intros. red in H0. destruct (eq_block a b0).
            * subst. rewrite meminj_add_new in H. inv H. apply sup_incr_tid_in1; auto.
              eapply Hv. left. auto.
            * rewrite meminj_add_diff in H. exploit H0; eauto.
              intro. eapply sup_incr_tid_in2; auto. eapply Hv; eauto. left. auto. auto.
      -- eapply IHsd1'; eauto. red. intros. apply Hv. right. auto.
Qed.

Lemma update_compose: forall j1 j2 j' sd1' si1 si1' j1' j2' sd1 si2,
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    valid_t_blocks sd1' si1 ->
    inject_dom_in_bl j' sd1' ->
    inject_dom_in j1 sd1 ->
    inject_image_in j1 si1 ->
    inject_dom_in j2 si1 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' sd1 si2 ->
    j' = (compose_meminj j1' j2').
Proof.
  intros.
  exploit update_compose_meminj; eauto.
  intro A.
  exploit update_meminj_eq; eauto. intro B. congruence.
Qed.

Lemma add_from_to_dom_in : forall s1 s1' j12 j12' j',
    update_add_exists j12 j12' j' ->
    Mem.sup_include s1 s1' ->
    inject_dom_in j12 s1 ->
    inject_incr j12 j12' ->
    inject_dom_in j' s1' ->
    inject_dom_in j12' s1'.
Proof.
  intros. red. intros.
  destruct (j12 b) as [[b'' o']|] eqn: Hj12.
  + erewrite H2 in H4; eauto.
  + exploit H; eauto. intros (b3 & ofs3 & Hj'). eauto.
Qed.

(** Summerize of the memory injection composition. *)
Lemma inject_incr_inv: forall j1 j2 j' s1 s2 s3 s1',
    valid_t_blocks (Mem.sup_list s1') s2 ->
    Mem.meminj_thread_local j1 ->
    Mem.meminj_thread_local j2 ->
    Mem.meminj_thread_local j' ->
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_dom_in j' s1' ->
    Mem.sup_include s1 s1' ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    exists j1' j2' s2', j' = compose_meminj j1' j2' /\
               inject_incr j1 j1' /\
               inject_incr j2 j2' /\
               Mem.sup_include s2 s2' /\
               inject_dom_in j1' s1' /\
               inject_image_in j1' s2' /\
               inject_dom_in j2' s2' /\
               inject_incr_disjoint j1 j1' s1 s2 /\
               inject_incr_disjoint j2 j2' s2 s3 /\
               inject_incr_no_overlap' j1 j1' /\
               update_add_zero j1 j1' /\
               update_add_exists j1 j1' j' /\
               update_add_same j2 j2' j1' /\
               Mem.meminj_thread_local j1' /\
               Mem.meminj_thread_local j2' /\
               Mem.match_sup s2 s2'.
Proof.
  intros until s1'. intros Hvt Htl1 Htl2 Htl'. intros.
  destruct (update_meminj12 (Mem.sup_list s1') j1 j2 j' s2) as [[j1' j2'] s2'] eqn: UPDATE.
  exists j1' ,j2' ,s2'.
  apply inject_dom_in_eqv in H as H'.
  apply inject_dom_in_eqv in H2 as H2'.
  apply inject_incr_disjoint_eqv in H5 as H5'.
  exploit update_compose; eauto.
  intro COMPOSE.
  exploit update_properties'; eauto.
  rewrite inject_incr_disjoint_eqv.
  intros (A & B & C & D & E & F & G & I & J & K & L & M & N & P & Q).
  repeat apply conj; eauto. eapply add_from_to_dom_in; eauto.
Qed.


(* no_overlaping from update_meminj12 *)
Lemma update_meminj_no_overlap1 : forall m1' m1 m2 j1 j1',
    injp_max_perm_decrease m1 m1' ->
    inject_incr j1 j1' ->
    Mem.inject j1 m1 m2 ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    inject_incr_no_overlap' j1 j1' ->
    Mem.meminj_no_overlap j1' m1' .
Proof.
  intros m1' m1 m2 j1 j1' MPD INCR INJECT INCRDISJ INCRNOLAP.
  red. intros.
  destruct (j1 b1) as [[b1'' delta1']|] eqn : H0';
  destruct (j1 b2) as [[b2'' delta2']|] eqn : H1'.
  - (* old mappings *)
    erewrite INCR in H0; eauto. inv H0.
    erewrite INCR in H1; eauto. inv H1.
    inversion INJECT. apply inject_implies_dom_in in INJECT as DOMIN.
    eapply mi_no_overlap; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
  - (* b1 old, b2 new *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H0; eauto. inv H0.
    apply IMGIN in H0'. left. congruence.
  - (* b1 new, b2 old *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H1; eauto. inv H1.
    apply IMGIN in H1'. left. congruence.
  - (* new mappings *)
    left. eauto.
Qed.



(* properties of memory operations defined in Memory.v *)
Lemma pmap_update_diff: forall (A:Type) b f (map1 map2: NMap.t A) b',
  Mem.pmap_update b f map1 = map2 ->
  b <> b' ->
  NMap.get _ b' map1 = NMap.get _ b' map2.
Proof.
  intros. rewrite <- H. unfold Mem.pmap_update.
  rewrite NMap.gsspec. rewrite pred_dec_false; auto.
Qed.

Definition mem_memval (m:mem) b ofs : memval :=
  Maps.ZMap.get ofs (NMap.get _ b (Mem.mem_contents m)).

Lemma loc_out_of_reach_incr : forall j1 j1' m1 m2 m1' b ofs,
    loc_out_of_reach j1 m1 b ofs ->
    inject_dom_in j1 (Mem.support m1) ->
    inject_incr j1 j1' ->
    injp_max_perm_decrease m1 m1' ->
    sup_In b (Mem.support m2) ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    loc_out_of_reach j1' m1' b ofs.
Proof.
  intros. red. intros.
  destruct (j1 b0) as [[b' delta']|] eqn : Hj1b.
  - erewrite H1 in H5; eauto. inv H5.
    intro. apply H2 in H5.
    apply H in Hj1b. congruence.
    unfold Mem.valid_block. eauto.
  - exploit H4; eauto. intros [A B].
    congruence.
Qed.

(** Lemma C.6 *)
Lemma loc_out_of_reach_trans:
  forall m1 m2 m3 j1 j2 b2 ofs2 b3 delta3 k p,
    Mem.inject j1 m1 m2 ->
    Mem.inject j2 m2 m3 ->
    j2 b2 = Some (b3,delta3) ->
    Mem.perm m2 b2 ofs2 k p ->
    loc_out_of_reach j1 m1 b2 ofs2 ->
    loc_out_of_reach (compose_meminj j1 j2) m1 b3 (ofs2 + delta3).
Proof.
  intros until p. intros INJ12 INJ23 MAP2 PERM2 OUTOFREACH1.
  red.
  red in OUTOFREACH1.
  intros.
  unfold compose_meminj in H.
  destruct (j1 b0) as [[b2' delta']|] eqn: Hj1b; try congruence.
  destruct (j2 b2') as [[b3' delta'']|] eqn: Hj2b; try congruence.
  inv H.
  destruct (Mem.perm_dec m1 b0 (ofs2 + delta3 - (delta' + delta'')) Max Nonempty); auto.
  destruct (eq_block b2 b2'). subst. rewrite MAP2 in Hj2b. inv Hj2b. apply OUTOFREACH1 in Hj1b.
  replace (ofs2 + delta'' - (delta' + delta'')) with (ofs2 - delta') in p0 by lia.
  congruence.
  eapply Mem.perm_inject in Hj1b; eauto.
  inversion INJ23. exploit mi_no_overlap. apply n. eauto. eauto.
  eauto with mem. eauto. intros [A|A]. congruence. extlia.
Qed.

(** Lemma C.5 *)
Lemma memval_compose_1 : forall j1 j2 mv mv3,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j1 mv (Mem.memval_map j1 mv).
Proof.
  intros. destruct mv; simpl; try constructor.
  destruct v; simpl; try repeat constructor.
  destruct (j1 b) as [[b1 d]|] eqn : ?.
  repeat constructor. econstructor; eauto.
  inv H. inv H4. unfold compose_meminj in H1. rewrite Heqo in H1.
  congruence.
Qed.

Lemma memval_compose_2:
  forall mv mv3 j1 j2,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j2 (Mem.memval_map j1 mv) mv3.
Proof.
  intros; inv H; simpl.
  - constructor.
  - inv H0; try constructor; try constructor.
    unfold compose_meminj in H.
    destruct (j1 b1) as [[b2' delta']|] eqn:Hj1; try constructor.
    destruct (j2 b2') as [[b2'' delta'']|] eqn:Hj2; try constructor.
    inv H.
    econstructor; eauto.
    rewrite add_repr.
    rewrite Ptrofs.add_assoc. auto.
    congruence.
  - constructor.
Qed.

(** * The construction of intermidiate memory state m2' *)
Section CONSTR_PROOF.
  Variable m1 m2 m3 m1' m3': mem.
  Variable j1 j2 j1' j2': meminj.
  Variable s2': sup.
  Hypothesis ROUNC1: Mem.ro_unchanged m1 m1'.
  Hypothesis ROUNC3: Mem.ro_unchanged m3 m3'.
  Hypothesis DOMIN1: inject_dom_in j1 (Mem.support m1).
  Hypothesis DOMIN1': inject_dom_in j1' (Mem.support m1').
  Hypothesis UNCHANGE1: Mem.unchanged_on_e (loc_unmapped (compose_meminj j1 j2)) m1 m1'.
  Hypothesis UNCHANGE3: Mem.unchanged_on_e (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3'.
  Hypothesis INJ12 : Mem.inject j1 m1 m2.
  Hypothesis INJ23 : Mem.inject j2 m2 m3.
  Hypothesis INJ13': Mem.inject (compose_meminj j1' j2') m1' m3'.
  Hypothesis SUPINCL2 : Mem.sup_include (Mem.support m2) s2'.
  Hypothesis SUPINCL3 : Mem.sup_include (Mem.support m3) (Mem.support m3').
  Hypothesis INCR1 : inject_incr j1 j1'.
  Hypothesis INCR2 : inject_incr j2 j2'.
  Hypothesis INCRDISJ1 :inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2).
  Hypothesis INCRDISJ2 :inject_incr_disjoint j2 j2' (Mem.support m2) (Mem.support m3).
  Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j1 j1'.
  Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'.
  Hypothesis IMGIN1': inject_image_in j1' s2'.
  Hypothesis DOMIN2': inject_dom_in j2' s2'.
  Hypothesis ADDZERO: update_add_zero j1 j1'.
  Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2').
  Hypothesis ADDSAME : update_add_same j2 j2' j1'.
  Hypothesis THREADLOCAL1: Mem.meminj_thread_local j1'.
  Hypothesis THREADLOCAL2: Mem.meminj_thread_local j2'.
  Hypothesis MATCHSUP2: Mem.match_sup (Mem.support m2) s2'.

  (** step2 of Definition C.7, defined in common/Memory.v as memory operation *)
  Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.
  (** step3 of Definition C.7, in common/Memory.v *)
  Definition m2' := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.
  
  Lemma INJNOLAP1' : Mem.meminj_no_overlap j1' m1'.
  Proof. eapply update_meminj_no_overlap1; eauto. Qed.

  (** unchanged_on properties about m2' *)

  Lemma pmap_update_diff': forall (A:Type) b f (map: NMap.t A) b',
  b <> b' ->
  NMap.get _ b' (Mem.pmap_update b f map) = NMap.get _ b' map.
  Proof.
    intros. unfold Mem.pmap_update.
    rewrite NMap.gsspec. rewrite pred_dec_false; auto.
  Qed.

  Lemma supext_unchanged_on : forall s m m' P,
    Mem.supext s m = m' ->
    Mem.unchanged_on P m m'.
Proof.
  intros. unfold Mem.supext in H.
  destruct Mem.sup_include_dec in H.
  - constructor; inv H.
    + eauto.
    + intros. reflexivity.
    + intros. reflexivity.
  - subst. eauto with mem.
Qed.

  Lemma unchanged_on_map_block : forall m m' b,
      Mem.map_block m1 m1' j1' b m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    intros. subst.
    unfold Mem.map_block.
    destruct (j1' b) as [[b2 d]|] eqn:j1'b; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl.
    erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
    intros. erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
  Qed.

  Lemma unchanged_on_map_sup' : forall bl m m',
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    induction bl.
    - intros. inv H. simpl. eauto with mem.
    - intros. inv H. simpl.
      eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_map_block; eauto.
      eauto.
  Qed.
  
  Lemma unchanged_on_map_sup : forall s m m',
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    intros. eapply unchanged_on_map_sup'; eauto.
  Qed.

  Lemma unchanged_step2: Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m2 m2'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s2' m2). reflexivity.
    eapply unchanged_on_map_sup; eauto. reflexivity.
  Qed.
                                          
  Lemma unchanged1_step2: Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged2_step2: Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.

    Lemma unchanged_on_copy_block1 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_access_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
          - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
  Qed.

  Lemma unchanged_on_copy'1 : forall s m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block1; eauto.
      eauto.
  Qed.
  
  Lemma unchanged_on_copy'2 : forall s m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block2; eauto.
      eauto.
  Qed.
  
  Lemma unchanged1_step3: Mem.unchanged_on (loc_out_of_reach j1 m1) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'1; eauto.
  Qed.

  Lemma unchanged2_step3: Mem.unchanged_on (loc_unmapped j2) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'2; eauto.
  Qed.

  (** Lemma C.8(1) *)
  Theorem UNCHANGE21 : Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged1_step2.
    eapply unchanged1_step3.
  Qed.

  (** Lemma C.8(2) *)
  Theorem UNCHANGE22 : Mem.unchanged_on (loc_unmapped j2) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged2_step2.
    eapply unchanged2_step3.
  Qed.

  (* Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m3 m1' s2' j1 j2 j1' j2' INJ12 INJ23 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.
   *)

  Lemma m2'1_support : Mem.support m2'1 = s2'.
  Proof. unfold m2'1. erewrite Mem.step2_support; eauto. Qed.
  Lemma m2'_support : Mem.support m2' = s2'.
  Proof. unfold m2'. erewrite Mem.copy_sup_support; eauto. erewrite m2'1_support; eauto. Qed.

  Lemma copy_block_perm1 : forall m b1 o1 b2 o2 k p,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Max Nonempty ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold Mem.perm. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_access_block_result.
      destruct Mem.loc_in_reach_find as [[b1' o1']|]eqn:FIND.
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1. reflexivity.
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia. auto.
      intro. inv H3. eauto.
    - exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.

  Lemma copy_block_perm2 : forall m b2 o2 b2' k p,
      b2 <> b2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. rewrite pmap_update_diff'; eauto. reflexivity.
  Qed.

  Lemma copy_sup_perm': forall bl m b1 o1 b2 o2 k p,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    induction bl; intros.
    - inv H2.
    - simpl. destruct H2.
      + subst a.
        eapply copy_block_perm1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_perm1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_perm2; eauto.
  Qed.

  Lemma copy_sup_perm: forall s m b1 o1 b2 o2 k p,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. apply Mem.sup_list_in in H2 as H2'.
    unfold Mem.copy_sup. eapply copy_sup_perm'; eauto.
  Qed.

  Lemma copy_perm: forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. eapply copy_sup_perm; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_block_content : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
(*      Mem.perm m1 b1 o1 Max Writable ->
*)
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 =
          if (Mem.perm_dec m1 b1 o1 Max Writable) then
            Mem.memval_map j1' (mem_memval m1' b1 o1)
            else mem_memval m b2 o2.
  Proof.
    intros.
    assert (PERM1 : Mem.perm m1 b1 o1 Max Nonempty).
    {
      eapply MAXPERM1; eauto with mem.
      eapply DOMIN1; eauto.
    }
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold mem_memval. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1' o1']|] eqn:FIND.
      + 
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto with mem.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1.
      destruct Mem.perm_dec; try congruence.
      destruct Mem.perm_dec; try congruence.
      +
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia.
      eauto with mem. intro X. inv X.
    - 
      exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.
  
  Lemma copy_block_content1 : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_true; eauto.
  Qed.

  Lemma copy_block_content3 : forall m b2 o2 b2',
      b2 <> b2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold mem_memval. simpl. rewrite pmap_update_diff'; eauto.
  Qed.

  Lemma copy_block_content2 :  forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_false; eauto.
  Qed.

  Lemma copy_sup_content': forall bl m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H3.
    - simpl. destruct H3.
      + subst a.
        eapply copy_block_content1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_content1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_content3; eauto.
  Qed.
  
  Lemma copy_sup_content: forall s m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. apply Mem.sup_list_in in H3 as H3'.
    eapply copy_sup_content'; eauto.
  Qed.
  
  Lemma copy_sup_content_2: forall bl m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        ~ Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 = mem_memval m b2 o2.
  Proof.
    induction bl; intros; cbn.
    - reflexivity.
    - destruct (eq_block a b2). subst a.
      erewrite copy_block_content2; eauto.
      erewrite Mem.copy_sup_support'; eauto. 
      erewrite copy_block_content3; eauto.
  Qed.

  Lemma copy_content : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. eapply copy_sup_content; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_content_2 : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable -> ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = mem_memval m2 b2 o2.
  Proof.
    intros. etransitivity.
    unfold m2'. eapply copy_sup_content_2; eauto.
    apply m2'1_support.
    apply Mem.ro_unchanged_memval_bytes in ROUNC1.
    exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
    intros [P1 X].
    generalize unchanged_step2. intro U.
    inv U. eapply unchanged_on_contents.
    eapply Mem.valid_block_inject_2; eauto.
    replace o2 with (o1 + (o2 - o1)) by lia.
    eapply Mem.perm_inject; eauto.
  Qed.

  Lemma copy_content_inject : forall b1 o1 b2 o2,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1' b1 o1 Cur Readable ->
          Mem.perm m1 b1 o1 Max Writable ->
          ~ (j2 b2 = None) ->
          memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite copy_content; eauto.
    apply INCR1 in H as MAP1'.
    destruct (j2 b2) as [[b3 d]|] eqn : MAP2; try congruence.
    apply INCR2 in MAP2 as MAP2'.
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto. unfold compose_meminj.
    rewrite MAP1', MAP2'. reflexivity.
  Qed.

  Lemma copy_perm_1 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m1' b1 o1 k p ->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.

  Lemma copy_perm_2 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p ->
          Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.


  Lemma unchanged_on_copy_block_old : forall a m m',
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 a m = m' ->
      Mem.unchanged_on (fun b o => a <> b) m m'.
  Proof.
    intros. constructor.
    - erewrite <- Mem.copy_block_support; eauto.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
      reflexivity. reflexivity.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
  Qed.

  Lemma unchanged_on_copy_sup_old' : forall bl m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m = m' ->
      Mem.unchanged_on (fun b o => ~ In b bl) m m'.
  Proof.
    induction bl; intros.
    - inv H. simpl. eauto with mem.
    - simpl in H. set (m'0 := Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m).
      exploit IHbl. instantiate (1:= m'0). reflexivity. fold m'0 in H.
      intro UNC1. apply unchanged_on_copy_block_old in H as UNC2.
      apply Mem.copy_block_support in H as SUP1.
      constructor.
      + inversion UNC1. eapply Mem.sup_include_trans.  eauto.
        apply Mem.copy_block_support in H. rewrite H. eauto.
      + intros. etransitivity.
        inversion UNC1. eapply unchanged_on_perm.
        intro. apply H0. right. eauto. eauto.
        inversion UNC2. eapply unchanged_on_perm.
        intro. apply H0. left. subst. eauto.
        unfold m'0. unfold Mem.valid_block in *.
        erewrite Mem.copy_sup_support'; eauto.
      + intros. etransitivity.
        inversion UNC2. eapply unchanged_on_contents; eauto.
        intro. apply H0. left. eauto.
        inversion UNC1. eapply unchanged_on_perm0; eauto.
        intro. apply H0. right. auto. eauto with mem.
        inversion UNC1. eapply unchanged_on_contents.
        intro. apply H0. right. auto. eauto.
  Qed.
  
  Lemma unchanged_on_copy_sup_old : forall s m m',
      Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (fun b o => ~ sup_In b s) m m'.
  Proof.
    intros.
    unfold Mem.copy_sup in H.
    apply unchanged_on_copy_sup_old' in H.
    eapply Mem.unchanged_on_implies. apply H.
    intros. red. intro. apply H0. eapply Mem.sup_list_in; eauto.
  Qed.

  (*TODO: to mem*)
  Lemma perm_check_true1:
    forall m b o, Mem.perm m b o Max Nonempty ->
             Mem.perm_check_any  (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_any.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) Max) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.
  
  Lemma perm_check_true2:
    forall m b o, Mem.perm m b o Cur Readable ->
             Mem.perm_check_readable  (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_readable.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) Cur) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.

  Lemma subinj_dec : forall j j' b1 b2 d,
      inject_incr j j' -> j' b1 = Some (b2,d) ->
      {j b1 = Some (b2,d)} + {j b1 = None}.
  Proof.
    intros.
    destruct (j b1) as [[b' d']|] eqn:H1.
    left.
    apply H in H1. rewrite H0 in H1. inv H1. reflexivity.
    right. reflexivity.
  Qed.


  
  Lemma map_block_perm_1: forall b1 o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm (Mem.map_block m1 m1' j1' b1 m) b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold Mem.perm. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_access_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true1. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_perm_2: forall b1 b1' o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      b1 <> b1' ->
      Mem.perm (Mem.map_block m1 m1' j1' b1' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. 
    simpl. setoid_rewrite NMap.gso. reflexivity.
    assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
    - exploit INCRDISJ1; eauto.
    - intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_1' : forall bl m m' b2 o2 b1 o1 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      In b1 bl ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H.
      destruct H0.
      + subst a. rewrite <- H.
        eapply map_block_perm_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          eapply map_block_perm_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. apply H6. rewrite <- H.
          symmetry.
          eapply map_block_perm_2; eauto.
          rewrite Mem.map_sup_support'. eauto. 
  Qed.

  Lemma map_sup_rev' : forall bl m m' b2 o2 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        In b1 bl /\
        ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
    induction bl; intros.
    - inv H. simpl in H2. exfalso. apply H1. eauto with mem.
    - simpl in H.
      destruct (Mem.perm_dec (Mem.map_sup' m1 m1' j1' bl m) b2 o2 k p).
      + exploit IHbl; eauto.
        intros (b1 & o1 & A & B & C & D).
        exists b1,o1. repeat apply conj; eauto.
        right. eauto.
      + unfold Mem.map_block in H.
        destruct (j1' a) as [[b d]|] eqn:Hj1'a; try congruence.
        destruct (Mem.sup_dec); try congruence.
        destruct (Mem.sup_dec); try congruence.
        subst. unfold Mem.perm in H2. simpl in H2.
        unfold Mem.perm in n. simpl in n.
        destruct (eq_block b b2).
        -- subst. unfold Mem.pmap_update in H2.
           setoid_rewrite NMap.gss in H2; eauto.
           rewrite Mem.update_mem_access_result in H2.
           destruct Mem.perm_check_any.
           ++
           exists a, (o2 -d). repeat apply conj; eauto.
           left. auto. replace (o2 - (o2 - d)) with d by lia. auto.
           ++
           exfalso. apply n. eauto.
           ++ apply Mem.access_default.
        -- rewrite pmap_update_diff' in H2; eauto.
           unfold Mem.perm in n. exfalso. apply n. eauto.
  Qed.
  
  (*Lemma map_sup_rev : forall s m m' b2 o2 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        sup_In b1 s /\
        ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit map_sup_rev'; eauto.
    (* intros (b1 & o1 & A & B & C & D).
    exists b1, o1. repeat apply conj; eauto. apply Mem.sup_list_in; eauto. *)
  Qed.
   *)    
  Lemma map_sup_1 : forall s m m' b2 o2 b1 o1 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      sup_In b1 s ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    intros. apply Mem.sup_list_in in H0 as H0'. split; intro.
    eapply map_sup_1'; eauto with mem.
    exploit map_sup_rev'; eauto.
    intros (b1' & o1' & A & B & C & D).
    assert (b1 = b1').
    { destruct (eq_block b1 b1'). auto.
      exploit INCRNOLAP'1; eauto.
      inv INJ12; eauto. inv INJ12; eauto.
      intro. inv H6.
    }
    subst. rewrite H4 in C. inv C.
    assert (o1 = o1'). lia. subst. eauto.
  Qed.

  Lemma map_block_memval_1: forall b1 o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      mem_memval (Mem.map_block m1 m1' j1' b1 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_content_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true2. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_memval_2: forall b1 b1' o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      b1 <> b1' ->
      mem_memval (Mem.map_block m1 m1' j1' b1' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; eauto.
    destruct Mem.sup_dec; eauto.
    destruct Mem.sup_dec; eauto.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gso. reflexivity.
       assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
       destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
       ++ exploit INCRDISJ1; eauto.
       ++ intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_2 : forall bl m m' b2 o2 b1 o1,
            Mem.map_sup' m1 m1' j1' bl m = m' ->
            In b1 bl ->
            ~ sup_In b1 (Mem.support m1) ->
            Mem.support m = s2' ->
            j1' b1 = Some (b2, o2 - o1) ->
            Mem.perm m1' b1 o1 Cur Readable ->
            (mem_memval m' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H. generalize INJNOLAP1'. intro INJNOLAP1'.
      destruct H0.
      + subst a. rewrite <- H. apply map_block_memval_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          apply map_block_memval_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * exploit IHbl; eauto.
          intro. rewrite <- H5. rewrite <- H.
          eapply map_block_memval_2; eauto.
          rewrite Mem.map_sup_support'. eauto.
  Qed.
  
  Lemma supext_empty : forall b o k p,
      ~ sup_In b (Mem.support m2) ->
      ~ Mem.perm (Mem.supext s2' m2) b o k p.
  Proof.
    intros. unfold Mem.supext.
    destruct Mem.sup_include_dec.
    unfold Mem.perm. simpl.
    erewrite Mem.nextblock_noaccess. eauto. eauto.
    congruence.
  Qed.
      
                        
  Lemma step2_perm: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (forall k p, Mem.perm m1' b1 o1 k p <-> Mem.perm m2' b2 o2 k p).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    transitivity (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence.
      eauto. eauto. eauto.
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
  Qed.

  Lemma step2_perm2: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    assert (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto.
      intro. unfold m2'1 in H2. apply H3. eauto.
  Qed.

  Lemma step2_content: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      (mem_memval m2' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    exploit unchanged_on_copy_sup_old. instantiate (1:= m2'). reflexivity.
    intro UNC2.
    assert (Mem.perm m2'1 b2 o2 Cur Readable).
    { unfold m2'.
      inversion UNC2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
      eapply step2_perm; eauto. eauto with mem.
    }
    - etransitivity. inversion UNC2.
      setoid_rewrite unchanged_on_contents. reflexivity. eauto.
      eauto.
      unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_2. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))). unfold Mem.map_sup.
      reflexivity. rewrite <- Mem.sup_list_in. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto. eauto.
  Qed.

  Lemma step2_content_inject: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite step2_content; eauto.
    exploit ADDEXISTS; eauto. intros (b3 & o3 & MAP13).
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto.
  Qed.

  Lemma step2_perm1: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p ->
      Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit step2_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.
  
  (** Lemma C.10 *)
  Theorem MAXPERM2 : injp_max_perm_decrease m2 m2'.
  Proof.
    red. intros b2 o2 p VALID PERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|]eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct (j2 b2) as [[b3 d2]|] eqn: Hj2.
      + destruct LOCIN as [MAP1 PERM1_].
        exploit copy_perm_2; eauto. congruence.
        intro PERM1'.
        red in MAXPERM1. exploit MAXPERM1; eauto.
        unfold Mem.valid_block. eauto.
        intro PERM1.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
      + generalize (UNCHANGE22). intro UNC2.
        inversion UNC2. eapply unchanged_on_perm; eauto.
    - generalize (UNCHANGE21). intro UNC1.
      inversion UNC1. eapply unchanged_on_perm; eauto.
      eapply Mem.loc_in_reach_find_none; eauto.
  Qed.

  (** Lemma C.11 *)
  Theorem ROUNC2 : Mem.ro_unchanged m2 m2'.
  Proof.
    apply Mem.ro_unchanged_memval_bytes.
    red. intros b2 o2 VALID PERM2' NOPERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
      destruct (j2 b2) as [[b3 d2]|] eqn: MAP2.
      + 
        exploit copy_perm_2; eauto. congruence. intro PERM1'.
        assert (NOWRIT1: ~ Mem.perm m1 b1 o1 Max Writable).
        intro. apply NOPERM2.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        split. apply Mem.ro_unchanged_memval_bytes in ROUNC1.
        exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
        intros [READ1 ?].
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        symmetry. eapply copy_content_2; eauto. congruence.
      + generalize UNCHANGE22. intro UNC22. split; inv UNC22.
        rewrite unchanged_on_perm; eauto.
        symmetry. eapply unchanged_on_contents; eauto.
        eapply unchanged_on_perm; eauto.
    - eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
      generalize UNCHANGE21. intro UNC21.
      split; inv UNC21. rewrite unchanged_on_perm; eauto.
      symmetry. eapply unchanged_on_contents; eauto.
      eapply unchanged_on_perm; eauto.
  Qed.
    
  (** Lemma C.13 *)
  Theorem INJ12' : Mem.inject j1' m1' m2'.
  Proof.
    constructor.
    - constructor. rewrite m2'_support. constructor. admit. (*wrong*)
      inv MATCHSUP2. rewrite <- H0. destruct UNCHANGE1 as [[_ X]_].
      inv INJ12. inv mi_thread. inv Hms. congruence.
      auto.
    - constructor.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- eapply copy_perm_1; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. apply unchanged_on_perm; eauto.
             inversion INJ12. eauto.
             eapply Mem.perm_inject; eauto.
             inversion UNCHANGE1. inversion unchanged_on_e'.
             eapply unchanged_on_perm0; eauto. red. split; auto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             admit.
             unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          replace (ofs + 0) with ofs by lia.
          eapply step2_perm1; eauto. replace (ofs - ofs) with 0 by lia.
          eauto. eauto with mem.
      + intros. destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * inversion INJ12. inversion mi_inj.
          eapply mi_align; eauto.
          red. intros. exploit H0; eauto.
          intro. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          exists 0. lia.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1 b1 ofs Max Writable).
             ++ 
               eapply copy_content_inject; eauto.
               replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
             ++ generalize ROUNC2. intro ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC1.
                exploit ROUNC1; eauto.
                eapply Mem.valid_block_inject_1; eauto.
                intros [PERM1 MVAL1]. rewrite <- MVAL1.

                exploit ROUNC2; eauto.
                eapply Mem.valid_block_inject_2. apply e. eauto.
                eapply copy_perm_1; eauto with mem. instantiate (1:= ofs + delta).
                replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
                intro. eapply n. inversion INJ12.
                exploit mi_perm_inv; eauto. intros [|]. auto.
                exfalso. apply H2. eauto with mem.
                intros [PERM2 MVAL2]. rewrite <- MVAL2.
                inversion INJ12. inversion mi_inj.
                eapply memval_inject_incr; eauto.
          -- assert (PERM1 : Mem.perm m1 b1 ofs Cur Readable).
             inversion UNCHANGE1. inversion unchanged_on_e'. eapply unchanged_on_perm; eauto.
             red. split; auto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity. admit.
             unfold Mem.valid_block. eauto.
             assert (PERM2 : Mem.perm m2 b2 (ofs + delta) Cur Readable).
             eapply Mem.perm_inject; eauto.
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. rewrite unchanged_on_contents; eauto.
             inversion INJ12. 
             inversion UNCHANGE1. inversion unchanged_on_e'. rewrite unchanged_on_contents0; eauto.
             inversion mi_inj.
             eapply memval_inject_incr; eauto.
             red. split; auto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity. admit.
        * eapply step2_content_inject; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
    - intros.
      destruct (j1' b) as [[b2 d]|] eqn:?.
      exploit ADDEXISTS; eauto. inversion INJ12.
      eapply mi_freeblocks. inversion UNCHANGE1. inversion unchanged_on_e'.
      intro. apply H. apply unchanged_on_support. eauto.
      intros (b3 & ofs3 & MAP).
      inversion INJ13'. exploit mi_freeblocks; eauto.
      intro. congruence. reflexivity.
    - intros. unfold Mem.valid_block. rewrite m2'_support. eauto.
    - eapply update_meminj_no_overlap1; eauto.
    - intros. destruct (j1 b) as [[b2' d']|] eqn: Hj1b.
        * apply INCR1 in Hj1b as H'. rewrite H in H'. inv H'.
          inversion INJ12.
          eapply mi_representable; eauto.
          destruct H0.
          left. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
          right. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst. split. lia.
          generalize (Ptrofs.unsigned_range_2 ofs). lia.
    - intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1' b1 ofs Max Nonempty); eauto.
             left.
             eapply copy_perm_2; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- 
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. apply unchanged_on_perm in H0 as PERM2; eauto.
             2: inversion INJ12; eauto.
             inversion INJ12. exploit mi_perm_inv; eauto.
             intros [A|B].
             left.
             inversion UNCHANGE1. inversion unchanged_on_e'. eapply unchanged_on_perm0; eauto.
             red. split; auto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity. admit.
             unfold Mem.valid_block. eauto.
             right. intro. apply B.
             inversion UNCHANGE1. inversion unchanged_on_e'. eapply unchanged_on_perm0; eauto.
             red. split; auto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity. admit.
             unfold Mem.valid_block. eauto.
        * left. eapply step2_perm2; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
  Admitted.


  Lemma step2_perm2': forall b1 o1 b2 o2 b3 d k p,
      j1' b1 = Some (b2, o2 - o1) ->
      j2 b2 = None -> j2' b2 = Some (b3, d) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit step2_perm2; eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 H); auto.
    exploit INCRDISJ2; eauto. intros [A B].
    inversion INJ12. exploit mi_mappedblocks; eauto.
  Qed.

  (** Lemma C.14 *)
  Theorem INJ23' : Mem.inject j2' m2' m3'.
  Proof.
     assert (DOMIN2: inject_dom_in j2 (Mem.support m2)).
     eapply inject_implies_dom_in; eauto.
     assert (IMGIN2: inject_image_in j2 (Mem.support m3)).
     eapply inject_implies_image_in; eauto.
     constructor.
     - constructor. constructor. admit.
       inv MATCHSUP2. rewrite m2'_support. rewrite <- H0.
       inv INJ23. inv mi_thread. inv Hms. rewrite H2. destruct UNCHANGE3 as [[_ X]_].
       congruence.
       auto.
    - (*mem_inj*)
      constructor.
      + (*perm*)
        intros b2 b3 d2 o2 k p MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            
            exploit copy_perm_2; eauto. congruence.
            intro PERM1'.
            apply INCR1 in MAP1 as MAP1'.
            exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
            unfold compose_meminj. rewrite MAP1', MAP2'.
            reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
            auto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM2 : Mem.perm m2 b2 o2 k p).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. inversion unchanged_on_e'.  eapply unchanged_on_perm; eauto.
            red. split; auto. admit.
            inversion INJ23. eauto.
            eapply Mem.perm_inject; eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          eapply Mem.perm_inject. 2: apply INJ13'. unfold compose_meminj.
          rewrite MAP1', MAP2'. eauto. eauto.
      + (*align*)
        intros b2 b3 d2 chunk o2 p MAP2' RP2. destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
        * inversion INJ23. inversion mi_inj. eapply mi_align; eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intro. generalize MAXPERM2. intro UNC2.
          eapply UNC2; eauto. unfold Mem.valid_block in *.
          destruct (Mem.sup_dec b2 (Mem.support m2)).
          eauto.  exploit mi_freeblocks; eauto.
        *
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          inversion INJ13'. inv mi_inj.
          exploit mi_align.
          unfold compose_meminj. rewrite MAP1', MAP2'.
          replace (0 + d2) with d2 by lia. reflexivity.
          2: eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intros. eapply step2_perm2'; eauto.
          replace (ofs - ofs) with 0 by lia. eauto.
      + (*memval*)
        intros b2 o2 b3 d2 MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            apply INCR1 in MAP1 as MAP1'.
            destruct (Mem.perm_dec m1 b1 o1 Max Writable).
            ++
              exploit copy_content; eauto. eapply copy_perm_2; eauto. congruence. congruence.
              intro. setoid_rewrite H.
              eapply memval_compose_2; eauto.
              inversion INJ13'. inversion mi_inj.
              exploit mi_memval; eauto. unfold compose_meminj.
              rewrite MAP1'. rewrite MAP2'. reflexivity.
              eapply copy_perm; eauto. congruence. 
              replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
              eauto.
            ++ generalize ROUNC2. intro ROUNC2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC2.
               assert (NOWRIT2: ~ Mem.perm m2 b2 o2 Max Writable).
               intro. apply n. inversion INJ12. exploit mi_perm_inv; eauto.
               instantiate (3:= o1). replace (o1 + (o2 - o1)) with o2 by lia. eauto.
               intros [|]. eauto. congruence.
               exploit ROUNC2; eauto. intros [PERM2 MVAL2]. rewrite <- MVAL2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC3.
               assert (NOWRIT3 : ~ Mem.perm m3 b3 (o2 + d2) Max Writable).
               intro. apply NOWRIT2. inversion INJ23. exploit mi_perm_inv; eauto.
               intros [|]. eauto. exfalso. apply H0. eauto with mem.
               exploit ROUNC3; eauto. eapply Mem.valid_block_inject_2; eauto.
               exploit copy_perm_2; eauto. congruence.
               intro PERM1'.
               exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
               unfold compose_meminj. rewrite MAP1', MAP2'.
               reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
               auto.
               intros [PERM3 MVAL3]. rewrite <- MVAL3.
               inversion INJ23. inversion mi_inj. eapply memval_inject_incr; eauto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM2 : Mem.perm m2 b2 o2 Cur Readable).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (PERM3 : Mem.perm m3 b3 (o2 + d2) Cur Readable).
            eapply Mem.perm_inject; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. inversion unchanged_on_e'. erewrite unchanged_on_contents; eauto.
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            erewrite unchanged_on_contents0; eauto.
            eapply memval_inject_incr; eauto.
            inversion INJ23. inversion mi_inj. eauto.
            red. split; auto. admit.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          exploit step2_content; eauto.
          destruct (subinj_dec _ _ _ _ _ INCR1 MAP1'); auto.
          exfalso. apply n. inversion INJ12. exploit mi_mappedblocks; eauto.
          instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro.
          setoid_rewrite H.
          eapply memval_compose_2; eauto.
          inversion INJ13'. inversion mi_inj.
          eapply mi_memval; eauto.
          unfold compose_meminj.
          rewrite MAP1'. rewrite MAP2'. reflexivity.
    - intros. destruct (j2' b) as [[b3 d]|] eqn:?.
      exploit DOMIN2'; eauto.
      unfold Mem.valid_block in H.
      rewrite m2'_support in H. intro. congruence.
      reflexivity.
    - intros. destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. exploit mi_mappedblocks; eauto.
        unfold Mem.valid_block.
        intro. inversion UNCHANGE3. eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_mappedblocks; eauto.
        unfold compose_meminj. rewrite MAP1',H. reflexivity.
    - red. intros b2 b3 d2 b2' b3' d2' o2 o2' NEQ MAP2 MAP2' PERM2 PERM2'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2); destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + inversion INJ23. eapply mi_no_overlap; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit ADDSAME. apply e. all: eauto. intros [b1 [MAP1 SAME1]].
        exploit ADDSAME; eauto. intros [b1' [MAP1' SAME1']].
        inversion INJ13'. red in mi_no_overlap.
        assert (b1 <> b1'). intro. subst. rewrite MAP1 in MAP1'. inv MAP1'. congruence.
        eapply mi_no_overlap. eauto.
        unfold compose_meminj. rewrite MAP1, MAP2. eauto.
        unfold compose_meminj. rewrite MAP1', MAP2'. eauto.
        eapply step2_perm2'. instantiate (1:= o2).
        replace (o2 - o2) with 0 by lia. eauto. eauto. eauto. eauto.
        eapply step2_perm2'. instantiate (1:= o2').
        replace (o2' - o2') with 0 by lia. eauto. eauto. eauto. eauto.
    - intros.
      destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. eapply mi_representable; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        destruct H0.
        left. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
        right. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_representable; eauto.
        unfold compose_meminj. rewrite MAP1',H. eauto.
        destruct H0.
        left. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
        right. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
    - intros b2 o2 b3 d2 k p MAP2' PERM3'.
      generalize INJ12'. intro INJ12'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
        * eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
          destruct LOCIN as [MAP1 PERM1].
          apply INCR1 in MAP1 as MAP1'.
          inversion INJ13'. exploit mi_perm_inv.
          unfold compose_meminj. rewrite MAP1', MAP2'. reflexivity.
          instantiate (3:= o1). replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
          eauto. intros [A | B].
          left. eapply copy_perm; eauto. congruence.
          right. intro. apply B. eapply copy_perm; eauto. congruence.
        * eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
          destruct (Mem.perm_dec m2' b2 o2 Max Nonempty); auto.
          left. generalize UNCHANGE21. intro UNC2.
          assert (PERM2: Mem.perm m2 b2 o2 Max Nonempty).
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
          assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
          eapply loc_out_of_reach_trans; eauto.
          assert (PERM3: Mem.perm m3 b3 (o2 + d2) k p).
          inversion UNCHANGE3. inversion unchanged_on_e'. eapply unchanged_on_perm; eauto.
          red. split; auto. admit.
          eapply IMGIN2; eauto.
          inversion INJ23. exploit mi_perm_inv. eauto. apply PERM3.
          intros [A|B]; try congruence.
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
      + exploit INCRDISJ2; eauto. intros [A B].
        exploit ADDSAME; eauto. intros [b1 [MAP1' SAME]].
        inversion INJ13'. exploit mi_perm_inv.
        unfold compose_meminj. rewrite MAP1', MAP2'. replace (0 + d2) with d2 by lia.
        reflexivity. eauto.
        destruct (subinj_dec _ _ _ _ _ INCR1 MAP1').
        inversion INJ12. exploit mi_mappedblocks0; eauto.
        intros [P1 | P1].
        left. eapply step2_perm1; eauto. replace (o2 - o2) with 0 by lia. eauto. eauto with mem.
        right. intro. apply P1. eapply step2_perm2; eauto.
        replace (o2 - o2) with 0 by lia. eauto.
  Admitted.

  (*Lemma tid_s2 :
    Mem.tid (Mem.support m2) = Mem.tid (Mem.support m2').
  Admitted.
 *)
  
End CONSTR_PROOF.

(** main content of Lemma C.16*)
Lemma out_of_reach_trans: forall j12 j23 m1 m2 m3 m3',
    Mem.inject j12 m1 m2 ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3' ->
    Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
Proof.
  intros.
  inv H0. constructor; auto.
  - intros. eapply unchanged_on_perm; auto.
  red in H. red.
  intros b1 delta23 MAP13.  unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto.
  - intros. eapply unchanged_on_contents.
  red in H. red.
  intros b1 delta23 MAP13. unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto. auto.
Qed.

Inductive external_mid_hidden: injp_world -> injp_world -> Prop :=
|external_mid_hidden_intro :
  forall j12 j23 m1 m2 m3 Hm12 Hm23
    (** This case says that for any related external blocks [j13 b1 = Some b3],
        we have constructed b2 in m2 s.t. j12 b1 = Some b2.*)
    (Hconstr1: forall b1 b2 d, fst b2 <> Mem.tid (Mem.support m2) ->
                 j12 b1 = Some (b2, d) -> j23 b2 <> None)
    (** This cases says that for any external stack block [with permission] in m2
        and *mapped to m3* in m2, it comes from a corresponding position im m1*)
    (Hconstr2: forall b2 ofs2 b3 d2, fst b2 <> Mem.tid (Mem.support m2) ->
                Mem.perm m2 b2 ofs2 Max Nonempty -> j23 b2 = Some (b3, d2) ->
                exists b1 ofs1, Mem.perm m1 b1 ofs1 Max Nonempty /\ j12 b1 = Some (b2, ofs2 - ofs1)),
    external_mid_hidden (injpw j12 m1 m2 Hm12) (injpw j23 m2 m3 Hm23).

Lemma injp_acce_outgoing_constr: forall j12 j23 m1 m2 m3 Hm13 j13' m1' m3' (Hm12: Mem.inject j12 m1 m2) (Hm23 :Mem.inject j23 m2 m3) Hm13',
    let w1 := injpw j12 m1 m2 Hm12 in
    let w2 := injpw j23 m2 m3 Hm23 in
    injp_acce  (injpw (compose_meminj j12 j23) m1 m3 Hm13) (injpw j13' m1' m3' Hm13') -> external_mid_hidden w1 w2 ->
    exists j12' j23' m2' Hm12' Hm23',
      let w1' := injpw j12' m1' m2' Hm12' in
      let w2' := injpw j23' m2' m3' Hm23' in
      j13' = compose_meminj j12' j23' /\
      injp_acce w1 w1' /\ injp_acce w2 w2' /\ external_mid_hidden w1' w2'.
Proof.
Admitted.
(* Lemma injp_acco_outgoing_construction : forall  *)
