Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.
Require Export Memory.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Pos_Block <: BLOCK.

Definition block := positive.
Definition eq_block := peq.

End Pos_Block.

Module MemPos.
Module Mem := Mem(Pos_Block).
Include Mem.

Fixpoint find_max_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => let m' := find_max_pos tl in
             match plt hd m' with
             |left _ => m'
             |right _ => hd
             end
  end.

Theorem Lessthan: forall p l, In p l -> Ple p (find_max_pos l).
Proof.
  intros.
  induction l.
  destruct H.
  destruct H;simpl.
  - destruct (plt a (find_max_pos l)); subst a.
    + apply Plt_Ple. assumption.
    + apply Ple_refl.
  - destruct (plt a (find_max_pos l)); apply IHl in H.
    + auto.
    + eapply Ple_trans. eauto.  apply Pos.le_nlt. apply n.
Qed.

Definition fresh_block (l: list ident) := Pos.succ (find_max_pos l).

Theorem freshness : forall s, ~In (fresh_block s) s.
Proof.
  intros. unfold fresh_block.
  intro.
  apply Lessthan in H.
  assert (Plt (find_max_pos s) (Pos.succ (find_max_pos s))). apply Plt_succ.
  assert (Plt (find_max_pos s) (find_max_pos s)). eapply Plt_Ple_trans. eauto. auto.
  apply Plt_strict in H1.
  auto.
Qed.

Lemma fresh_ne : forall (b:block)(s:sup), In b s -> b <> fresh_block s.
Proof.
  intros. destruct (eq_block b (fresh_block s)).
  - rewrite e in H. apply freshness in H. destruct H.
  - auto.
Qed.

End MemPos.

(*
 Opaque MemPos.alloc MemPos.free MemPos.store MemPos.load MemPos.storebytes MemPos.loadbytes.

 Hint Resolve
  MemPos.valid_not_valid_diff
  MemPos.perm_implies
  MemPos.perm_cur
  MemPos.perm_max
  MemPos.perm_valid_block
  MemPos.range_perm_implies
  MemPos.range_perm_cur
  MemPos.range_perm_max
  MemPos.valid_access_implies
  MemPos.valid_access_valid_block
  MemPos.valid_access_perm
  MemPos.valid_access_load
  MemPos.load_valid_access
  MemPos.loadbytes_range_perm
  MemPos.valid_access_store
  MemPos.perm_store_1
  MemPos.perm_store_2
  MemPos.store_valid_block_1
  MemPos.store_valid_block_2
  MemPos.store_valid_access_1
  MemPos.store_valid_access_2
  MemPos.store_valid_access_3
  MemPos.storebytes_range_perm
  MemPos.perm_storebytes_1
  MemPos.perm_storebytes_2
  MemPos.storebytes_valid_access_1
  MemPos.storebytes_valid_access_2
  MemPos.storebytes_valid_block_1
  MemPos.storebytes_valid_block_2
  MemPos.valid_block_alloc
  MemPos.fresh_block_alloc
  MemPos.valid_new_block
  MemPos.perm_alloc_1
  MemPos.perm_alloc_2
  MemPos.perm_alloc_3
  MemPos.perm_alloc_4
  MemPos.perm_alloc_inv
  MemPos.valid_access_alloc_other
  MemPos.valid_access_alloc_same
  MemPos.valid_access_alloc_inv
  MemPos.range_perm_free
  MemPos.free_range_perm
  MemPos.valid_block_free_1
  MemPos.valid_block_free_2
  MemPos.perm_free_1
  MemPos.perm_free_2
  MemPos.perm_free_3
  MemPos.valid_access_free_1
  MemPos.valid_access_free_2
  MemPos.valid_access_free_inv_1
  MemPos.valid_access_free_inv_2
  MemPos.unchanged_on_refl
: mem. *)

(** * Difinition of Nominal Memory Model with Structured Memory Space **)

Definition path := list nat.

Definition fid := option ident. (*None means external function*)

Lemma nat_eq: forall n1 n2 :nat, {n1=n2} + {n1<>n2}.
Proof.
  intros.
  destruct (Nat.eqb n1 n2) eqn:?.
  apply Nat.eqb_eq in Heqb. left. auto.
  apply Nat.eqb_neq in Heqb. right. auto.
Qed.

Lemma beq : forall b1 b2:bool, {b1=b2}+{b1<>b2}.
Proof.
  intros.
  destruct (eqb b1 b2) eqn:?.
  rewrite eqb_true_iff in Heqb. auto.
  rewrite eqb_false_iff in Heqb. auto.
Qed.

Definition eq_path := list_eq_dec nat_eq.

Definition fid_eq : forall fi1 fi2 : fid, {fi1=fi2} + {fi1<>fi2}.
Proof.
  intros.
  destruct fi1; destruct fi2.
  + destruct (peq i i0). left. congruence. right. congruence.
  + right. congruence.
  + right. congruence.
  + left. congruence.
Qed.

Module Struc_Block <: BLOCK.

Inductive block' :=
  |Stack : fid -> path -> positive -> block'
  |Global : ident -> block'.

Definition block := block'.

Theorem eq_block : forall (x y:block),{x=y}+{x<>y}.
Proof.
  intros. destruct x; destruct y; try(right; congruence).
  - (destruct (eq_path p p1)); try (right; congruence).
    destruct (peq p0 p2); try (right; congruence).
    destruct (fid_eq f f0). left. congruence. right. congruence.
  - destruct (peq i i0). left. congruence. right. congruence.
Qed.

End Struc_Block.

Section STREE.

Fixpoint fresh_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => let m' := fresh_pos tl in
             match plt hd m' with
             |left _ => m'
             |right _ => hd +1
             end
  end.

Lemma Lessthan: forall b l, In b l -> Plt b (fresh_pos l).
Proof.
  intros.
  induction l.
  destruct H.
  destruct H;simpl.
  - destruct (plt a (fresh_pos l)); subst a.
    auto.
    apply Pos.lt_add_r.
  - destruct (plt a (fresh_pos l)); apply IHl in H.
    + auto.
    + eapply Plt_trans. eauto.
      apply Pos.le_nlt in n.

      apply Pos.le_lteq in n. destruct n.
      eapply Plt_trans. eauto.
      apply Pos.lt_add_r.
      subst.
      apply Pos.lt_add_r.
Qed.


Lemma fresh_notin : forall l, ~In (fresh_pos l) l.
Proof.
  intros. intro. apply Lessthan in H.
  unfold fresh_pos in H. extlia.
Qed.

Import List.ListNotations.

Inductive stree : Type :=
  |Node : fid -> (list positive)  -> list stree -> option stree -> stree.

Fixpoint cdepth (t:stree) : nat :=
  match t with
    |Node fid bl tl (Some hd) => S (cdepth hd)
    |Node fid bl tl None => O
  end.

(* well-founded induction *)

Fixpoint depth (t:stree) : nat :=
  match t with
    |Node fid bl tl head =>
     let d_head := option_map depth head in
     let d_list := map depth tl in
     let f := (fun n1 n2 => if Nat.leb n1 n2 then n2 else n1) in
     match d_head with
       |None => fold_right f O d_list + 1
       |Some n => fold_right f n d_list + 1
     end
  end.

Definition substree (t1 t2 : stree) : Prop :=
  match t2 with
    |Node fid bl tl head => head = Some t1 \/ In t1 tl end.

Lemma substree_depth : forall t1 t2, substree t1 t2 ->
                                ((depth t1) < (depth t2))%nat.
Proof.
  intros. unfold substree in H. destruct t2.
  inv H.
  - simpl. induction l0.
    + simpl. lia.
    + simpl. destr. apply Nat.leb_gt in Heqb. lia.
  - induction l0.
    + inv H0.
    + inv H0.
      simpl. repeat destr.
      apply Nat.leb_le in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
      apply Nat.leb_le in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
      apply IHl0 in H. simpl in *.
      repeat destr.
      apply Nat.leb_gt in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
Qed.

Lemma substree_wf' : forall n t, (depth t <= n)%nat -> Acc substree t.
  unfold substree; induction n; intros.
  - destruct t.
    destruct o; destruct l0.
    + simpl in H. extlia.
    + simpl in H. extlia.
    + constructor. intros. inv H0; inv H1.
    + simpl in H. extlia.
  - constructor.
    intros.
    apply substree_depth in H0.
    apply IHn. lia.
Defined.

Lemma substree_wf : well_founded substree.
  red; intro. eapply substree_wf'; eauto.
Defined.

Definition stree_ind := well_founded_induction substree_wf.

(* operations *)
Definition empty_stree := Node None [] [] None.

Fixpoint next_stree (t: stree) (id:ident) : (stree * path) :=
  match t with
  | Node b bl l None =>
    let idx := length l in
    ((Node b bl l (Some (Node (Some id) [] [] None))), [idx])
  | Node b bl l (Some t') =>
    let (t'', p) := next_stree t' id in
    (Node b bl l (Some t''), (length l) :: p)
  end.

Fixpoint next_block_stree (t:stree) : (fid * positive * path * stree) :=
  match t with
  |Node b bl l None =>
   (b, (fresh_pos bl), nil, Node b ((fresh_pos bl)::bl) l None)
  |Node b bl l (Some t') =>
   match next_block_stree t' with (pos,path,t'')
    => (pos, (length l)::path, Node b bl l (Some t''))
   end
  end.

Definition next_block_stree' (s:stree) :=
  match next_block_stree s with
    |(fid,pos,p,s') => (Struc_Block.Stack fid p pos,s')
  end.

Fixpoint return_stree (t: stree) : option (stree * path):=
  match t with
  | Node _ bl l None =>
    None
  | Node b bl l (Some t) =>
    let idx := length l in
    match return_stree t with
    | None => Some ((Node b bl (l ++ [t]) None),[idx])
    | Some (t',p') => Some ((Node b bl l (Some t')),(idx::p'))
    end
  end.

Fixpoint stree_In (fid:option ident)(p:path) (pos:positive) (t:stree) :=
  match p,t with
    |nil , Node b' bl dt _ => fid = b' /\ In pos bl
    |n::p' , Node b' bl dt None =>
     match nth_error dt n with
       |Some t' => stree_In fid p' pos t'
       |None => False
     end
    |n::p',Node b' bl dt (Some t') =>
     if (n =? (length dt))%nat then stree_In fid p' pos t' else
     match nth_error dt n with
       |Some t'' => stree_In fid p' pos t''
       |None => False
     end
  end.

Lemma node_Indec :
  forall (f f0:fid) (p:positive) (l: list positive), {f=f0 /\ In p l}+{~(f=f0/\ In p l)}.
Proof.
  intros.
  destruct (fid_eq f f0) eqn:?.
  destruct (In_dec peq p l).
  subst. auto.
  right. intro. inv H. congruence.
  right. intro. inv H. congruence.
Qed.

(* properties of the operations above *)

Definition cpath (s:stree) : path :=
  match next_block_stree s with
    |(f,pos,path,_) => path
  end.

Definition npath (s:stree)(id:ident) : path :=
  let (t,p) := next_stree s id in p.

Lemma next_stree_cdepth: forall p t t' id,
    next_stree t id = (t',p) -> cdepth t' = S (cdepth t).
Proof.
  induction p; (intros; destruct t; destruct o; simpl in H).
  destr_in H. inv H. destr_in H. inv H.
  simpl. exploit IHp; eauto. inv H. simpl. auto.
Qed.

Lemma next_block_stree_cdepth : forall p pos fid t t',
    next_block_stree t = (fid,pos,p,t') -> cdepth t' = cdepth t.
Proof.
  induction p; (intros; destruct t; destruct o; inv H; repeat destr_in H1).
  auto. simpl. exploit IHp; eauto.
Qed.

Lemma return_stree_cdepth : forall p t t',
    return_stree t = Some (t',p) -> S (cdepth t') = (cdepth t).
Proof.
  induction p; (intros; destruct t; destruct o; inv H; repeat destr_in H1).
  simpl. exploit IHp; eauto. simpl. destruct s. destruct o.
  simpl in Heqo. repeat destr_in Heqo. reflexivity.
Qed.

Lemma next_stree_cpath :
  forall p t t' id,
    next_stree t id = (t',p) ->  cpath t' = p.
Proof.
  induction p.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s id). inv H.
    simpl in H. inv H.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s id) eqn:?. inv H.
    apply IHp in Heqp0.
    unfold cpath in *. simpl in *.
    destruct (next_block_stree s0) eqn:?.
    destruct p0 eqn:?.
    destruct p1 eqn:?.
    congruence. simpl in H. inv H.
    unfold cpath. simpl. auto.
Qed.

Lemma next_stree_next_block_stree :
  forall t t' t'' id p f pos path,
    next_stree t id = (t',p) ->
    next_block_stree t' = (f,pos,path,t'') ->
    f = Some id /\ pos = 1%positive /\ path = p.
Proof.
  induction t using stree_ind. intros. destruct t. destruct o.
  - simpl in H0. destruct (next_stree s id) eqn:?. inv H0. simpl in H1.
    destruct (next_block_stree s0) eqn:?. destruct p. destruct p.
    exploit H. instantiate (1:=s). simpl. auto. eauto. eauto. inv H1.
    intros [A [B C]]. split. auto. split. auto. congruence.
  - simpl in H0. inv H0. simpl in H1. inv H1. auto.
Qed.

Lemma next_block_stree_next_block : forall s1 s2 s3 fid1 fid2 pos1 pos2 path1 path2,
      next_block_stree s1 = (fid1,pos1,path1,s2) ->
      next_block_stree s2 = (fid2,pos2,path2,s3) ->
      fid1 = fid2 /\ path1 = path2 /\ pos2 = Pos.succ pos1.
Proof.
  induction s1 using stree_ind. intros. destruct s1. destruct o.
  - simpl in H0. destruct (next_block_stree s) eqn:?. destruct p. destruct p.
    inv H0. simpl in H1.
    destruct (next_block_stree s0) eqn:?. destruct p. destruct p. inv H1.
    exploit H. instantiate (1:=s). simpl. auto. eauto. eauto.
    intros [A [B C]]. split. auto. split. rewrite B. auto. auto.
  - simpl in H0. inv H0. simpl in H1. inv H1. split. auto.
    split. auto. rewrite pred_dec_false. lia. extlia.
Qed.

Definition stree_Indec :forall tree f path p , {stree_In f path p tree}+{~stree_In f path p tree}.
Proof.
  induction tree using (well_founded_induction substree_wf ); intros.
  destruct tree; destruct path0.
  - simpl. apply node_Indec.
  - destruct o; destruct l0; simpl; repeat destr.
    + apply H. simpl. auto.
    + rewrite nth_error_nil in Heqo. congruence.
    + apply H. simpl. auto.
    + apply nth_error_in in Heqo.
      apply H. simpl. auto.
    + rewrite nth_error_nil in Heqo. congruence.
    + apply nth_error_in in Heqo.
      apply H. simpl. auto.
Qed.

Lemma stree_freshness : forall b p pos t t', next_block_stree t = (b,pos,p,t')
  -> ~ stree_In b p pos t.
Proof.
  induction p.
  - intros. destruct t. simpl in *.
    destruct o.
    destruct (next_block_stree s).
    destruct p. inv H.
    inv H.
    intro. inv H. apply fresh_notin in H1. auto.
  - intros. destruct t. simpl in *.
    destruct o.
    destruct (next_block_stree s) eqn:?.
    destruct p0. inv H.
    rewrite <- beq_nat_refl. eauto.
    inv H.
Qed.

Lemma next_block_stree_in : forall t t' path pos path' pos' f f',
        next_block_stree t = (f,pos,path,t') ->
        stree_In f' path' pos' t' <->
        ((f',path',pos') = (f,path,pos)
        \/ stree_In f' path' pos' t).
Proof.
  induction t using stree_ind. intros.
  destruct t.
  - destruct path0; destruct path';
    simpl in H0; repeat destr_in H0; simpl.
    + split; intros; inv H0.
      inv H2; auto.
      inv H1; auto. inv H1; auto.
    + split; intros; auto.
      destruct H0. inv H0. auto.
    + split; intros; auto.
      destruct H0. inv H0. auto.
    + destr.
      *
      apply beq_nat_true in Heqb. subst.
      exploit H; eauto. simpl. auto.
      intros.
      split; intros. apply H0 in H1.
      inv H1. left. inv H2. auto.
      right. auto.
      apply H0. inv H1. inv H2. auto.
      auto.
      *
      apply beq_nat_false in Heqb.
      destr.
Qed.

Lemma next_stree_in : forall p p' t t' pos b id,
    next_stree t id = (t',p') ->
    stree_In b p pos t <-> stree_In b p pos t'.
Proof.
  induction p.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s). inv H.
    simpl. reflexivity.
    simpl in H. inv H.
    simpl. reflexivity.
  - intros. destruct t. destruct o.
    * simpl in H. destruct (next_stree s) eqn:?. inv H.
      eapply IHp in Heqp0.
      simpl.
      destruct (a =? Datatypes.length l0)%nat. eauto.
      destruct (nth_error l0 a). reflexivity. split; auto.
    * simpl in H. inv H. simpl.
      destruct (a =? Datatypes.length l0)%nat eqn:H.
      assert (nth_error l0 a = None).
      apply nth_error_None. apply beq_nat_true in H.
      subst. lia. rewrite H0. destruct p.
      simpl. split. intro. inv H1. intros [H1 H2]. congruence.
      simpl. destruct n; reflexivity.
      destruct (nth_error l0 a); reflexivity.
Qed.

Lemma return_stree_in : forall s s' path p pos b,
    return_stree s = Some (s',path) ->
    stree_In b p pos s <-> stree_In b p pos s'.
Proof.
  induction s using stree_ind. intros.
  destruct s. destruct o.
  - simpl in H0. repeat destr_in H0;
    destruct p; simpl. reflexivity.
    destr. eapply H; eauto. simpl. auto. reflexivity.
    destr. apply beq_nat_true in Heqb0. subst.
    rewrite nth_error_app2. rewrite Nat.sub_diag.
    reflexivity. lia.
    apply beq_nat_false in Heqb0.
    destruct (n <? Datatypes.length l0)%nat eqn:H1.
    rewrite nth_error_app1. destr; auto.
    apply Nat.ltb_lt. auto.
    apply Nat.ltb_ge in H1.
    assert (nth_error (l0++[s]) n = None).
    apply nth_error_None.
    rewrite app_length. simpl. lia. rewrite H0.
    assert (nth_error l0 n = None).
    apply nth_error_None. lia. rewrite H2.
    reflexivity.
  - inv H0.
Qed.

Inductive struct_eq : stree -> stree -> Prop :=
  |struct_eq_leaf : forall fi bl1 bl2,
      struct_eq (Node fi bl1 nil None) (Node fi bl2 nil None)
  |struct_eq_dead_node :
     forall fi bl1 bl2 tl1 tl2,
       list_forall2 struct_eq tl1 tl2 ->
       struct_eq (Node fi bl1 tl1 None) (Node fi bl2 tl2 None)
  |struct_eq_active_node :
     forall fi bl1 bl2 tl1 tl2 head1 head2,
       list_forall2 struct_eq tl1 tl2 ->
       struct_eq head1 head2 ->
       struct_eq (Node fi bl1 tl1 (Some head1)) (Node fi bl2 tl2 (Some head2)).

Theorem struct_eq_refl : forall s , struct_eq s s.
Proof.
  induction s using stree_ind.
  intros. destruct s.
  destruct o; destruct l0.
  - apply struct_eq_active_node. constructor.
    apply H. simpl. left. auto.
  - apply struct_eq_active_node.
    {
      constructor. apply H. simpl. auto.
      induction l0. constructor.
      constructor. apply H. simpl. auto.
      apply IHl0. intros. apply H.
      simpl in H0. simpl. inv H0. auto. inv H1; auto.
    }
    apply H. simpl. auto.
  - constructor.
  - apply struct_eq_dead_node.
    constructor. apply H. simpl. auto.
    induction l0. constructor.
    constructor. apply H. simpl. auto.
    apply IHl0. intros.
    apply H. simpl. simpl in H0.
    destruct H0. inv H0. destruct H0; auto.
Qed.

Lemma list_forall2_struct_eq_refl : forall l,
    list_forall2 struct_eq l l.
Proof.
  induction l; constructor.
  apply struct_eq_refl. auto.
Qed.

Theorem struct_eq_comm : forall s1 s2, struct_eq s1 s2 -> struct_eq s2 s1.
Proof.
  induction s1 using stree_ind.
  intros. inv H0.
  constructor.
  constructor.
   eapply list_forall2_ind with (P:= fun t1 t2 => In t1 tl1 /\ struct_eq t1 t2) (P0:= fun l1 l2 => list_forall2 struct_eq l2 l1 ).
   constructor.
   intros. inv H0. constructor; auto. apply H. simpl. auto. auto.
   eapply list_forall2_imply; eauto.
  constructor.
   eapply list_forall2_ind with (P:= fun t1 t2 => In t1 tl1 /\ struct_eq t1 t2) (P0:= fun l1 l2 => list_forall2 struct_eq l2 l1 ).
   constructor.
   intros. inv H0. constructor; auto. apply H. simpl. auto. auto.
   eapply list_forall2_imply; eauto.
   apply H. simpl. auto. auto.
Qed.

Theorem list_forall2_trans : forall {A:Type} (l2 l1 l3 : list A) (P: A -> A -> Prop),
    (forall a1 a2 a3, In a1 l1 -> P a1 a2 -> P a2 a3 -> P a1 a3) ->
    list_forall2 P l1 l2 ->
    list_forall2 P l2 l3 ->
    list_forall2 P l1 l3.
Proof.
  induction l2; intros; inv H0; inv H1; constructor.
  eapply H. left. auto. all: eauto.
  eapply IHl2. intros. exploit H. right. eauto. all: eauto.
Qed.

Theorem struct_eq_trans : forall s1 s2 s3, struct_eq s1 s2 -> struct_eq s2 s3 -> struct_eq s1 s3.
Proof.
  induction s1 using stree_ind.
  intros. inv H0. inv H1.
  - constructor.
  - inv H5. constructor.
  - destruct s3. inv H1. inv H2. constructor.
    constructor.
    eapply list_forall2_trans.
    intros. eapply H. simpl. auto. all : eauto.
  - destruct s3. inv H1. inv H2. constructor. inv H5. constructor.
    eapply H; eauto. simpl. auto.
    constructor. inv H5. constructor. eapply H; eauto. simpl. auto.
    eapply list_forall2_trans.
    intros. eapply H. simpl. auto. all : eauto.
    eapply H; eauto. simpl. auto.
Qed.

Lemma next_block_stree_struct_eq: forall s path s' f pos,
    next_block_stree s = (f,pos,path,s') -> struct_eq s s'.
Proof.
  induction s. intros. destruct s. destruct s'.
  inv H0. destr_in H2.
  destruct (next_block_stree s) eqn:?.
  destruct p. inv H2.
  constructor. apply list_forall2_struct_eq_refl.
  eapply H; eauto. simpl. auto.
  inv H2. constructor. apply list_forall2_struct_eq_refl.
Qed.


Definition is_active (s:stree) : Prop :=
  match s with
    |Node _ _ _ (Some _) => True
    |_ => False
  end.

Lemma active_struct_eq : forall s1 s2,
    struct_eq s1 s2 ->
    is_active s1 <-> is_active s2.
Proof.
  intros. inv H; reflexivity.
Qed.

Lemma next_stree_struct_eq: forall s1 s2 id p1 p2 s1' s2',
    struct_eq s1 s2 ->
    next_stree s1 id = (s1',p1) ->
    next_stree s2 id = (s2',p2) ->
    p1 = p2 /\ struct_eq s1' s2'.
Proof.
  induction s1. intros.
  destruct s1; destruct s2. inv H0.
  - inv H1. inv H2. split. auto. constructor. constructor. constructor.
  - inv H1. inv H2. split.
    apply list_forall2_length in H4. congruence.
    constructor. auto. constructor.
  - inv H1. inv H2. destr_in H3. destr_in H1.
    inv H3. inv H1.
    apply list_forall2_length in H5 as H6.
    exploit H; eauto. simpl. auto. intros [H1 H2].
    split. congruence. constructor. auto. auto.
Qed.

Lemma return_stree_struct_eq: forall s1 s2 s1' p,
    struct_eq s1 s2 ->
    return_stree s1 = Some (s1',p) ->
    exists s2',
    return_stree s2 = Some (s2',p) /\
    struct_eq s1' s2'.
Proof.
  induction s1. intros.
  destruct s1; destruct s2. inv H0; inv H1.
  repeat destr_in H2.
  + exploit H; eauto. simpl. auto. intros (head2' & H5 & H6).
    exists (Node f0 l1 l2 (Some head2')). split. simpl. rewrite H5.
    apply list_forall2_length in H4 as H7. rewrite H7. auto.
    constructor. auto. auto.
  + exists (Node f0 l1 (l2++[head2]) None). split.
    simpl. destruct head1. inv Heqo. repeat destr_in H1.
    inv H11. simpl. apply list_forall2_length in H4 as H7. rewrite H7. auto.
    simpl. apply list_forall2_length in H4 as H7. rewrite H7. auto.
    constructor. apply list_forall2_app. auto.
    constructor. auto. constructor.
Qed.

Lemma struct_eq_next_block_stree : forall s1 s2 fid1 fid2 p1 p2 pos1 pos2 s1' s2',
    struct_eq s1 s2 ->
    next_block_stree s1 = (fid1,pos1,p1,s1') ->
    next_block_stree s2 = (fid2,pos2,p2,s2') ->
    fid1=fid2 /\ p1 = p2.
Proof.
  induction s1. intros.
  destruct s1. destruct s2. inv H0.
  - inv H1. inv H2. auto.
  - inv H1. inv H2. auto.
  - inv H1. inv H2.  repeat destr_in H3.  repeat destr_in H1.
    exploit H; eauto. simpl. auto. intros [X Y].
    split. auto. subst. erewrite list_forall2_length; eauto.
Qed.

End STREE.

Module StrucMem.

Module Mem := Mem(Struc_Block).
Include Mem.
Export Struc_Block.

Record struc' : Type := mkstruc {
  stack : stree;
  global : list ident;
}.

Definition struc := struc'.

Definition struc_empty : struc := mkstruc empty_stree nil.

Definition struc_cpath (s:struc) := cpath (stack s).

Definition struc_npath (s:struc) := npath (stack s).

Definition struc_depth (s:struc) := depth (stack s).

Definition struc_In(b:block)(s:struc) : Prop :=
  match b with
  | Stack fid path pos => stree_In fid path pos (stack s)
  | Global id => In id (global s)
  end.

Definition empty_in: forall b, ~ struc_In b struc_empty.
Proof.
  intros. destruct b; simpl in *; try congruence.
  destruct p; unfold stree_In; simpl; auto. intro. inv H. auto.
  destruct n; auto.
Qed.

Definition struc_dec : forall b s, {struc_In b s}+{~struc_In b s}.
Proof.
  intros. destruct b.
  apply stree_Indec.
  apply In_dec. apply peq.
Qed.

Definition fresh_block (s:struc): block :=
  match next_block_stree (stack s) with
    |(f,pos,path,_) =>  Stack f path pos
  end.

Theorem freshness : forall s, ~struc_In (fresh_block s) s.
Proof.
  intros. unfold fresh_block.
  destruct (next_block_stree (stack s)) eqn:?.
  destruct p. destruct p.
  eapply stree_freshness; eauto.
Qed.

Definition struc_incr (s:struc):struc :=
  let (pp,t') := next_block_stree (stack s) in
  mkstruc t' (global s).

Definition struc_include(s1 s2:struc) := forall b, struc_In b s1 -> struc_In b s2.

Theorem struc_incr_in : forall b s,
    struc_In b (struc_incr s) <-> b = (fresh_block s) \/ struc_In b s.
Proof.
  intros. unfold struc_In. destruct b.
  - unfold struc_incr. unfold fresh_block.
    destruct (next_block_stree) eqn:?. simpl.
    destruct p1. destruct p1.
    eapply next_block_stree_in in Heqp1.
    split. intro. apply Heqp1 in H. destruct H.
    inv H. auto. auto.
    intro. apply Heqp1. destruct H.
    inv H. auto. auto.
  - unfold struc_incr. unfold fresh_block.
    destruct (next_block_stree) eqn:?. simpl.
    destruct p. destruct p. split.
    auto. intros [H|H]. inv H. auto.
Qed.

Theorem struc_incr_in1 : forall s, struc_In (fresh_block s) (struc_incr s).
Proof. intros. apply struc_incr_in. left. auto. Qed.
Theorem struc_incr_in2 : forall s, struc_include s (struc_incr s).
Proof. intros. intro. intro. apply struc_incr_in. right. auto. Qed.

Lemma struc_include_refl : forall s:struc, struc_include s s.
Proof. intro. intro. auto. Qed.

Lemma struc_include_trans:
  forall p q r:struc,struc_include p q-> struc_include q r -> struc_include p r.
Proof.
  intros. intro. intro.  auto.
Qed.

Lemma struc_include_incr:
  forall s, struc_include s (struc_incr s).
Proof.
  intros. apply struc_incr_in2.
Qed.

(* struc_incr_frame *)
Definition struc_incr_frame (s:struc)(id:ident):struc :=
  let (t',p) := next_stree (stack s) id in
  mkstruc t' (global s).

Theorem struc_incr_frame_in : forall s b id,
    struc_In b s <-> struc_In b (struc_incr_frame s id).
Proof.
  intros. unfold struc_In. destruct b.
  - unfold struc_incr_frame.
    destruct (next_stree (stack s)) eqn:?.
    simpl.
    eapply next_stree_in. eauto.
  - unfold struc_incr_frame.
    destruct (next_stree (stack s)).
    reflexivity.
Qed.

(* struc_return_frame *)
Definition struc_return_frame (s:struc) : option struc :=
  match return_stree (stack s) with
    |Some (t',p) => Some (mkstruc t' (global s))
    |None => None
  end.

Definition struc_return_frame' (s:struc) : struc :=
  match struc_return_frame s with
    |Some s' => s'
    |None => struc_empty
  end.

Lemma struc_return_refl : forall s s', is_active (stack s) ->
    struc_return_frame s = Some s' <-> struc_return_frame' s = s'.
Proof.
  intros.
  unfold struc_return_frame'. destruct (struc_return_frame s) eqn:?.
  split;  congruence.
  unfold struc_return_frame in Heqo.
  destruct (return_stree (stack s)) eqn:?. destruct p.
  inv Heqo.
  unfold is_active in H. destruct (stack s).
  destruct o.
  inv Heqo0. destr_in H1. destruct p. inv H1.
  destruct H.
Qed.

Lemma struc_return_refl' : forall s , is_active (stack s) ->
    struc_return_frame s = Some (struc_return_frame' s).
Proof.
  intros. apply struc_return_refl; auto.
Qed.

Theorem struc_return_frame_in : forall s s',
    struc_return_frame s = Some (s') ->
    (forall b, struc_In b s <-> struc_In b s').
Proof.
  intros.
  destruct b; unfold struc_return_frame in H;
  destruct (return_stree (stack s)) eqn:?.
  - destruct p1. inv H.
    simpl.
    eapply return_stree_in; eauto.
  - inv H.
  - destruct p. inv H. reflexivity.
  - inv H.
Qed.

(* struc_incr_glob *)
Definition struc_incr_glob (i:ident) (s:struc) : struc :=
 mkstruc (stack s) (i::(global s)).

Theorem struc_incr_glob_in :  forall i s b,
    struc_In b (struc_incr_glob i s) <-> b = (Global i) \/ struc_In b s.
Proof.
  split.
  - unfold struc_incr_glob.
    destruct b; simpl. auto. intros [H|H]. rewrite H. auto. auto.
  - intros [H|H]; unfold struc_incr_glob.
    rewrite H. simpl. auto.
    destruct b. simpl. auto. simpl. auto.
Qed.

Theorem struc_incr_glob_in1 : forall i s, struc_In (Global i) (struc_incr_glob i s).
Proof. intros. apply struc_incr_glob_in. left. auto. Qed.
Theorem struc_incr_glob_in2 : forall i s, struc_include s (struc_incr_glob i s).
Proof. intros. intro. intro. apply struc_incr_glob_in. right. auto. Qed.

Definition match_struc_sup (s:struc) (m:mem) : Prop :=
  forall b, struc_In b s <-> In b (support m).

(** Things to define: *)
(*
Globalenvs : init of struc
Events: operations of memorys
Cminor:

memory + mem structure =?

*)

Definition is_stack (b:block) : Prop :=
  match b with
    | Stack _ _ _ => True
    |  _ => False
  end.

Definition incr_without_glob (j j' : meminj) : Prop :=
  forall b b' delta, j b = None -> j' b = Some (b',delta) ->
       is_stack b /\ is_stack b'.

Record smem : Type := mksmem{
  structure : struc;
  memory: mem;
  match_struc_mem : match_struc_sup structure memory
}.

Program Definition smem_empty := mksmem struc_empty empty _.
Next Obligation.
intro. simpl. generalize empty_in.
intro. split. intro. apply H in H0. auto. intro. inversion H0.
Qed.

End StrucMem.

 Opaque StrucMem.alloc StrucMem.free StrucMem.store StrucMem.load StrucMem.storebytes StrucMem.loadbytes.

 Hint Resolve
  StrucMem.valid_not_valid_diff
  StrucMem.perm_implies
  StrucMem.perm_cur
  StrucMem.perm_max
  StrucMem.perm_valid_block
  StrucMem.range_perm_implies
  StrucMem.range_perm_cur
  StrucMem.range_perm_max
  StrucMem.valid_access_implies
  StrucMem.valid_access_valid_block
  StrucMem.valid_access_perm
  StrucMem.valid_access_load
  StrucMem.load_valid_access
  StrucMem.loadbytes_range_perm
  StrucMem.valid_access_store
  StrucMem.perm_store_1
  StrucMem.perm_store_2
  StrucMem.store_valid_block_1
  StrucMem.store_valid_block_2
  StrucMem.store_valid_access_1
  StrucMem.store_valid_access_2
  StrucMem.store_valid_access_3
  StrucMem.storebytes_range_perm
  StrucMem.perm_storebytes_1
  StrucMem.perm_storebytes_2
  StrucMem.storebytes_valid_access_1
  StrucMem.storebytes_valid_access_2
  StrucMem.storebytes_valid_block_1
  StrucMem.storebytes_valid_block_2
  StrucMem.valid_block_alloc
  StrucMem.fresh_block_alloc
  StrucMem.valid_new_block
  StrucMem.perm_alloc_1
  StrucMem.perm_alloc_2
  StrucMem.perm_alloc_3
  StrucMem.perm_alloc_4
  StrucMem.perm_alloc_inv
  StrucMem.valid_access_alloc_other
  StrucMem.valid_access_alloc_same
  StrucMem.valid_access_alloc_inv
  StrucMem.range_perm_free
  StrucMem.free_range_perm
  StrucMem.valid_block_free_1
  StrucMem.valid_block_free_2
  StrucMem.perm_free_1
  StrucMem.perm_free_2
  StrucMem.perm_free_3
  StrucMem.valid_access_free_1
  StrucMem.valid_access_free_2
  StrucMem.valid_access_free_inv_1
  StrucMem.valid_access_free_inv_2
  StrucMem.unchanged_on_refl
: mem.












