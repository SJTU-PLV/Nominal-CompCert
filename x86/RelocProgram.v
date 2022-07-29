(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 13, 2019 *)
(* Last updated:  Feb 27, 2022 by Jinhua Wu*)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs Asm RelocProg.
Require Import Errors.
Local Open Scope error_monad_scope.

Definition section := @RelocProg.section instruction.

Definition sectable := @RelocProg.sectable instruction.


Definition sec_size (instr_size: instruction -> Z) (s: section) : Z :=
  match s with
  | sec_text c => code_size instr_size c
  | sec_data d => AST.init_data_list_size d
  (* | sec_rodata d => AST.init_data_list_size d *)
  | sec_bytes bs => Z.of_nat (length bs)
  end.

Definition sections_size instr_size stbl :=
  fold_left (fun sz sec => sz + (sec_size instr_size sec)) stbl 0.

Definition program := @RelocProg.program fundef unit instruction.

(** *Some transformation Lemma *)

Definition acc_PTree_fold {A B: Type} (f: positive -> A -> res B) (acc: res (PTree.t B)) (p: positive) (ele: A) : res (PTree.t B) :=
  do acc' <- acc;
  do ele' <- f p ele;
  OK (PTree.set p ele' acc').


Lemma PTree_fold_elements_aux: forall A B n l t (f: positive -> A -> res B) (UNIQUE: list_norepet (map fst l)),
    Datatypes.length l = n ->
    fold_left
      (fun (a : res (PTree.t B)) (p : positive * A) =>
         acc_PTree_fold f a (fst p) (snd p)) 
      l (OK (PTree.empty B)) =  OK t ->
    (forall i a, In (i,a) l -> exists b, f i a = OK b /\ t ! i = Some b) /\
    (forall i b, t ! i = Some b -> exists a, f i a = OK b /\ In (i,a) l).
Proof.
  induction n;intros.
  - rewrite length_zero_iff_nil in H. subst.
    simpl in *. inv H0. split.
    intros.
    apply False_ind;auto.
    intros. rewrite PTree.gempty in H.
    congruence.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l1 & a1 & A1 & B1). subst. clear H.
    rewrite map_app in UNIQUE.
    rewrite fold_left_app in H0.
    simpl in H0.
    split.
    + intros i a InP.
      apply in_app in InP. destruct InP.
      * apply list_norepet_app in UNIQUE.
        destruct UNIQUE as (U1 & U2 & U3).
        unfold list_disjoint in U3.
        generalize (in_map fst _  _ H). simpl.
        intros Infst. simpl in  U3. 
        apply (U3 _ (fst a1)) in Infst.
        unfold acc_PTree_fold in H0 at 1.
        monadInv H0.
        rewrite PTree.gsspec. destr.
        
        exploit IHn. eapply U1. auto. apply EQ.
        intros D. destruct D as (D1 & D2). apply D1 in H. eauto.
        left. auto.
      * simpl in H. destruct H;try congruence. subst.
        simpl in H0.
        unfold acc_PTree_fold in H0 at 1.
        monadInv H0.
        rewrite PTree.gsspec. rewrite peq_true.
        exists x0. auto.
        apply False_ind;auto.
    + intros i a P.
      apply list_norepet_app in UNIQUE.
      destruct UNIQUE as (U1 & U2 & U3).
      unfold list_disjoint in U3.
      unfold acc_PTree_fold in H0 at 1.
      monadInv H0.
      rewrite PTree.gsspec in P.
      destr_in P;subst.
      * inv P. exists (snd a1).
        split;auto.
        apply in_app.
        right. simpl. left. destruct a1;simpl;auto.
      * exploit IHn. eapply U1. auto. apply EQ.
        intros D. destruct D as (D1 & D2). apply D2 in P.
        destruct P as (a0 & ? & ?).
        exists a0. split;auto.
        apply in_app. left;auto.
Qed.

Lemma PTree_fold_equiv: forall A B m n (f: positive -> A -> res B),
    PTree.fold (acc_PTree_fold f) m (OK (PTree.empty B)) = OK n ->
    (forall i a, m ! i = Some a -> exists b, f i a = OK b /\ n ! i = Some b) /\
    (forall i b, n ! i = Some b -> exists a, f i a = OK b /\ m ! i = Some a).  
Proof.
  intros.
  rewrite PTree.fold_spec in H.
  exploit  PTree_fold_elements_aux.
  eapply PTree.elements_keys_norepet.
  eapply eq_refl.
  eauto. intros (P & Q).
  split.
  - intros. apply PTree.elements_correct in H0.
    apply P in H0. auto.
  - intros. apply Q in H0.
    destruct H0 as (a & ? & ?).
    exists a. split;auto. apply PTree.elements_complete.
    auto.
Qed.

Lemma PTree_fold_elements: forall A B m n (f: positive -> A -> res B),
    let R := (fun p a b => f p a = OK b) in
    PTree.fold (acc_PTree_fold f) m (OK (PTree.empty B)) = OK n ->
    list_forall2
      (fun (i_x : positive * A) (i_y : positive * B) =>
         fst i_x = fst i_y /\ R (fst i_x) (snd i_x) (snd i_y))
      (PTree.elements m) (PTree.elements n).
Proof.
  intros.
  exploit PTree_fold_equiv;eauto. intros (? & ?).
  apply PTree.elements_canonical_order1.
  unfold R in *. intros. apply H0 in H2. destruct H2 as (? & ? & ?).
  eauto.
  unfold R in *. intros. apply H1 in H2. destruct H2 as (? & ? & ?).
  eauto.
Qed.
