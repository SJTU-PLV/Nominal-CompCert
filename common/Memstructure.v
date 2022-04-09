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

(* Module Type SUP(Block:BLOCK).
Include Block.
Parameter sup: Type.

Parameter sup_empty : sup.

Parameter sup_In : block -> sup -> Prop.
Parameter empty_in: forall b, ~ sup_In b sup_empty.
Parameter sup_dec : forall b s, {sup_In b s}+{~sup_In b s}.

Parameter fresh_block : sup -> block.
Parameter freshness : forall s, ~sup_In (fresh_block s) s.

Parameter sup_add : block -> sup -> sup.

Definition sup_incr(s:sup) := sup_add (fresh_block s) s.

Definition sup_include(s1 s2:sup) := forall b, sup_In b s1 -> sup_In b s2.

Parameter sup_add_in : forall b s b', sup_In b' (sup_add b s) <-> b' = b \/ sup_In b' s.

Theorem sup_add_in1 : forall b s, sup_In b (sup_add b s).
Proof. intros. apply sup_add_in. left. auto. Qed.
Theorem sup_add_in2 : forall b s, sup_include s (sup_add b s).
Proof. intros. intro. intro. apply sup_add_in. right. auto. Qed.

Lemma sup_include_refl : forall s:sup, sup_include s s.
Proof. intro. intro. auto. Qed.

Lemma sup_include_trans:
  forall p q r:sup,sup_include p q-> sup_include q r -> sup_include p r.
Proof.
  intros. intro. intro.  auto.
Qed.

Lemma sup_include_incr:
  forall s b, sup_include s (sup_add b s).
Proof.
  intros. apply sup_add_in2.
Qed.

End SUP.*)

Module Memstructure1.

Module Block <: BLOCK.
Inductive block' :=
|Global : ident -> block'
|Heap : ident -> block'
|Stack : ident -> block'.

Definition block := block'.
Theorem eq_block : forall (x y:block),{x=y}+{x<>y}.
Proof.
  intros. destruct x; destruct y.
  destruct (peq i i0). left; congruence. right; congruence.
  right. congruence. right. congruence.
  right. congruence.
  destruct (peq i i0). left; congruence. right; congruence.
  right. congruence.
  right. congruence. right. congruence.
  destruct (peq i i0). left; congruence. right; congruence.
Qed.
End Block.

Module Mem := Mem(Block).
Include Block.

Record structure := mk_struc{
 global_sup: list ident;
 heap_sup: list ident;
 stack_sup: list ident;
}.

Definition structure_In (b:block)(s:structure) :=
  match b with
    |Global id => In id (global_sup s)
    |Heap id => In id (heap_sup s)
    |Stack id => In id (stack_sup s)
  end.


Definition match_mem_structure (m:Mem.mem) (s:structure) :=
   forall b, Mem.valid_block m b <-> structure_In b s.

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

Definition fresh_ident (l: list ident ) := Pos.succ (find_max_pos l).

Theorem freshness : forall s, ~In (fresh_ident s) s.
Proof.
  intros. unfold fresh_ident.
  intro.
  apply Lessthan in H.
  assert (Plt (find_max_pos s) (Pos.succ (find_max_pos s))). apply Plt_succ.
  assert (Plt (find_max_pos s) (find_max_pos s)). eapply Plt_Ple_trans. eauto. auto.
  apply Plt_strict in H1.
  auto.
Qed.

End Memstructure1.


