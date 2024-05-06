Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice.
Require Import Rusttypes RustlightBase RustIR.
Require Import Ordered.
Require FSetAVL.
Require Import Errors.

Import ListNotations.
Scheme Equality for list.
Open Scope error_monad_scope.

(** ** The abstract domain for borrow checking based on Polonius *)

(** Loans  *)

Inductive loan : Type :=
| Lintern (mut: mutkind) (p: place)
| Lextern (org: origin).

Lemma loan_eq_dec: forall (l1 l2: loan), {l1 = l2} + {l1 <> l2}.
Proof.
  generalize Pos.eq_dec place_eq. intros.
  decide equality.
  decide equality.
Qed.                                                         

Module Loan <: DecidableType.DecidableType.
  Definition t := loan.
  Definition eq := @eq t.
  Definition eq_dec := loan_eq_dec.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Loan.

Module LoanSet := FSetWeakList.Make(Loan).

Module LoanSetL := LFSet(LoanSet).


(** Origin state *)

Inductive origin_state : Type :=
| Live (ls: LoanSetL.t)
| Dead.

(* Origin state is a lattice *)

Module LOrgSt <: SEMILATTICE_WITH_TOP.
  
Definition t := origin_state.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@eq_refl t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

Definition beq (s1 s2 : t) : bool :=
  match s1, s2 with
  | Live ls1, Live ls2 => LoanSetL.beq ls1 ls2
  | Dead, Dead => true
  | _, _ => false
  end.

Axiom beq_correct: forall x y, beq x y = true -> eq x y.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Dead, _ => True
  | _, Dead => False
  | Live ls1, Live ls2 => LoanSetL.ge ls1 ls2
  end.

Axiom ge_refl: forall x y, eq x y -> ge x y.

Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

Definition bot := Live(LoanSetL.bot).

Axiom ge_bot: forall x, ge x bot.

Definition top := Dead.

Axiom ge_top: forall x, ge top x.

Definition lub (x y: t) :=
  match x, y with
  | Dead, _ => Dead
  | _, Dead => Dead
  | Live ls1, Live ls2 => Live(LoanSetL.lub ls1 ls2)
  end.

Axiom ge_lub_left: forall x y, ge (lub x y) x.

Axiom ge_lub_right: forall x y, ge (lub x y) y.

End LOrgSt.
  
(** Origin environment *)

Module LOrgEnv := LPMap(LOrgSt).

(** Alias graph *)

Module OriginSet := FSetAVL.Make(OrderedPositive).

Module LOriginSet := LFSet(OriginSet).

Module LAliasGraph := LPMap1(LOriginSet).


(** Top level environment for dataflow analysis *)

(* Define equality for errcode *)

Lemma errcode_eq : forall (c1 c2: errcode), {c1 = c2} + {c1 <> c2}.
  generalize string_dec Pos.eq_dec.
  decide equality.
Qed.

Module AE <: SEMILATTICE.
  
  Inductive t' := | Bot | Err (loc: node) (msg: errmsg) | State (live_loans: LoanSetL.t) (org_env: LOrgEnv.t) (alias: LAliasGraph.t).
  
  Definition t := t'.
 
  Definition eq (x y: t) : Prop :=
    match x, y with
    | Bot, Bot => True
    | State ls1 oe1 a1, State ls2 oe2 a2 =>
        LoanSetL.eq ls1 ls2 /\
        LOrgEnv.eq oe1 oe2 /\
        LAliasGraph.eq a1 a2          
    | Err pc1 msg1, Err pc2 msg2 =>
        Pos.eq pc1 pc2 /\ list_forall2 eq msg1 msg2
    | _, _ => False
    end.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => false
    | State ls1 oe1 a1, State ls2 oe2 a2 =>
        LoanSetL.beq ls1 ls2 &&
        LOrgEnv.beq oe1 oe2 &&
        LAliasGraph.beq a1 a2          
    | Err pc1 msg1, Err pc2 msg2 =>
        Pos.eqb pc1 pc2 && List.list_eq_dec errcode_eq msg1 msg2
    | _, _ => false
    end.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    (* Err is the top *)
    | Err pc1 _, Err pc2 _ => Pos.ge pc1 pc2
    | Err _ _, _ => True
    | _, Err _ _ => False
    | State ls1 oe1 a1, State ls2 oe2 a2 =>
        LoanSetL.ge ls1 ls2 /\
        LOrgEnv.ge oe1 oe2 /\
        LAliasGraph.ge a1 a2          
    end.

  Definition bot := Bot.

  Definition lub (x y: t) :=
    match x,y with
    | _, Bot => x
    | Bot, _ => y
    | Err pc1 msg1, Err pc2 msg2 =>
        if Pos.ltb pc1 pc2 then Err pc2 msg2 else Err pc1 msg1
    | Err _ _, State _ _ _ => x
    | State _ _ _, Err _ _ => y
    | State ls1 oe1 a1, State ls2 oe2 a2 =>
        State (LoanSetL.lub ls1 ls2) (LOrgEnv.lub oe1 oe2) (LAliasGraph.lub a1 a2)
    end.

  (** TODO  *)
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End AE.
