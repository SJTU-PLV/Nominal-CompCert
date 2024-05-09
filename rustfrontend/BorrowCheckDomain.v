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

(* May-live loan set *)
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


(** Auxilary defintions and functions *)

Inductive access_kind : Type :=
| Aread
| Awrite.

Definition conflict_access (a: access_kind) (mut: mutkind) : bool :=
  match a, mut with
  | Awrite, _ => true
  | Aread, Mutable => true
  | Aread, Immutable => false
  end.

(* Access loan [l] with [a] would invalidate [ls] *)
Definition conflict_loan (ls: LoanSet.t) (a: access_kind) (l: loan) : bool :=
  if LoanSet.mem l ls then
    match l with
    | Lintern mut _ =>
        conflict_access a mut
    | Lextern _ =>
        (* It is impossible to access a external loan *)
        false
    end
  else false.

(* Access ls1 with [a] as access kind, if there is any loan in ls2
that is conflict with this access, return true *)
Definition conflict (ls1 ls2 : LoanSet.t) (a: access_kind) : bool :=
  LoanSet.fold (fun elt acc => orb acc (conflict_loan ls2 a elt)) ls1 false.

(* Invalidate an origin *)
Definition invalidate_origin (ls1: LoanSet.t) (a: access_kind) (os: origin_state) : origin_state :=
  match os with
  | Live ls2 =>
      if conflict ls1 ls2 a then Dead
      else os
  | Dead => Dead
  end.

(* Check whether we should invalidate each origin in the origin
environment *)
Definition invalidate_origins (ls: LoanSet.t) (a: access_kind) (oe: LOrgEnv.t) : LOrgEnv.t :=
  match oe with
  | LOrgEnv.Bot => LOrgEnv.Bot
  | LOrgEnv.Top_except t =>
      LOrgEnv.Top_except (PTree.map1 (invalidate_origin ls a) t)
  end.

(* All the origins appear in the type [ty] *)
Fixpoint origins_of_type (ty: type) : list origin :=
  match ty with
  | Tbox ty _ => origins_of_type ty
  | Treference org _ ty _ => org :: origins_of_type ty
  | Tstruct orgs _ _ => orgs
  | Tvariant orgs _ _ => orgs
  | _ => []
  end.       

(* Definition of valid access of a place: check whether there is any
dead origin in the type of the place. Return an error report if
invalid access happens *)
Definition valid_access (oe: LOrgEnv.t) (p: place) : res unit :=
  match oe with
  | LOrgEnv.Bot => Error (msg "It is impossible to pass an invalid origin environment to valid_access")
  | LOrgEnv.Top_except t =>
      let ty := local_type_of_place p in
      let orgs := origins_of_type ty in
      let check acc org :=
        do acc' <- acc;
        match t!org with
        | Some (Live _) => OK tt
        | Some Dead => Error [CTX org; MSG ": access a place with this dead origin (valid_access)"]
        | None => Error [CTX org; MSG ": no such origin in the origin environment (valid_access)"]
        end in
      fold_left check orgs (OK tt)
  end.


(* Relevant loans for a place [p] in the live loan set. The result
depends on the access access_mode *)

Inductive access_mode := Ashallow | Adeep.

(* relevant borrows as shown in NLL *)
Definition relevant_place (p: place) (am: access_mode) (p': place) : bool :=
  match am with
  | Ashallow =>
      is_prefix p' p || is_shallow_prefix p p'
  | Adeep =>
      is_prefix p' p || is_support_prefix p p'
  end.
  
Definition relevant_loan (p: place) (am: access_mode) (l: loan) : bool :=
  match l with
  | Lintern mut p' =>
      relevant_place p am p'
  | Lextern _ =>
      false
  end.

Definition relevant_loans (live_loans: LoanSet.t) (p: place) (am: access_mode) : LoanSet.t :=
  LoanSet.fold (fun elt acc => if relevant_loan p am elt then LoanSet.add elt acc else acc) LoanSet.empty live_loans.


(* Update Alias graph *)

Definition set_alias (org1 org2: origin) (g: LAliasGraph.t) : LAliasGraph.t :=
  match g!org1, g!org2 with
  | Some ls1, Some ls2 =>
      (* merge two cliques *)
      let ls := OriginSet.add org2 (OriginSet.add org1 (OriginSet.union ls1 ls2)) in
      PTree.map (fun id ls' => if OriginSet.mem id ls then
                              OriginSet.union ls' (OriginSet.remove id ls)
                            else ls') g
  | Some ls1, None =>
      let ls := OriginSet.add org2 (OriginSet.add org1 ls1) in
      let g0 := PTree.set org2 OriginSet.empty g in
      PTree.map (fun id ls' => if OriginSet.mem id ls then
                              OriginSet.union ls' (OriginSet.remove id ls)
                            else ls') g0                          
  | None, Some ls2 =>
      let ls := OriginSet.add org2 (OriginSet.add org1 ls2) in
      let g0 := PTree.set org1 OriginSet.empty g in
      PTree.map (fun id ls' => if OriginSet.mem id ls then
                              OriginSet.union ls' (OriginSet.remove id ls)
                            else ls') g0
  | None, None =>
      let g0 := PTree.set org1 (OriginSet.singleton org2) g in
      PTree.set org2 (OriginSet.singleton org1) g0
  end.

(* Set loans to an origin and then update all the alias origin *)

Definition set_loans_with_alias (org: origin) (ls: LoanSet.t) (oe: LOrgEnv.t) (a: LAliasGraph.t) : LOrgEnv.t :=
  let os := Live ls in
  let oe1 := LOrgEnv.set org os oe in
  match a!org with
  | Some orgs =>
      OriginSet.fold (fun elt oe' => LOrgEnv.set elt os oe') orgs oe1
  | None =>
      oe1
  end.
  
(* Remove alias of org in the alias graph, i.e., remove a node in a clique *)
Definition remove_alias (org: origin) (g: LAliasGraph.t) : LAliasGraph.t :=
  match g!org with
  | Some orgs =>
      let g' := PTree.map (fun id s => if OriginSet.mem id orgs then
                                      OriginSet.remove org s
                                    else s) g in
      PTree.remove org g'
  | _ => g
  end.
