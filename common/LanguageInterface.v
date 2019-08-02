Require Import AST.
Require Import Globalenvs.

(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
  }.

(** ** Null interface *)

(** The null language interface defined below is used as the outgoing
  interface for closed semantics. *)

Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
  |}.

(** * Calling conventions *)

(** ** Definition *)

Record callconv li1 li2 :=
  mk_callconv {
    ccworld : Type;
    match_senv: ccworld -> Senv.t -> Senv.t -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;
    match_senv_public_preserved:
      forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Senv.public_symbol se2 id = Senv.public_symbol se1 id;
  }.

Arguments ccworld {_ _}.
Arguments match_senv {_ _} _ _ _.
Arguments match_query {_ _} _ _ _.
Arguments match_reply {_ _} _ _ _.

Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.
Next Obligation.
  congruence.
Qed.

(** ** Composition *)

Program Definition cc_compose {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld := ccworld cc12 * ccworld cc23;
    match_senv w se1 se3 :=
      exists se2,
        match_senv cc12 (fst w) se1 se2 /\
        match_senv cc23 (snd w) se2 se3;
    match_query w q1 q3 :=
      exists q2,
        match_query cc12 (fst w) q1 q2 /\
        match_query cc23 (snd w) q2 q3;
    match_reply w r1 r3 :=
      exists r2,
        match_reply cc12 (fst w) r1 r2 /\
        match_reply cc23 (snd w) r2 r3;
  |}.
Next Obligation.
  intros li1 li2 li3 cc12 cc23 w se1 se3 (se2 & H12 & H23) id.
  etransitivity; eauto using match_senv_public_preserved.
Qed.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.
