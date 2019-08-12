Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

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

Record callconv {li1 li2} :=
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

Arguments callconv: clear implicits.
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
Solve All Obligations with
  congruence.

(** ** Composition *)

(*
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
Next Obligation.
  intros until w. intros se1 se3 id (se2 & Hse12 & Hse23).
  rewrite @match_senv_kept by eauto.
  rewrite @match_senv_kept by eauto.
  tauto.
Qed.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.
*)

(** * C-like languages *)

(** ** Interface *)

Record c_query :=
  cq {
    cq_vf: val;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Record c_reply :=
  cr {
    cr_retval: val;
    cr_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
  |}.

(** ** Simulation conventions *)

(** *** Memory extensions *)

Inductive cc_ext_query: c_query -> c_query -> Prop :=
  cc_ext_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
    Val.lessdef vf1 vf2 ->
    Val.lessdef_list vargs1 vargs2 ->
    Mem.extends m1 m2 ->
    cc_ext_query (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_ext_reply: c_reply -> c_reply -> Prop :=
  cc_ext_reply_intro vres1 vres2 m1 m2:
    Val.lessdef vres1 vres2 ->
    Mem.extends m1 m2 ->
    cc_ext_reply (cr vres1 m1) (cr vres2 m2).

Program Definition cc_ext :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := cc_ext_query;
    match_reply w := cc_ext_reply;
  |}.
Solve All Obligations with
  congruence.

(** *** Memory injections *)

Inductive cc_inj_query (f: meminj): c_query -> c_query -> Prop :=
  cc_inj_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
    Val.inject f vf1 vf2 ->
    Val.inject_list f vargs1 vargs2 ->
    Mem.inject f m1 m2 ->
    cc_inj_query f (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_inj_reply (f: meminj): c_reply -> c_reply -> Prop :=
  cc_inj_reply_intro vres1 vres2 m1 m2:
    Val.inject f vres1 vres2 ->
    Mem.inject f m1 m2 ->
    cc_inj_reply f (cr vres1 m1) (cr vres2 m2).

Program Definition cc_inj :=
  {|
    match_senv := symbols_inject;
    match_query := cc_inj_query;
    match_reply := cc_inj_reply;
  |}.
Solve All Obligations with
  firstorder.

(** *** Injections with footprint enforcement *)

Record cc_injp_world :=
  injpw { injp_inj :> meminj; injp_m1: mem; injp_m2: mem }.

Inductive cc_injp_query: cc_injp_world -> c_query -> c_query -> Prop :=
  cc_injp_query_intro f vf1 vf2 sg vargs1 vargs2 m1 m2:
    Val.inject f vf1 vf2 ->
    Val.inject_list f vargs1 vargs2 ->
    Mem.inject f m1 m2 ->
    cc_injp_query (injpw f m1 m2) (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_injp_reply: cc_injp_world -> c_reply -> c_reply -> Prop :=
  cc_injp_reply_intro f m1 m2 f' vres1 vres2 m1' m2':
    Val.inject f' vres1 vres2 ->
    Mem.inject f' m1' m2' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m1' ->
    cc_injp_reply (injpw f m1 m2) (cr vres1 m1') (cr vres2 m2').

Program Definition cc_injp :=
  {|
    match_senv w := symbols_inject (injp_inj w);
    match_query := cc_injp_query;
    match_reply := cc_injp_reply;
  |}.
Solve All Obligations with
  firstorder.
