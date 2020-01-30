Require Import Values.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import LanguageInterface.
Require Import Smallstep.

(** Simulation proofs sometimes rely on invariants of the source
  and/or target languages, such as type preservation. The
  constructions defined below can be used to decouple these
  preservation and simulation proofs, and to introduce calling
  conventions characterizing the invariant at module boundaries. *)


(** * Invariants *)

(** ** Interface *)

(** First, we need to define a sort of "invariant interface", which
  will describe how a given invariant impacts the queries and replies
  of the language under consideration. *)

Record lts_invariant {li: language_interface} :=
  {
    query_inv : query li -> Prop;
    reply_inv : reply li -> Prop;
  }.

Arguments lts_invariant : clear implicits.

Definition invariant li :=
  Genv.symtbl -> lts_invariant li.

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [IS]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record lts_preserves {liA liB S} (L: lts liA liB S) IA IB (IS: S -> Prop) :=
  {
    preserves_step s t s':
      IS s ->
      Step L s t s' ->
      IS s';
    preserves_initial_state q s:
      query_inv IB q ->
      initial_state L q s ->
      IS s;
    preserves_external s q:
      IS s ->
      at_external L s q ->
      query_inv IA q /\
      forall r s',
        reply_inv IA r ->
        after_external L s r s' ->
        IS s';
    preserves_final_state s r:
      IS s ->
      final_state L s r ->
      reply_inv IB r;
  }.

Definition preserves {liA liB} (L: semantics liA liB) (IA IB: invariant _) IS :=
  forall se,
    Genv.valid_for (skel L) se ->
    lts_preserves (L se) (IA se) (IB se) (IS se).

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Inductive rel_inv {A} (I: A -> Prop) (x: A): A -> Prop :=
  rel_inv_intro: I x -> rel_inv I x x.

Program Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    ccworld := Genv.symtbl;
    match_senv se := rel_inv (eq se);
    match_query se := rel_inv (query_inv (I se));
    match_reply se := rel_inv (reply_inv (I se));
  |}.
Solve All Obligations with
  cbn; intros; destruct H; auto.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li res} (L: semantics li res) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) L L.
Proof.
  fsim eapply forward_simulation_step with (match_states := rel_inv (IS se1));
  destruct Hse; subst.
  - reflexivity.
  - destruct 1. auto.
  - intros q _ s [Hq] Hs.
    exists s. split; eauto.
    constructor.
    eapply preserves_initial_state; eauto.
  - intros s _ r [Hs] Hr.
    exists r. split; eauto.
    constructor.
    eapply preserves_final_state; eauto.
  - intros s _ q [Hs] Hq.
    edestruct @preserves_external as (HqA & Hr); eauto.
    exists se1, q. repeat apply conj; cbn; eauto.
    + constructor. auto.
    + constructor. auto.
    + intros r' _ s' [Hr'] Hs'.
      exists s'. split; eauto.
      constructor.
      eapply Hr; eauto.
  - intros s t s' Hstep _ [Hs].
    exists s'. split; eauto.
    constructor.
    eapply preserves_step; eauto.
Qed.


(** * Invariant-based simulation proof methods *)

(** Once we have established that the source or target language
  preserves an invariant of interest, we wish to use that fact to
  help prove the forward simulation for the pass being considered.

  The most basic way to do that is to add an assertion to the
  simulation relation that the states satisfy the invariant. Then,
  we rely on these assertions to prove a simulation step, and use the
  relevant preservation lemmas to establish them again for the
  successor states. This approach is workable and has been used in
  CompCert for typing invariants, but it is somewhat ad-hoc and
  becomes more involved when the interaction with the environment is
  involved in the invariant's preservation.

  Instead, we would like to formulate a weaker simulation diagram,
  where the invariant can be assumed on the current states but does
  not need to be established for the successor states, then show that
  if the language involved [preserves] the invariant (in the sense
  defined above), then this weakened diagram is sufficient to
  establish a forward simulation for the pass.

  The most straightforward way to do this would be to define a
  weakened version of [forward_simulation] along these lines, however
  this comes with its own pitfall: there already exists many lemmas
  one can use to establish a [forward_simulation] using simplified
  diagrams rather than the more complex, general form, and we would
  like to be able to use simplified diagrams for our weakened version
  as well. Under this approach, we would have to duplicate such lemmas
  for the weakened diagram. Instead, the method implemented below
  reuses [forward_simulation] and expresses the weakened diagram as a
  special case, making it possible to reuse all existing techniques to
  prove it.

  Since by definition, [forward_simulation] uses the same simulation
  relation for the current and successor states, we accomplish this by
  acting on the transition systems themselves:

    - for the source language, we can build a strengthened version of
      the transition system which restricts the transitions to states
      which statisfy the invariant;
    - for the target language, we can build a relaxed version of the
      transition system which adds arbitrary transitions from states
      which do not satisfy the invariant.

  Proving a simulation from the strengthened source semantics, and/or
  to the weakened target semantics, is easier because we have
  hypotheses that the states involved satify the invariant. At the
  same time, for an invariant-preserving language, we can easily show
  a simulation from the original to the strengthened version, and from
  the weakened to the original version, and these simulations can be
  composed with that proved by the used to obtain the desired one. *)

(** ** Strengthening the source semantics *)

Definition restrict_lts {liA liB S} (L: lts liA liB S) IA IB IS :=
  {|
    step ge s t s' :=
      step L ge s t s' /\ IS s /\ IS s';
    valid_query q :=
      valid_query L q;
    initial_state q s :=
      initial_state L q s /\ query_inv IB q /\ IS s;
    final_state s r :=
      final_state L s r /\ IS s /\ reply_inv IB r;
    at_external s q :=
      at_external L s q /\ IS s /\ query_inv IA q;
    after_external s r s' :=
      after_external L s r s' /\ IS s /\ IS s' /\ reply_inv IA r;
    globalenv :=
      globalenv L;
  |}.

Definition restrict {liA liB} (L: semantics liA liB) IA IB IS :=
  {|
    skel := skel L;
    state := state L;
    activate se := restrict_lts (L se) (IA se) (IB se) (IS se);
  |}.

Lemma restrict_fsim {li res} (L: semantics li res) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) L (restrict L IA IB IS).
Proof.
  set (ms x := rel_inv (IS x) : state L -> state (restrict L IA IB IS) -> Prop).
  (fsim apply forward_simulation_step with (match_states := ms se1); destruct Hse; subst);
  cbn; subst ms; auto.
  - destruct 1. reflexivity.
  - intros q _ s [Hq] Hs. exists s.
    assert (IS se1 s) by (eapply preserves_initial_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ r [Hs] Hr. exists r.
    assert (reply_inv (IB se1) r) by (eapply preserves_final_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ q [Hs] H. exists se1, q.
    edestruct @preserves_external as [Hq Hs']; eauto.
    intuition auto using rel_inv_intro.
    destruct H0. exists s1'. intuition eauto using rel_inv_intro.
  - intros s t s' STEP _ [Hs].
    assert (IS se1 s') by (eapply preserves_step; eauto).
    exists s'. eauto using rel_inv_intro.
Qed.

(** ** Weakening the target semantics *)

Definition expand_lts {liA liB S} (L: lts liA liB S) IA IB (IS: _ -> Prop) :=
  {|
    valid_query q :=
      valid_query L q;
    step ge s t s' :=
      IS s -> step L ge s t s';
    initial_state q s :=
      query_inv IB q -> initial_state L q s;
    final_state s r :=
      IS s -> final_state L s r;
    at_external s q :=
      IS s -> at_external L s q;
    after_external s r s' :=
      IS s -> reply_inv IA r -> after_external L s r s';
    globalenv :=
      globalenv L;
  |}.

Definition expand {liA liB} (L: semantics liA liB) IA IB IS :=
  {|
    skel := skel L;
    state := state L;
    activate se := expand_lts (L se) (IA se) (IB se) (IS se);
  |}.

Lemma expand_fsim {liA liB} (L: semantics liA liB) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) (expand L IA IB IS) L.
Proof.
  set (ms x := rel_inv (IS x) : state (expand L IA IB IS) -> state L -> Prop).
  (fsim apply forward_simulation_step with (match_states := ms se1); destruct Hse; subst);
  cbn; subst ms; auto.
  - destruct 1; reflexivity.
  - intros q _ s [Hq] Hs. exists s.
    assert (IS se1 s) by (eapply preserves_initial_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ r [Hs] Hr.
    assert (reply_inv (IB se1) r) by (eapply preserves_final_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ q [Hs] H. exists se1, q.
    edestruct @preserves_external as [Hq Hs']; eauto. intuition auto using rel_inv_intro.
    destruct H. exists s1'. intuition eauto using rel_inv_intro.
  - intros s t s' STEP _ [Hs].
    assert (IS se1 s') by (eapply preserves_step; eauto).
    exists s'. eauto using rel_inv_intro.
Qed.
