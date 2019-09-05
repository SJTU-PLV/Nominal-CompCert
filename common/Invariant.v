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

Record invariant {li: language_interface} :=
  {
    query_inv : query li -> Prop;
    reply_inv : query li -> reply li -> Prop;
  }.

Arguments invariant : clear implicits.

(** As a core example, here is an invariant for the C language
  interface asserting that the queries and replies are well-typed. *)

Definition wt_c : invariant li_c :=
  {|
    query_inv q := Val.has_type_list (cq_args q) (sig_args (cq_sg q));
    reply_inv q r := Val.has_type (cr_retval r) (proj_sig_res (cq_sg q));
  |}.

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [IS]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record preserves {li res} (L: semantics li res) IA (IR IS: _ -> Prop) :=
  {
    preserves_step s t s':
      IS s ->
      Step L s t s' ->
      IS s';
    preserves_initial_state s:
      initial_state L s ->
      IS s;
    preserves_external s q:
      IS s ->
      at_external L s q ->
      query_inv IA q /\
      forall r s',
        reply_inv IA q r ->
        after_external L s r s' ->
        IS s';
    preserves_final_state s r:
      IS s ->
      final_state L s r ->
      IR r;
  }.

Definition open_preserves {liA liB} (L: open_sem liA liB) IA IB IS :=
  forall se q,
    query_inv IB q ->
    preserves (L se q) IA (reply_inv IB q) (IS se q).

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Inductive rel_inv {A} (I: A -> Prop) (x: A): A -> Prop :=
  rel_inv_intro: I x -> rel_inv I x x.

Program Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    ccworld := query li;
    match_senv q := eq;
    match_query q q1 q2 := query_inv I q /\ q1 = q /\ q2 = q;
    match_reply q := rel_inv (reply_inv I q);
  |}.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li res} (L: semantics li res) IA IR IS:
  preserves L IA IR IS ->
  forward_simulation (cc_inv IA) (rel_inv IR) L L.
Proof.
  intros HL.
  apply forward_simulation_step with (match_states := rel_inv IS).
  - intros s Hs. subst.
    exists s. split; eauto.
    constructor.
    eapply preserves_initial_state; eauto.
  - intros s _ r [Hs] Hr.
    exists r. split; eauto.
    constructor.
    eapply preserves_final_state; eauto.
  - intros s _ qA [Hs] HAE.
    edestruct @preserves_external as (HqA & Hr); eauto.
    exists qA, qA. repeat apply conj; eauto.
    + intros r' _ s' [Hr'] Hs'.
      exists s'. split; eauto.
      constructor.
      eapply Hr; eauto.
  - intros s t s' Hstep _ [Hs].
    exists s'. split; eauto.
    constructor.
    eapply preserves_step; eauto.
Qed.

Lemma open_preserves_fsim {li} (L: open_sem li li) IA IB IS:
  open_preserves L IA IB IS ->
  open_fsim (cc_inv IA) (cc_inv IB) L L.
Proof.
  intros HL. split; auto. cbn.
  intros q ? se ? ? Hse _ ? (Hq & ? & ?). subst.
  eapply preserves_fsim; eauto.
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

Definition restrict {li res} (L: semantics li res) IA P IR IS :=
  {|
    step ge s t s' :=
      step L ge s t s' /\ IS s /\ IS s';
    initial_state s :=
      initial_state L s /\ P /\ IS s;
    final_state s r :=
      final_state L s r /\ IS s /\ IR r;
    at_external s q :=
      at_external L s q /\ IS s /\ query_inv IA q;
    after_external s r s' :=
      after_external L s r s' /\ IS s /\ IS s' /\
      exists q, at_external L s q /\ query_inv IA q /\ reply_inv IA q r;
    globalenv :=
      globalenv L;
  |}.

Lemma restrict_fsim {li res} (L: semantics li res) IA (P: Prop) IR IS:
  preserves L IA IR IS -> P ->
  forward_simulation (cc_inv IA) (rel_inv IR) L (restrict L IA P IR IS).
Proof.
  intros HL HP.
  set (ms := rel_inv IS : state L -> state (restrict L IA P IR IS) -> Prop).
  apply forward_simulation_step with (match_states := ms); cbn; subst ms.
  - intros s Hs. exists s.
    assert (IS s) by (eapply preserves_initial_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ r [Hs] Hr. exists r.
    assert (IR r) by (eapply preserves_final_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ q [Hs] H. exists q, q.
    edestruct @preserves_external as [Hq Hs']; eauto. intuition auto.
    destruct H0. exists s1'. intuition eauto using rel_inv_intro.
  - intros s t s' STEP _ [Hs].
    assert (IS s') by (eapply preserves_step; eauto).
    exists s'. eauto using rel_inv_intro.
Qed.

Definition open_restrict {liA liB} (L: open_sem liA liB) IA IB IS :=
  {|
    activate se q :=
      restrict (L se q) IA (query_inv IB q) (reply_inv IB q) (IS se q);
    skel :=
      skel L;
  |}.

Lemma open_restrict_fsim {liA liB} (L: open_sem liA liB) IA IB IS:
  open_preserves L IA IB IS ->
  open_fsim (cc_inv IA) (cc_inv IB) L (open_restrict L IA IB IS).
Proof.
  intros HL. split; cbn; auto.
  intros q se _ q1 q2 Hse _ [ ] (Hq & Hq1 & Hq2). subst.
  eapply restrict_fsim; eauto.
Qed.

(** ** Weakening the target semantics *)

Definition expand {li res} (L: semantics li res) IA (P: Prop) IS :=
  {|
    step ge s t s' :=
      IS s -> step L ge s t s';
    initial_state s :=
      P -> initial_state L s;
    final_state s r :=
      IS s -> final_state L s r;
    at_external s q :=
      IS s -> at_external L s q;
    after_external s r s' :=
      forall q,
        IS s -> at_external L s q -> query_inv IA q -> reply_inv IA q r ->
        after_external L s r s';
    globalenv :=
      globalenv L;
  |}.

Lemma expand_fsim {li res} (L: semantics li res) IA (P: Prop) IR IS:
  preserves L IA IR IS -> P ->
  forward_simulation (cc_inv IA) (rel_inv IR) (expand L IA P IS) L.
Proof.
  intros HL HP.
  set (ms := rel_inv IS : state (expand L IA P IS) -> state L -> Prop).
  apply forward_simulation_step with (match_states := ms); cbn; subst ms.
  - intros s Hs. exists s.
    assert (IS s) by (eapply preserves_initial_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ r [Hs] Hr.
    assert (IR r) by (eapply preserves_final_state; eauto).
    eauto using rel_inv_intro.
  - intros s _ q [Hs] H. exists q, q.
    edestruct @preserves_external as [Hq Hs']; eauto. intuition auto.
    destruct H. exists s1'. intuition eauto using rel_inv_intro.
  - intros s t s' STEP _ [Hs].
    assert (IS s') by (eapply preserves_step; eauto).
    exists s'. eauto using rel_inv_intro.
Qed.

Definition open_expand {liA liB} (L: open_sem liA liB) IA IB IS :=
  {|
    activate se q := expand (L se q) IA (query_inv IB q) (IS se q);
    skel := skel L;
  |}.

Lemma open_expand_fsim {liA liB} (L: open_sem liA liB) IA IB IS:
  open_preserves L IA IB IS ->
  open_fsim (cc_inv IA) (cc_inv IB) (open_expand L IA IB IS) L.
Proof.
  intros HL. split; cbn; auto.
  intros q se _ q1 q2 Hse _ [ ] (Hq & Hq1 & Hq2). subst.
  eapply expand_fsim; eauto.
Qed.
