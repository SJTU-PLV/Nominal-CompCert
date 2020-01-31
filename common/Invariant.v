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
    inv_world : Type;
    symtbl_inv : inv_world -> Genv.symtbl -> Prop;
    query_inv : inv_world -> query li -> Prop;
    reply_inv : inv_world -> reply li -> Prop;
  }.

Arguments invariant : clear implicits.

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [IS]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record lts_preserves {liA liB S} se (L: lts liA liB S) IA IB (IS: _ -> S -> Prop) w :=
  {
    preserves_step s t s':
      IS w s ->
      Step L s t s' ->
      IS w s';
    preserves_initial_state q s:
      query_inv IB w q ->
      initial_state L q s ->
      IS w s;
    preserves_external s q:
      IS w s -> at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
      forall r s', reply_inv IA wA r -> after_external L s r s' -> IS w s';
    preserves_final_state s r:
      IS w s ->
      final_state L s r ->
      reply_inv IB w r;
  }.

Definition preserves {liA liB} (L: semantics liA liB) (IA IB: invariant _) IS :=
  forall w se,
    Genv.valid_for (skel L) se ->
    symtbl_inv IB w se ->
    lts_preserves se (L se) IA IB IS w.

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Inductive rel_inv {A} (I: A -> Prop) (x: A): A -> Prop :=
  rel_inv_intro: I x -> rel_inv I x x.

Program Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    ccworld := inv_world I;
    match_senv w := rel_inv (symtbl_inv I w);
    match_query w := rel_inv (query_inv I w);
    match_reply w := rel_inv (reply_inv I w);
  |}.
Solve All Obligations with
  cbn; intros; destruct H; auto.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li res} (L: semantics li res) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) L L.
Proof.
  fsim (eapply forward_simulation_step with (match_states := rel_inv (IS w));
        destruct Hse; subst).
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
    edestruct @preserves_external as (wA & Hse & HqA & Hr); eauto.
    exists wA, q. repeat apply conj; cbn; eauto.
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

Section RESTRICT.
  Context {liA liB} (L: semantics liA liB).
  Context (IA: invariant liA) (IB: invariant liB).
  Context (IS: inv_world IB -> state L -> Prop).

  Definition restrict_lts se :=
    {|
      step ge s t s' :=
        exists w,
          symtbl_inv IB w se /\
          step (L se) ge s t s' /\
          IS w s /\
          IS w s';
      valid_query q :=
        valid_query (L se) q;
      initial_state q s :=
        exists w,
          symtbl_inv IB w se /\
          initial_state (L se) q s /\
          query_inv IB w q /\
          IS w s;
      final_state s r :=
        exists w,
          symtbl_inv IB w se /\
          final_state (L se) s r /\
          IS w s /\
          reply_inv IB w r;
      at_external s q :=
        exists w wA,
          symtbl_inv IB w se /\
          at_external (L se) s q /\
          IS w s /\
          query_inv IA wA q;
      after_external s r s' :=
        exists w wA q,
          symtbl_inv IB w se /\
          at_external (L se) s q /\
          after_external (L se) s r s' /\
          IS w s /\
          query_inv IA wA q /\
          reply_inv IA wA r /\
          IS w s';
    globalenv :=
      globalenv (L se);
  |}.

  Definition restrict :=
    {|
      skel := skel L;
      state := state L;
      activate se := restrict_lts se;
    |}.

  Lemma restrict_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) L restrict.
  Proof.
    fsim (apply forward_simulation_step with (match_states := rel_inv (IS w));
          destruct Hse; subst); cbn; auto.
    - destruct 1. reflexivity.
    - intros q _ s [Hq] Hs. exists s.
      assert (IS w s) by (eapply preserves_initial_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros s _ r [Hs] Hr. exists r.
      assert (reply_inv IB w r) by (eapply preserves_final_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros s _ q [Hs] Hx.
      edestruct @preserves_external as (wA & HseA & Hq & Hk); eauto.
      eexists wA, q. intuition eauto 10 using rel_inv_intro.
      destruct H0. exists s1'. intuition eauto 20 using rel_inv_intro.
    - intros s t s' STEP _ [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto 10 using rel_inv_intro.
  Qed.
End RESTRICT.

(** ** Weakening the target semantics *)

Section EXPAND.
  Context {liA liB} (L: semantics liA liB).
  Context (IA: invariant liA) (IB: invariant liB).
  Context (IS: inv_world IB -> state L -> Prop).

  Definition expand_lts se :=
    {|
      valid_query q :=
        valid_query (L se) q;
      step ge s t s' :=
        forall w, symtbl_inv IB w se -> IS w s -> step (L se) ge s t s';
      initial_state q s :=
        forall w, symtbl_inv IB w se -> query_inv IB w q -> initial_state (L se) q s;
      final_state s r :=
        forall w, symtbl_inv IB w se -> IS w s -> final_state (L se) s r;
      at_external s q :=
        forall w, symtbl_inv IB w se -> IS w s -> at_external (L se) s q;
      after_external s r s' :=
        forall w wA q, symtbl_inv IB w se -> IS w s -> at_external (L se) s q ->
        query_inv IA wA q -> reply_inv IA wA r -> after_external (L se) s r s';
      globalenv :=
        globalenv (L se);
    |}.

  Definition expand :=
    {|
      skel := skel L;
      state := state L;
      activate se := expand_lts se;
    |}.

  Lemma expand_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) expand L.
  Proof.
    fsim (apply forward_simulation_step with (match_states := rel_inv (IS w));
          destruct Hse; subst); cbn; auto.
    - destruct 1; reflexivity.
    - intros q _ s [Hq] Hs. exists s.
      assert (IS w s) by (eapply preserves_initial_state; eauto).
      eauto using rel_inv_intro.
    - intros s _ r [Hs] Hr.
      assert (reply_inv IB w r) by (eapply preserves_final_state; eauto).
      eauto using rel_inv_intro.
    - intros s _ q [Hs] Hk. specialize (Hk w H Hs).
      edestruct @preserves_external as (wA & HseA & Hq & Hr); eauto.
      exists wA, q. intuition auto using rel_inv_intro.
      destruct H0. exists s1'. intuition eauto using rel_inv_intro.
    - intros s t s' STEP _ [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto using rel_inv_intro.
  Qed.
End EXPAND.

(** ** Using invariants to prove simulations *)

Section METHODS.
  Context {liA1 liA2} {ccA: callconv liA1 liA2}.
  Context {liB1 liB2} {ccB: callconv liB1 liB2}.
  Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).

  Lemma source_invariant_fsim IA IB IS:
    preserves L1 IA IB IS ->
    forward_simulation ccA ccB (restrict L1 IA IB IS) L2 ->
    forward_simulation (IA @ ccA) (IB @ ccB) L1 L2.
  Proof.
    intros HL1 HL.
    eapply compose_forward_simulations; eauto.
    apply restrict_fsim; auto.
  Qed.

  Lemma target_invariant_fsim IA IB IS:
    preserves L2 IA IB IS ->
    forward_simulation ccA ccB L1 (expand L2 IA IB IS) ->
    forward_simulation (ccA @ IA) (ccB @ IB) L1 L2.
  Proof.
    intros HL2 HL.
    eapply compose_forward_simulations; eauto.
    apply expand_fsim; auto.
  Qed.
End METHODS.
