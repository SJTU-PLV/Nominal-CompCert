Require Import Values.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Smallstep.

Require Import Invariant.
Require Import CallconvBig VCompBig.
               
(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [IS]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record lts_preserves {li S} se (L: lts li li S) I (IS: _ -> S -> Prop) w :=
  {
    preserves_step s t s':
      IS w s ->
      Step L s t s' ->
      IS w s';
    preserves_initial_state q s:
      query_inv I w q ->
      initial_state L q s ->
      IS w s;
    preserves_external s q:
      IS w s -> at_external L s q ->
      exists wA, symtbl_inv I wA se /\ query_inv I wA q /\
      forall r s', reply_inv I wA r -> after_external L s r s' -> IS w s';
    preserves_final_state s r:
      IS w s ->
      final_state L s r ->
      reply_inv I w r;
  }.

Definition preserves {li} (L: semantics li li) (I: invariant _) IS :=
  forall w se,
    Genv.valid_for (skel L) se ->
    symtbl_inv I w se ->
    lts_preserves se (L se) I IS w.

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Program Coercion cc_inv {li : language_interface} (I : invariant li) : GS.callconv li li :=
  {|
    GS.ccworld := inv_world I;
    GS.ccworld_world := world_unit;
    GS.match_senv := fun w => rel_inv (symtbl_inv I w);
    GS.match_query := fun w => rel_inv (query_inv I w);
    GS.match_reply := fun w => rel_inv (reply_inv I w)
  |}.
Next Obligation.
  inv H. reflexivity.
Qed.
Next Obligation.
  inv H. auto.
Qed.


(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li} (L: semantics li li) I IS:
  preserves L I IS ->
  GS.forward_simulation (cc_inv I) L L.
Proof.
  intros MATCH. constructor.
  eapply GS.Forward_simulation; eauto.
  intros se1 se2 w Hse Hse1. (eapply GS.forward_simulation_step with (match_states := fun _ => rel_inv (IS w));
                                
                                destruct Hse; subst).
  - destruct 1. auto.
  - intros q _ s [Hq] Hs.
    exists s. split; eauto.
    constructor.
    eapply preserves_initial_state; eauto.
  - intros gw s _ r [Hs] Hr.
    exists r, tt. split; eauto.
    constructor. reflexivity. split. reflexivity. constructor.
    eapply preserves_final_state; eauto.
  - intros gw s _ q [Hs] Hq.
    edestruct @preserves_external as (wA & Hse & HqA & Hr); eauto.
    exists wA, q. repeat apply conj; cbn; eauto.
    + constructor. auto.
    + constructor. auto.
    + intros r' r'' s' t [Hr'] Hs'. inv H0.
      exists s'. split; eauto.
      econstructor.
      eapply Hr; eauto.
  - intros s t s' Hstep a b [Hs].
    exists s'. split; eauto.
    constructor.
    eapply preserves_step; eauto.
  - auto using well_founded_ltof.
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
  composed with that proved by the user to obtain the desired one. *)

(** ** Strengthening the source semantics *)


Section RESTRICT.
  Context {li} (L: semantics li li).
  Context (I: invariant li).
  Context (IS: inv_world I -> state L -> Prop).

  Definition restrict_lts se :=
    {|
      step ge s t s' :=
        step (L se) ge s t s' /\
        exists w,
          symtbl_inv I w se /\
          IS w s /\
          IS w s';
      valid_query q :=
        valid_query (L se) q;
      initial_state q s :=
        initial_state (L se) q s /\
        exists w,
          symtbl_inv I w se /\
          query_inv I w q /\
          IS w s;
      final_state s r :=
        final_state (L se) s r /\
        exists w,
          symtbl_inv I w se /\
          IS w s /\
          reply_inv I w r;
      at_external s q :=
        at_external (L se) s q /\
        exists w wA,
          symtbl_inv I w se /\
          IS w s /\
          query_inv I wA q;
      after_external s r s' :=
        after_external (L se) s r s' /\
        exists w wA q,
          symtbl_inv I w se /\
          at_external (L se) s q /\
          IS w s /\
          query_inv I wA q /\
          reply_inv I wA r /\
          IS w s';
    globalenv :=
      globalenv (L se);
  |}.

  Definition restrict :=
    {|
      skel := skel L;
      state := state L;
      (* memory_of_state := memory_of_state L; *)
      activate se := restrict_lts se;
    |}.

  Lemma restrict_fsim:
    preserves L I IS ->
    GS.forward_simulation (cc_inv I) L restrict.
  Proof.
    intro MATCH. econstructor.
    econstructor. reflexivity.
    intros se1 sae2 w Hse Hse1. eapply GS.forward_simulation_step with (match_states := fun _ =>rel_inv (IS w));(destruct Hse; subst); cbn; auto.
    - destruct 1. reflexivity.
    - intros q _ s [Hq] Hs. exists s.
      assert (IS w s) by (eapply preserves_initial_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros gw s _ r [Hs] Hr. exists r.
      assert (reply_inv I w r) by (eapply preserves_final_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros tt s _ q [Hs] Hx.
      edestruct @preserves_external as (wA & HseA & Hq & Hk); eauto.
      eexists wA, q. intuition eauto 10 using rel_inv_intro.
      destruct H3. exists s1'. intuition eauto 20 using rel_inv_intro.
    - intros s t s' STEP a b [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto 10 using rel_inv_intro.
    - auto using well_founded_ltof.
  Qed.

  Lemma restrict_determinate:
    determinate L ->
    determinate restrict.
  Proof.
    intros HL se. specialize (HL se) as [ ].
    split; unfold nostep, not, single_events in *; cbn; intros;
    repeat (lazymatch goal with H : _ /\ _ |- _ => destruct H as [H _] end);
    eauto.
  Qed.
End RESTRICT.
  
Infix "@" := GS.cc_compose (at level 30, right associativity).

Section METHODS.
  Context {li1 li2} {cc: GS.callconv li1 li2}.
  Context (L1: semantics li1 li1) (L2: semantics li2 li2).

  Lemma source_invariant_fsim I IS:
    preserves L1 I IS ->
    GS.forward_simulation cc (restrict L1 I IS) L2 ->
    GS.forward_simulation (I @ cc) L1 L2.
  Proof.
    intros HL1 HL.
    eapply st_fsim_vcomp; eauto.
    apply restrict_fsim; auto.
  Qed.

End METHODS.
