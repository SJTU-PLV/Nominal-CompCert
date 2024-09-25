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
               

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

(*
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
 *)

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)
Import GS.

Lemma preserves_fsim {li} (L: semantics li li) I IS:
  preserves L I I IS ->
  forward_simulation (cc_inv I) L L.
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
    + intros r' r'' s' t t' [Hr'] Hs'.
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

Lemma restrict_fsim :
  forall {li: language_interface} (L : semantics li li) (I: invariant li)
    (IS : inv_world I -> state L -> Prop),
    preserves L I I IS -> GS.forward_simulation I L (restrict L I I IS).
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
      destruct H2. exists s1'. intuition eauto 20 using rel_inv_intro.
    - intros s t s' STEP a b [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto 10 using rel_inv_intro.
    - auto using well_founded_ltof.
Qed.

  
Infix "@" := GS.cc_compose (at level 30, right associativity).

Section METHODS.
  Context {li1 li2} {cc: GS.callconv li1 li2}.
  Context (L1: semantics li1 li1) (L2: semantics li2 li2).

  Lemma source_invariant_fsim I IS:
    preserves L1 I I IS ->
    GS.forward_simulation cc (restrict L1 I I IS) L2 ->
    GS.forward_simulation (I @ cc) L1 L2.
  Proof.
    intros HL1 HL.
    eapply st_fsim_vcomp; eauto.
    apply restrict_fsim; auto.
  Qed.

End METHODS.
