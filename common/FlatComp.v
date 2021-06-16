Require Import Relations.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Smallstep_.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Section FLAT_COMP.
  Context {liA liB S1 S2} (L1: lts liA liB S1) (L2: lts liA liB S2).

  Variant flat_state := | flat_st1 (s: S1) | flat_st2 (s: S2).

  Inductive flat_step: flat_state -> trace -> flat_state -> Prop :=
  | step1 s t s':
      Step L1 s t s' -> flat_step (flat_st1 s) t (flat_st1 s')
  | step2 s t s':
      Step L2 s t s' -> flat_step (flat_st2 s) t (flat_st2 s').

  Inductive flat_initial_state (q: query liB): flat_state -> Prop :=
  | initial_state1 s:
      valid_query L1 q = true ->
      initial_state L1 q s ->
      flat_initial_state q (flat_st1 s)
  | initial_state2 s:
      valid_query L2 q = true ->
      initial_state L2 q s ->
      flat_initial_state q (flat_st2 s).

  Inductive flat_at_external: flat_state -> query liA -> Prop :=
  | at_external1 s q:
      at_external L1 s q ->
      flat_at_external (flat_st1 s) q
  | at_external2 s q:
      at_external L2 s q ->
      flat_at_external (flat_st2 s) q.

  Inductive flat_after_external: flat_state -> reply liA -> flat_state -> Prop :=
  | after_external1 s r s':
      after_external L1 s r s' ->
      flat_after_external (flat_st1 s) r (flat_st1 s')
  | after_external2 s r s':
      after_external L2 s r s' ->
      flat_after_external (flat_st2 s) r (flat_st2 s').

  Inductive flat_final_state: flat_state -> reply liB -> Prop :=
  | final_state1 s r:
      final_state L1 s r ->
      flat_final_state (flat_st1 s) r
  | final_state2 s r:
      final_state L2 s r ->
      flat_final_state (flat_st2 s) r.

  Definition flat_lts :=
    {|
    step ge := flat_step;
    valid_query q := valid_query L1 q || valid_query L2 q;
    initial_state := flat_initial_state;
    at_external := flat_at_external;
    after_external := flat_after_external;
    final_state := flat_final_state;
    globalenv := tt;
    |}.

End FLAT_COMP.

Notation "L1 ⊎ L2" :=  (flat_lts L1 L2)(at level 40, left associativity): lts_scope.

Require Import CategoricalComp.

Section IDENTITY.
  Context {li S} (L : lts li li S).

  Inductive id_state_match: (@flat_state (@id_state li) S) -> S -> Prop :=
  | id_state_match_intro s:
      id_state_match (flat_st2 s) s.

  Lemma identity1: 1 ⊎ L ≤ L.
  Proof.
    apply fsim_lts_trivial_order.
    eexists. intros se.
    eapply forward_simulation_step with (match_states := id_state_match);
      intros; inv H; cbn; auto; inv H0.
    - inv H.
    - eexists; repeat constructor; eauto.
    - eexists; repeat constructor; eauto.
    - exists tt. exists q1. repeat apply conj; try constructor; auto.
      intros.  inv H0. eexists; repeat constructor; eauto.
    - eexists; repeat constructor; eauto.
  Qed.

  Hypothesis init_state_valid: forall q s, initial_state L q s -> valid_query L q = true.

  Lemma identity2: L ≤ 1 ⊎ L.
  Proof.
    apply fsim_lts_trivial_order.
    eexists. intros se.
    eapply forward_simulation_step with (match_states := fun s1 s2 => id_state_match s2 s1);
      intros; cbn; auto.
    - now inv H.
    - inv H. exists (flat_st2 s1).
      split; constructor; auto.
      eapply init_state_valid. eauto.
    - inv H. eexists. split; try constructor; auto.
    - inv H. exists tt. exists q1. repeat apply conj; try constructor; auto.
      intros. subst. eexists; repeat constructor; eauto.
    - inv H0. eexists; repeat constructor; eauto.
  Qed.

  Theorem flat_comp_left_identity: 1 ⊎ L ≡ L.
  Proof.
    split; [ exact identity1 | exact identity2 ].
  Qed.

  Inductive id_state_match': (@flat_state S (@id_state li)) -> S -> Prop :=
  | id_state_match'_intro s:
      id_state_match' (flat_st1 s) s.

  Lemma identity3: L ⊎ 1 ≤ L.
  Proof.
    apply fsim_lts_trivial_order.
    eexists. intros se.
    eapply forward_simulation_step with (match_states := id_state_match');
      intros; inv H; cbn; rewrite? orb_false_r; auto; inv H0.
    - eexists; repeat constructor; eauto.
    - inv H1. inv H.
    - eexists; repeat constructor; eauto.
    - exists tt. exists q1. repeat apply conj; try constructor; auto.
      intros. inv H0. eexists; repeat constructor; eauto.
    - eexists; repeat constructor; eauto.
  Qed.

  Lemma identity4: L ≤ L ⊎ 1.
  Proof.
    apply fsim_lts_trivial_order.
    eexists. intros se.
    eapply forward_simulation_step with (match_states := fun s1 s2 => id_state_match' s2 s1);
      intros; cbn; auto; try inv H.
    - now rewrite orb_false_r.
    - eexists; repeat constructor; auto.
      eapply init_state_valid; eauto.
    - eexists; repeat constructor; auto.
    - exists tt. exists q1. repeat apply conj; try constructor; auto.
      intros. subst. eexists; repeat constructor; auto.
    - inv H0. eexists; repeat constructor; auto.
  Qed.

  Theorem flat_comp_right_identity: L ⊎ 1 ≡ L.
  Proof.
    split; [ exact identity3 | exact identity4 ].
  Qed.

End IDENTITY.

Section DIST.
  Context {liA liB liC S1 S2 S}
          (L1: lts liB liC S1) (L2: lts liB liC S2)
          (L: lts liA liB S).

  Inductive dist_match_state:
    (@comp_state (@flat_state S1 S2) S) ->
    (@flat_state (@comp_state S1 S) (@comp_state S2 S)) -> Prop :=
  | dist_match_state1 s1:
      dist_match_state (st1 (flat_st1 s1)) (flat_st1 (st1 s1))
  | dist_match_state2 s2:
      dist_match_state (st1 (flat_st2 s2)) (flat_st2 (st1 s2))
  | dist_match_state3 s1 s:
      dist_match_state (st2 (flat_st1 s1) s) (flat_st1 (st2 s1 s))
  | dist_match_state4 s2 s:
      dist_match_state (st2 (flat_st2 s2) s) (flat_st2 (st2 s2 s)).

  Lemma distributivity1: (L1 ⊎ L2) ∘ L ≤ (L1 ∘ L) ⊎ (L2 ∘ L).
  Proof.
    apply fsim_lts_trivial_order. eexists. intros se.
    eapply forward_simulation_step with (match_states := dist_match_state).
    - intros. inv H. cbn.
      do 2 rewrite <- orb_assoc. f_equal.
      rewrite orb_comm. rewrite <- orb_assoc. f_equal.
      apply orb_diag.
    - intros. inv H; inv H0; inv H.
      + eexists; split; repeat constructor; auto.
        cbn. now rewrite H0.
      + eexists; split. apply initial_state2.
        cbn. now rewrite H0. constructor; eauto.
        constructor.
    - intros. inv H; inv H0; inv H1; eexists; repeat constructor; auto.
    - intros. inv H; inv H0.
      + exists tt. eexists. repeat apply conj; repeat constructor; auto.
        intros. inv H. inv H0. eexists; repeat constructor; auto.
      + exists tt. eexists. repeat apply conj; repeat constructor; auto.
        intros. inv H. inv H0. eexists; repeat constructor; auto.
    - intros. inv H0; inv H; try inv H1.
      + eexists; repeat constructor; auto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + inv H5. eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + inv H5. eexists. split; [ | constructor ]. repeat econstructor; eauto.
  Qed.

  Hypothesis init_state_valid1: forall q s, initial_state L1 q s -> valid_query L1 q = true.
  Hypothesis init_state_valid2: forall q s, initial_state L2 q s -> valid_query L2 q = true.

  Lemma distributivity2: (L1 ∘ L) ⊎ (L2 ∘ L) ≤ (L1 ⊎ L2) ∘ L.
  Proof.
    apply fsim_lts_trivial_order. eexists. intros se.
    eapply forward_simulation_step with (match_states := fun s1 s2 => dist_match_state s2 s1).
    - intros. inv H. cbn.
      do 2 rewrite <- orb_assoc. f_equal.
      rewrite orb_comm. rewrite orb_assoc. f_equal.
      symmetry. apply orb_diag.
    - intros. inv H; inv H0; inv H1.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
    - intros. inv H; inv H0; inv H1.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
    - intros. inv H; inv H0; inv H1.
      + exists tt. exists q1. repeat apply conj; repeat constructor; auto.
        intros. inv H. inv H0. inv H1.
        eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + exists tt. exists q1. repeat apply conj; repeat constructor; auto.
        intros. inv H. inv H0. inv H1.
        eexists. split; [ | constructor ]. repeat econstructor; eauto.
    - intros. inv H0; inv H; inv H1.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
      + eexists. split; [ | constructor ]. repeat econstructor; eauto.
  Qed.

  Theorem flat_categorical_comp_distributivity:
    (L1 ⊎ L2) ∘ L ≡ (L1 ∘ L) ⊎ (L2 ∘ L).
  Proof.
    split; [ exact distributivity1 | exact distributivity2 ].
  Qed.
End DIST.
