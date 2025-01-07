Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.
Require Import Classical.
Require Import SmallstepLinking.

(** * Compatibility with forward simulations *)

(** ** Simulation relation *)

Section FSIM.
  Context {li1 li2} (cc: callconv li1 li2).

  Notation I := bool.
  Context (L1 : I -> Smallstep.semantics li1 li1).
  Context (L2 : I -> Smallstep.semantics li2 li2).
  Context (HL : forall i, fsim_components cc cc (L1 i) (L2 i)).
  Context (se1 se2: Genv.symtbl) (w : ccworld cc).
  Context (Hse: match_senv cc w se1 se2).
  Context (Hse1: forall i, Genv.valid_for (skel (L1 i)) se1).
  Notation index := {i & fsim_index (HL i)}.

  Inductive match_topframes wk: index -> frame L1 -> frame L2 -> Prop :=
    match_topframes_intro i s1 s2 idx:
      match_senv cc wk se1 se2 ->
      Genv.valid_for (skel (L1 i)) se1 ->
      fsim_match_states (HL i) se1 se2 wk idx s1 s2 ->
      match_topframes wk
        (existT _ i idx)
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_contframes wk wk': frame L1 -> frame L2 -> Prop :=
    match_contframes_intro i s1 s2:
      match_senv cc wk' se1 se2 ->
      (forall r1 r2 s1', match_reply cc wk r1 r2 ->
       Smallstep.after_external (L1 i se1) s1 r1 s1' ->
       exists idx s2',
         Smallstep.after_external (L2 i se2) s2 r2 s2' /\
         fsim_match_states (HL i) se1 se2 wk' idx s1' s2') ->
      match_contframes wk wk'
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_states: index -> list (frame L1) -> list (frame L2) -> Prop :=
    | match_states_cons wk idx f1 f2 k1 k2:
        match_topframes wk idx f1 f2 ->
        match_cont wk k1 k2 ->
        match_states idx (f1 :: k1) (f2 :: k2)
  with match_cont: ccworld cc -> _ -> _ -> Prop :=
    | match_cont_cons wk wk' f1 f2 k1 k2:
        match_contframes wk wk' f1 f2 ->
        match_cont wk' k1 k2 ->
        match_cont wk (f1 :: k1) (f2 :: k2)
    | match_cont_nil:
        match_cont w nil nil.

  Inductive order: index -> index -> Prop :=
    order_intro i x y: fsim_order (HL i) x y -> order (existT _ i x) (existT _ i y).

  (** ** Simulation properties *)

  Lemma step_simulation:
    forall idx s1 s2 t s1', match_states idx s1 s2 -> step L1 se1 s1 t s1' ->
    exists idx' s2',
      (plus (fun _ => step L2 se2) tt s2 t s2' \/
       star (fun _ => step L2 se2) tt s2 t s2' /\ order idx' idx) /\
      match_states idx' s1' s2'.
  Proof.
    intros idx s1 s2 t s1' Hs Hs1'.
    destruct Hs1'; inv Hs.
    - (* internal step *)
      inv H3; subst_dep. clear idx0.
      edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto using fsim_lts.
      eexists (existT _ i idx'), _. split.
      * destruct Hs2'; [left | right]; intuition eauto using star_internal, plus_internal.
        constructor. auto.
      * econstructor; eauto. econstructor; eauto.
    - (* cross-component call *)
      inv H6; subst_dep. clear idx0.
      edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hsex & Hrx); eauto using fsim_lts.
      pose proof (fsim_lts (HL j) _ _ Hsex (Hse1 j)).
      edestruct @fsim_match_initial_states as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_push; eauto 1.
        erewrite fsim_match_valid_query; eauto.
      + repeat (econstructor; eauto).
    - (* cross-component return *)
      inv H5; subst_dep. clear idx0.
      pose proof (fsim_lts (HL i) _ _ H4 H8).
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      inv H7. inv H9; subst_dep. edestruct H11 as (idx' & s2' & Hs2'& Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_pop; eauto.
      + repeat (econstructor; eauto).
  Qed.

  Lemma initial_states_simulation:
    forall q1 q2 s1, match_query cc w q1 q2 -> initial_state L1 se1 q1 s1 ->
    exists idx s2, initial_state L2 se2 q2 s2 /\ match_states idx s1 s2.
  Proof.
    intros q1 q2 _ Hq [i s1 Hq1 Hs1].
    pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    exists (existT _ i idx), (st L2 i s2 :: nil).
    split; econstructor; eauto.
    + erewrite fsim_match_valid_query; eauto.
    + econstructor; eauto.
    + constructor.
  Qed.

  Lemma final_states_simulation:
    forall idx s1 s2 r1, match_states idx s1 s2 -> final_state L1 se1 s1 r1 ->
    exists r2, final_state L2 se2 s2 r2 /\ match_reply cc w r1 r2.
  Proof.
    clear. intros idx s1 s2 r1 Hs Hr1. destruct Hr1 as [i s1 r1 Hr1].
    inv Hs. inv H4. inv H2. subst_dep. clear idx0.
    pose proof (fsim_lts (HL i) _ _ H1 H4).
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    exists r2. split; eauto. constructor; eauto.
  Qed.

  Lemma external_simulation:
    forall idx s1 s2 qx1, match_states idx s1 s2 -> at_external L1 se1 s1 qx1 ->
    exists wx qx2, at_external L2 se2 s2 qx2 /\ match_query cc wx qx1 qx2 /\ match_senv cc wx se1 se2 /\
    forall rx1 rx2 s1', match_reply cc wx rx1 rx2 -> after_external L1 se1 s1 rx1 s1' ->
    exists idx' s2', after_external L2 se2 s2 rx2 s2' /\ match_states idx' s1' s2'.
  Proof.
    clear - HL Hse1.
    intros idx s1 s2 q1 Hs Hq1. destruct Hq1 as [i s1 qx1 k1 Hqx1 Hvld].
    inv Hs. inv H2. subst_dep. clear idx0.
    pose proof (fsim_lts (HL i) _ _ H1 H5) as Hi.
    edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hsex & H); eauto.
    exists wx, qx2. intuition idtac.
    + constructor. eauto.
      intros j. pose proof (fsim_lts (HL j) _ _ Hsex (Hse1 j)).
      erewrite fsim_match_valid_query; eauto.
    + inv H2; subst_dep.
      edestruct H as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ i idx'), _.
      split; repeat (econstructor; eauto).
  Qed.

  Lemma semantics_simulation sk1 sk2:
    fsim_properties cc cc se1 se2 w
      (semantics L1 sk1 se1)
      (semantics L2 sk2 se2)
      index order match_states.
  Proof.
    split; cbn.
    - intros. unfold valid_query. f_equal.
      + eapply (fsim_lts (HL true)); eauto.
      + eapply (fsim_lts (HL false)); eauto.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using step_simulation.
  Qed.
End FSIM.

Lemma compose_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  forward_simulation cc cc L1a L2a ->
  forward_simulation cc cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  forward_simulation cc cc L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  set (L1 := fun i:bool => if i then L1a else L1b).
  set (L2 := fun i:bool => if i then L2a else L2b).
  assert (HL: forall i, fsim_components cc cc (L1 i) (L2 i)) by (intros [|]; auto).
  constructor.
  eapply Forward_simulation with (order cc L1 L2 HL) (match_states cc L1 L2 HL).
  - destruct Ha, Hb. cbn. congruence.
  - intros se1 se2 w Hse Hse1.
    eapply semantics_simulation; eauto.
    pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
    intros [|]; cbn; eapply Genv.valid_for_linkorder; eauto.
  - clear - HL. intros [i x].
    induction (fsim_order_wf (HL i) x) as [x Hx IHx].
    constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
Qed.

