Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.
Require Import Classical.

(** NB: we assume that all components are deterministic and that their
  domains are disjoint. *)

Parameter (valid_query : forall {li}, Smallstep.open_sem li li -> Senv.t -> query li -> Prop).
Axiom valid_query_determ:
  forall {li} (L1 L2: open_sem li li) sk se q,
    link (skel L1) (skel L2) = Some sk -> valid_query L1 se q -> valid_query L2 se q -> False.

Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.

Section LINK.
  Context {li I} (L : I -> open_sem li li).

  (** * Definition *)

  Section WITH_SE.
    Context (se: Senv.t).

    Variant frame := st (i: I) (q: query li) (s: Smallstep.state (L i se q)).
    Notation state := (list frame).

    Inductive step: state -> trace -> state -> Prop :=
      | step_internal i q s t s' k :
          Step (L i se q) s t s' ->
          step (st i q s :: k) t (st i q s' :: k)
      | step_push i q j s qx s' k :
          Smallstep.at_external (L i se q) s qx ->
          valid_query (L j) se qx ->
          Smallstep.initial_state (L j se qx) s' ->
          step (st i q s :: k) E0 (st j qx s' :: st i q s :: k)
      | step_pop i qx j q s sk r s' k :
          Smallstep.final_state (L i se qx) s r ->
          Smallstep.after_external (L j se q) sk r s' ->
          step (st i qx s :: st j q sk :: k) E0 (st j q s' :: k).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s :
          valid_query (L i) se q ->
          Smallstep.initial_state (L i se q) s ->
          initial_state q (st i q s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro i q s qx k:
          Smallstep.at_external (L i se q) s qx ->
          (forall j, ~ valid_query (L j) se qx) ->
          at_external (st i q s :: k) qx.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro i q s r s' k:
          Smallstep.after_external (L i se q) s r s' ->
          after_external (st i q s :: k) r (st i q s' :: k).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro i q s r :
          Smallstep.final_state (L i se q) s r ->
          final_state (st i q s :: nil) r.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics: open_sem li li :=
    {|
      activate se q :=
        {|
          Smallstep.step ge := step se;
          Smallstep.initial_state := initial_state se q;
          Smallstep.at_external := at_external se;
          Smallstep.after_external := after_external se;
          Smallstep.final_state := final_state se;
          Smallstep.globalenv := tt;
        |};
      skel := sk;
    |}.

  (** * Properties *)

  Lemma star_internal se i q s t s' k:
    Star (L i se q) s t s' ->
    star (fun _ => step se) tt (st se i q s :: k) t (st se i q s' :: k).
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal se i q s t s' k:
    Plus (L i se q) s t s' ->
    plus (fun _ => step se) tt (st se i q s :: k) t (st se i q s' :: k).
  Proof.
    destruct 1; econstructor; eauto using step_internal, star_internal.
  Qed.

  (** * Receptiveness and determinacy *)

  Hypothesis valid_query_excl:
    forall i j se q, valid_query (L i) se q -> valid_query (L j) se q -> i = j.

  Lemma semantics_receptive:
    (forall i, open_receptive (L i)) ->
    open_receptive semantics.
  Proof.
    intros HL se q. unfold open_receptive in HL.
    constructor; cbn.
    - intros s t1 s1 t2 STEP Ht. destruct STEP.
      + edestruct @sr_receptive; eauto. eexists. eapply step_internal; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_push; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_pop; eauto.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sr_traces; eauto.
  Qed.

  Lemma semantics_determinate:
    (forall i, open_determinate (L i)) ->
    open_determinate semantics.
  Proof.
    intros HL se q. unfold open_determinate in HL.
    constructor; cbn.
    - destruct 1; inversion 1; subst_dep.
      + edestruct (sd_determ (HL i se q0) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_at_external_nostep; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_at_external_nostep; eauto.
      + destruct (sd_at_external_determ (HL i se q0) s qx qx0); eauto.
        assert (j0 = j) by eauto; subst.
        destruct (sd_initial_determ (HL j se qx) s' s'0); eauto.
        intuition auto. constructor.
      + eelim sd_final_noext; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_final_noext; eauto.
      + edestruct (sd_final_determ (HL i se qx) s r r0); eauto.
        edestruct (sd_after_external_determ (HL j se q0) sk0 r s' s'0); eauto.
        intuition auto. constructor.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sd_traces; eauto.
    - destruct 1; inversion 1; subst. assert (i0 = i) by eauto; subst.
      edestruct (sd_initial_determ (HL i se q) s s0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_at_external_nostep; eauto.
      + edestruct (sd_at_external_determ (HL i se q0) s qx qx0); eauto. eapply H0; eauto.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_after_external_determ (HL i se q0) s r s' s'0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_final_nostep; eauto.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_determ; eauto.
  Qed.

End LINK.

(** * Compatibility with forward simulations *)

(** ** Measure *)

(** Because the measure types and orders used by the simulations are
  existentially sealed by [forward_simulation], we need to use the
  following generic "meta-order". *)

Inductive index :=
  | mkind {T: Type} (lt: T -> T -> Prop) (Hlt: well_founded lt) (t: T).

Inductive order : index -> index -> Prop :=
  | ord_intro T (lt : T -> T -> Prop) Hlti Hltj i j:
      lt i j -> order (mkind lt Hlti i) (mkind lt Hltj j).

Lemma order_well_founded:
  well_founded order.
Proof.
  clear. intros [T lt Hlt i]. pose proof (Hlt i) as Hi. revert Hlt.
  induction Hi. constructor. intros y Hy.
  inv Hy; subst_dep. clear - H3 H0. eauto.
Qed.

(** ** Simulation relation *)

(** Likewise, we need to embed the simulation data into our simulation
  relation. This aspect makes it a little bit convoluted but it is
  otherwise straightforward. *)

Section FSIM.
  Context {li1 li2} (cc: callconv li1 li2).
  Context {I L1 L2} (HL: forall i:I, open_fsim cc cc (L1 i) (L2 i)).
  Context {sk1 sk2: AST.program unit unit}.
  Context {w se1 se2 q1 q2}
    (Hsk1: forall i, Senv.valid_for (skel (L1 i)) se1)
    (Hsk: forall i, match_skel se1 se2 (skel (L1 i)) (skel (L2 i)))
    (Hse: match_senv cc w se1 se2)
    (Hq: match_query cc w q1 q2).

  Inductive match_topframes wk: _ -> frame L1 se1 -> frame L2 se2 -> Prop :=
    match_topframes_intro i ind ord q1 q2 s1 s2 ms idx:
      forall (H: fsim_properties cc (match_reply cc wk) (L1 i se1 q1) (L2 i se2 q2) ind ord ms),
      ms idx s1 s2 ->
      match_topframes wk
        (mkind ord (fsim_order_wf H) idx)
        (st L1 se1 i q1 s1)
        (st L2 se2 i q2 s2).

  Inductive match_contframes wk wk': frame L1 se1 -> frame L2 se2 -> Prop :=
    match_contframes_intro i ind ord q1 q2 s1 s2 ms:
      forall (H: fsim_properties cc (match_reply cc wk') (L1 i se1 q1) (L2 i se2 q2) ind ord ms),
      (forall r1 r2 s1', match_reply cc wk r1 r2 ->
       Smallstep.after_external (L1 i se1 q1) s1 r1 s1' ->
       exists idx s2', Smallstep.after_external (L2 i se2 q2) s2 r2 s2' /\ ms idx s1' s2') ->
      match_contframes wk wk'
        (st L1 se1 i q1 s1)
        (st L2 se2 i q2 s2).

  Inductive match_states: index -> list (frame L1 se1) -> list (frame L2 se2) -> Prop :=
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
      inv H3; subst_dep. clear ms H0 ms1 H8.
      edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (mkind ord (fsim_order_wf H6) idx'), _. split.
      * destruct Hs2'; [left | right]; intuition eauto using star_internal, plus_internal.
        constructor. auto.
      * econstructor; eauto. econstructor; eauto.
    - (* cross-component call *)
      inv H5; subst_dep. clear ms H2 ms1 H10.
      edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hrx); eauto.
      edestruct (HL j wx) as [indj ordj msj Hj]; eauto. admit. (* match_senv *)
      edestruct @fsim_match_initial_states as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (mkind ordj (fsim_order_wf Hj) idx'), _. split.
      + left. apply plus_one. eapply step_push; eauto. admit. (* valid_query *)
      + repeat (econstructor; eauto).
    - (* cross-component return *)
      inv H4; subst_dep. clear H1 ms H9 ms1.
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      inv H6. inv H4; subst_dep. edestruct H9 as (idx' & s2' & Hs2'& Hs'); eauto.
      eexists (mkind ord0 (fsim_order_wf H6) idx'), _. split.
      + left. apply plus_one. eapply step_pop; eauto.
      + repeat (econstructor; eauto).
  Admitted.

  Lemma initial_states_simulation:
    forall s1, initial_state L1 se1 q1 s1 ->
    exists idx s2, initial_state L2 se2 q2 s2 /\ match_states idx s1 s2.
  Proof.
    intros _ [i s1 Hq1 Hs1].
    destruct (HL i w se1 se2 q1 q2 (Hsk1 i) (Hsk i) Hse Hq) as [ind ord ms Hms].
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    exists (mkind ord (fsim_order_wf Hms) idx), (st L2 se2 i q2 s2 :: nil).
    split; econstructor; eauto.
    + admit. (* valid_query *)
    + econstructor; eauto.
    + constructor.
  Admitted.

  Lemma final_states_simulation:
    forall idx s1 s2 r1, match_states idx s1 s2 -> final_state L1 se1 s1 r1 ->
    exists r2, final_state L2 se2 s2 r2 /\ match_reply cc w r1 r2.
  Proof.
    clear. intros idx s1 s2 r1 Hs Hr1. destruct Hr1 as [i q1 s1 r1 Hr1].
    inv Hs. inv H4. inv H2. subst_dep. clear ms H ms1 H6.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    exists r2. split; eauto. constructor; eauto.
  Qed.

  Lemma external_simulation:
    forall idx s1 s2 qx1, match_states idx s1 s2 -> at_external L1 se1 s1 qx1 ->
    exists wx qx2, at_external L2 se2 s2 qx2 /\ match_query cc wx qx1 qx2 /\
    forall rx1 rx2 s1', match_reply cc wx rx1 rx2 -> after_external L1 se1 s1 rx1 s1' ->
    exists idx' s2', after_external L2 se2 s2 rx2 s2' /\ match_states idx' s1' s2'.
  Proof.
    clear. intros idx s1 s2 q1 Hs Hq1. destruct Hq1 as [i q1 s1 qx1 k1 Hqx1 Hvld].
    inv Hs. inv H2. subst_dep. clear ms H ms1 H7.
    edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & H); eauto.
    exists wx, qx2. intuition idtac.
    + constructor; eauto. admit. (* valid query vs. match_query *)
    + inv H1; subst_dep.
      edestruct H as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (mkind _ (fsim_order_wf H5) idx'), _.
      split; repeat (econstructor; eauto).
  Admitted.

  Lemma semantics_simulation:
    fsim_properties cc (match_reply cc w)
      (semantics L1 sk1 se1 q1)
      (semantics L2 sk2 se2 q2)
      index order match_states.
  Proof.
    split; cbn.
    - apply order_well_founded.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using step_simulation.
  Qed.

End FSIM.

(** * Linking operator *)

Local Unset Program Cases.

Program Instance Linker_open_sem li: Linker (open_sem li li) :=
  {
    link La Lb :=
      let L i := match i with true => La | false => Lb end in
      option_map (semantics L) (link (skel La) (skel Lb));
    linkorder :=
      open_fsim cc_id cc_id;
  }.
Next Obligation.
  (* identity simulation *)
Admitted.
Next Obligation.
  (* vertical composition of simulations *)
Admitted.
Next Obligation.
  (* fsim between component and linked program (?) *)
Admitted.

Lemma link_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  open_fsim cc cc L1a L2a ->
  open_fsim cc cc L1b L2b ->
  link L1a L1b = Some L1 ->
  link L2a L2b = Some L2 ->
  open_fsim cc cc L1 L2.
Proof.
  intros Ha Hb H1 H2. cbn in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  intros w se1 se2 q1 q2. simpl. intros Hse1 Hsk Hse Hq.
  econstructor. eapply semantics_simulation; eauto.
  - intros [|]; auto.
  - admit. (* Senv.valid_for vs. skeleton linking *)
  - admit. (* match_skel vs. skeleton linking *)
Admitted.
