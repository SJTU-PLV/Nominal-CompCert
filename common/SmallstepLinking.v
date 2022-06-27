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

Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.

Section LINK.
  Context {I li} (L: I -> semantics li li).

  (** * Definition *)

  Section WITH_SE.
    Context (se: Genv.symtbl).

    Variant frame := st (i: I) (s: Smallstep.state (L i)).
    Notation state := (list frame).

    Inductive step: state -> trace -> state -> Prop :=
      | step_internal i s t s' k :
          Step (L i se) s t s' ->
          step (st i s :: k) t (st i s' :: k)
      | step_push i j s q s' k :
          Smallstep.at_external (L i se) s q ->
          valid_query (L j) se q ->
          Smallstep.initial_state (L j se) q s' ->
          step (st i s :: k) E0 (st j s' :: st i s :: k)
      | step_pop i j s sk r s' k :
          Smallstep.final_state (L i se) s r ->
          Smallstep.after_external (L j se) sk r s' ->
          step (st i s :: st j sk :: k) E0 (st j s' :: k).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s :
          valid_query (L i) se q ->
          Smallstep.initial_state (L i se) q s ->
          initial_state q (st i s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro i s q k:
          Smallstep.at_external (L i se) s q ->
          (forall j, ~ valid_query (L j) se q) ->
          at_external (st i s :: k) q.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro i s r s' k:
          Smallstep.after_external (L i se) s r s' ->
          after_external (st i s :: k) r (st i s' :: k).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro i s r :
          Smallstep.final_state (L i se) s r ->
          final_state (st i s :: nil) r.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics': semantics li li :=
    {|
      activate se :=
        {|
          Smallstep.step ge := step se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external se;
          Smallstep.after_external := after_external se;
          Smallstep.final_state := final_state se;
          Smallstep.globalenv := tt;
        |};
      skel := sk;
      footprint x := exists i, footprint (L i) x;
    |}.

  (** * Properties *)

  Lemma star_internal se i s t s' k:
    Star (L i se) s t s' ->
    star (fun _ => step se) tt (st i s :: k) t (st i s' :: k).
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal se i s t s' k:
    Plus (L i se) s t s' ->
    plus (fun _ => step se) tt (st i s :: k) t (st i s' :: k).
  Proof.
    destruct 1; econstructor; eauto using step_internal, star_internal.
  Qed.

  (** * Receptiveness and determinacy *)

  Lemma semantics_receptive:
    (forall i, receptive (L i)) ->
    receptive semantics'.
  Proof.
    intros HL se. unfold receptive in HL.
    constructor; cbn.
    - intros s t1 s1 t2 STEP Ht. destruct STEP.
      + edestruct @sr_receptive; eauto. eexists. eapply step_internal; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_push; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_pop; eauto.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sr_traces; eauto.
  Qed.

  Hypothesis valid_query_excl:
    forall i j se (q: query li),
      Smallstep.valid_query (L i) se q ->
      Smallstep.valid_query (L j) se q ->
      i = j.

  Lemma semantics_determinate:
    (forall i, determinate (L i)) ->
    determinate semantics'.
  Proof.
    intros HL se. unfold determinate in HL.
    constructor; cbn.
    - destruct 1; inversion 1; subst_dep.
      + edestruct (sd_determ (HL i se) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_at_external_nostep; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_at_external_nostep; eauto.
      + destruct (sd_at_external_determ (HL i se) s q q0); eauto.
        assert (j0 = j) by eauto; subst.
        destruct (sd_initial_determ (HL j se) q s' s'0); eauto.
        intuition auto. constructor.
      + eelim sd_final_noext; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_final_noext; eauto.
      + edestruct (sd_final_determ (HL i se) s r r0); eauto.
        edestruct (sd_after_external_determ (HL j se) sk0 r s' s'0); eauto.
        intuition auto. constructor.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sd_traces; eauto.
    - destruct 1; inversion 1; subst. assert (i0 = i) by eauto; subst.
      edestruct (sd_initial_determ (HL i se) q s s0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_at_external_nostep; eauto.
      + edestruct (sd_at_external_determ (HL i se) s q q0); eauto.
        specialize (H0 j). congruence.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_after_external_determ (HL i se) s r s' s'0); eauto.
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

(** ** Simulation relation *)

Section FSIM.
  Context {li1 li2} (cc: callconv li1 li2).
  Context {I : Type}.
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
      inv H5; subst_dep. clear idx0.
      edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hsex & Hrx); eauto using fsim_lts.
      pose proof (fsim_lts (HL j) _ _ Hsex (Hse1 j)).
      edestruct @fsim_match_initial_states as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_push; eauto 1.
        erewrite <- match_valid_query; eauto. constructor. apply HL.
      + repeat (econstructor; eauto).
    - (* cross-component return *)
      inv H4; subst_dep. clear idx0.
      pose proof (fsim_lts (HL i) _ _ H3 H7).
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      inv H6. inv H8; subst_dep. edestruct H10 as (idx' & s2' & Hs2'& Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_pop; eauto.
      + repeat (econstructor; eauto).
  Qed.

  Lemma initial_states_simulation:
    forall q1 q2 s1, match_query cc w q1 q2 -> initial_state L1 se1 q1 s1 ->
    exists idx s2, initial_state L2 se2 q2 s2 /\ match_states idx s1 s2.
  Proof.
    intros q1 q2 _ Hq [i s1 Hs1].
    pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    exists (existT _ i idx), (st L2 i s2 :: nil).
    split; econstructor; eauto.
    erewrite <- match_valid_query; eauto. constructor; apply HL.
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
      intros j. erewrite <- match_valid_query; eauto.
      econstructor; eauto.
    + inv H2; subst_dep.
      edestruct H as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ i idx'), _.
      split; repeat (econstructor; eauto).
  Qed.

  Lemma semantics_simulation sk1 sk2:
    fsim_properties cc cc se1 se2 w
      (semantics' L1 sk1 se1)
      (semantics' L2 sk2 se2)
      index order match_states.
  Proof.
    split; cbn.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using step_simulation.
  Qed.
End FSIM.

(* Lemma inhabited_ind_dep {I: Type} {X: I -> Type} {P: Prop}: (forall i, X i -> P) -> (forall i, inhabited (X i)) -> P. *)
(* Proof. *)
(*   intros f Hf. *)
(* Admitted. *)

(* I believe the above induction principle is provable, so we don't really
   need the epsilon operator. Epsilon is more handy though *)
Require Import ClassicalEpsilon.

Section HCOMP_FSIM.

  Context {li1 li2} (cc: callconv li1 li2)
          {I} (L1: I -> Smallstep.semantics li1 li1)
          (L2: I -> Smallstep.semantics li2 li2).

  Hypothesis (H: forall i, forward_simulation cc cc (L1 i) (L2 i)).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk: forall i, linkorder (skel (L1 i)) sk).

  Lemma semantics_simulation':
    forward_simulation cc cc (semantics' L1 sk) (semantics' L2 sk).
  Proof.
    assert (HL: forall i, fsim_components cc cc (L1 i) (L2 i)).
    {
      intros i. specialize (H i).
      apply epsilon. auto. exact (fun _ => True).
    }
    constructor.
    eapply Forward_simulation with
        (order cc L1 L2 HL) (match_states cc L1 L2 HL).
    - reflexivity.
    - intros id.
      split; intros [i Hi]; exists i; rewrite (fsim_footprint (HL i)) in *; auto.
    - intros se1 se2 w Hse Hse1.
      eapply semantics_simulation; eauto.
      intros; eapply Genv.valid_for_linkorder; eauto.
    - clear - HL. intros [i x].
      induction (fsim_order_wf (HL i) x) as [x Hx IHx].
      constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
  Qed.

End HCOMP_FSIM.

(** * Linking operator *)

Local Unset Program Cases.

Definition semantics {li} := @semantics' bool li.

Definition compose {li} (La Lb: Smallstep.semantics li li) :=
  let L i := match i with true => La | false => Lb end in
  option_map (semantics L) (link (skel La) (skel Lb)).

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
  replace sk2 with sk1.
  apply semantics_simulation'.
  - intros [|]; constructor; auto.
  - intros [|]; pose proof (link_linkorder _ _ _ Hsk1) as [ ]; auto.
  - destruct Ha, Hb. congruence.
Qed.

Section LEVEL.

  Context {I: Type} {J: I -> Type}.
  Context {li} (L: forall i, J i -> Smallstep.semantics li li).

  Variable (sk: AST.program unit unit).
  Variable (ski: I -> AST.program unit unit).

  Let S1' i := (fun j => L i j).
  Let S1 := (fun i => semantics' (S1' i) (ski i)).
  Let S2 := (fun p => L (projT1 p) (projT2 p)).

  Let L1 := semantics' S1 sk.
  Let L2 := semantics' S2 sk.

  Inductive match_levels: state L1 -> state L2 -> Prop :=
  | match_nil: match_levels nil nil
  | match_i i j s k1 k2:
      match_levels k1 k2 ->
      match_levels (st S1 i (st (S1' i) j s :: nil) :: k1) (st S2 (existT _ i j) s :: k2)
  | match_j i j s k ks k1 k2:
      match_levels (st S1 i (k :: ks) :: k1) k2 ->
      match_levels (st S1 i (st (S1' i) j s :: k :: ks) :: k1)
                   (st S2 (existT _ i j) s :: k2).
  Hint Constructors match_levels.
  Hint Constructors initial_state final_state at_external after_external.

  Lemma level_simulation1: forward_simulation 1 1 L1 L2.
  Proof.
    constructor. econstructor. reflexivity.
    - intros x. cbn. split.
      + intros [i [j H]]. exists (existT _ i j). apply H.
      + intros [ij H]. exists (projT1 ij), (projT2 ij). apply H.
    - intros se ? [ ] [ ] Hse.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      eapply forward_simulation_step
        with (match_states := match_levels).
      + intros q ? s1 [ ] H. inv H. inv H1. cbn in *.
        exists (st S2 (existT _ i i0) s0 :: nil). split; auto.
      + intros s1 s2 r Hs Hr. inv Hr. inv H.
        inv Hs. subst_dep. inv H5.
        exists r. split; constructor; auto.
      + intros s1 s2 q Hs Hq. inv Hq. inv H.
        inv Hs; subst_dep.
        * exists tt, q. repeat apply conj; try constructor; auto.
          -- intros [ix jx]. unfold S1', S1, S2 in *; cbn in *.
             specialize (H0 ix). intros Hx. apply H0. firstorder.
          -- intros r ? s1' [ ] Hr. inv Hr. inv H7.
             subst_dep. inv H4. subst_dep.
             eexists. split; constructor; eauto.
        * exists tt, q. repeat apply conj; try constructor; auto.
          -- intros [ix jx]. unfold S1', S1, S2 in *; cbn in *.
             specialize (H0 ix). intros Hx. apply H0. firstorder.
          -- intros r ? s1' [ ] Hr. inv Hr. inv H7.
             subst_dep. inv H4. subst_dep.
             eexists. split; constructor; eauto.
      + intros s1 t s1' Hstep s2 Hs. inv Hstep.
        (* Internal step of L i *)
        * inv H.
          (* Internal step of L i j *)
          -- inv Hs; subst_dep; eexists.
             ++ split; [ apply step_internal | econstructor ]; eauto.
             ++ split; [ apply step_internal | econstructor ]; eauto.
          (* L i j calls into L i j' *)
          -- inv Hs; subst_dep; eexists.
             ++ split; [ eapply step_push | ]; eauto; auto.
             ++ split; [ eapply step_push | ]; eauto; auto.
          (* L i j returns to L i j' *)
          -- inv Hs. subst_dep. inv H8; subst_dep; eexists.
             ++ split; [ eapply step_pop | ]; eauto.
             ++ split; [ eapply step_pop | ]; eauto.
        (* L i j calls into L i' j' *)
        * inv H. inv H1. inv Hs; subst_dep; eexists.
          -- split; [ eapply step_push | ]; eauto; auto.
          -- split; [ eapply step_push | ]; eauto; auto.
        (* L i j return to L i' j' *)
        * inv H. inv H0. inv Hs; subst_dep. inv H6; subst_dep; eexists.
          -- split; [ eapply step_pop | ]; eauto.
          -- split; [ eapply step_pop | ]; eauto.
    - apply well_founded_ltof.
  Qed.

  Lemma foo: forall i j s t, st S2 (existT J i j) s = st S2 (existT J i j) t -> s = t.
  Proof.
    intros. inv H. subst_dep. auto.
  Qed.

  Hypothesis I_dec: forall (ix iy: I), {ix = iy} + {ix <> iy}.

  Hypothesis valid_query_excl:
    forall i i' j j' se q,
      valid_query (li := li) (L i j) se q -> valid_query (L i' j') se q ->
      existT _ i j = existT _ i' j'.

  (* FIXME: clean up the proof *)
  Lemma level_simulation2: forward_simulation 1 1 L2 L1.
  Proof.
    constructor. econstructor. reflexivity.
    - intros x. cbn. split.
      + intros [ij H]. exists (projT1 ij), (projT2 ij). apply H.
      + intros [i [j H]]. exists (existT _ i j). apply H.
    - intros se ? [ ] [ ] Hse.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      eapply forward_simulation_step
        with (match_states := fun s1 s2 => match_levels s2 s1).
      + intros q ? s1 [ ] H. inv H.
        destruct i as [i j]. eexists. split.
        * constructor. instantiate (1 := i). firstorder.
          constructor. instantiate (1 := j). firstorder.
          eauto.
        * auto.
      + intros s1 s2 r Hs Hr. inv Hr.
        remember (st S2 i s :: nil) as xs. inv Hs.
        * inv H1.
        * remember (st S2 (existT J i0 j) s0) as x.
          remember (st S2 i s) as y. inv H2.
          inversion H3. subst. apply foo in H3. subst.
          eexists. split; [ | constructor ].
          inv H0. constructor. constructor. auto.
        * inv H2. inv H0.
      + intros s1 s2 q Hs H. inv H.
        remember (st S2 i s :: k) as xs. inversion Hs.
        * subst. inv H2.
        * subst. remember (st S2 (existT J i0 j) s0) as x.
          remember (st S2 i s) as y. inv H3.
          inversion H4. subst. apply foo in H4. subst.
          exists tt, q. repeat apply conj; try constructor.
          -- constructor. auto. intros j0.
             specialize (H1 (existT _ i0 j0)). firstorder.
          -- intros ix. intros Hx. firstorder.
             specialize (H1 (existT _ ix x0)).
             apply H1. firstorder.
          -- intros r ? s1' [ ] Hr. inv Hr.
             subst_dep. eexists; split.
             ++ constructor. constructor. eauto.
             ++ constructor. auto.
        * subst. remember (st S2 (existT J i0 j) s0) as x.
          remember (st S2 i s) as y. inv H3.
          inversion H4. subst. apply foo in H4. subst.
          exists tt, q. repeat apply conj; try constructor.
          -- constructor. auto. intros j0.
             specialize (H1 (existT _ i0 j0)). firstorder.
          -- intros ix. intros Hx. firstorder.
             specialize (H1 (existT _ ix x0)).
             apply H1. firstorder.
          -- intros r ? s1' [ ] Hr. inv Hr.
             subst_dep. eexists; split.
             ++ constructor. constructor. eauto.
             ++ constructor. auto.
      + intros s1 t s1' Hstep s2 Hs. inv Hstep.
        (* internal step *)
        * remember (st S2 i s :: k) as xs. inversion Hs.
          -- subst. inv H1.
          -- subst. remember (st S2 (existT J i0 j) s0) as x.
             remember (st S2 i s) as y. inv H2.
             inversion H3. subst. apply foo in H3. subst.
             eexists. split.
             ++ apply step_internal. apply step_internal. eauto.
             ++ constructor. auto.
          -- subst. remember (st S2 (existT J i0 j) s0) as x.
             remember (st S2 i s) as y. inv H2.
             inversion H3. subst. apply foo in H3. subst.
             eexists. split.
             ++ apply step_internal. apply step_internal. eauto.
             ++ constructor. auto.
        (* function call *)
        * remember (st S2 i s :: k) as xs. inversion Hs.
          -- subst. inv H3.
          -- subst. remember (st S2 (existT J i0 j0) s0) as x.
             remember (st S2 i s) as y. inv H4.
             inversion H5. subst. apply foo in H5. subst.
             destruct j as [i j]. destruct (I_dec i i0).
             ++ subst. eexists. split.
                apply step_internal. eapply step_push; eauto. auto.
             ++ eexists. split.
                eapply step_push. econstructor. apply H.
                intros j1 Hx. apply n.
                exploit valid_query_excl. apply H0. apply Hx.
                apply eq_sigT_fst.
                instantiate (1 := i). firstorder.
                constructor. apply H0. eauto. auto.
          -- subst. remember (st S2 (existT J i0 j0) s0) as x.
             remember (st S2 i s) as y. inv H4.
             inversion H5. subst. apply foo in H5. subst.
             destruct j as [i j]. destruct (I_dec i i0).
             ++ subst. eexists. split.
                apply step_internal. eapply step_push; eauto. auto.
             ++ eexists. split.
                eapply step_push. econstructor. apply H.
                intros j1 Hx. apply n.
                exploit valid_query_excl. apply H0. apply Hx.
                apply eq_sigT_fst.
                instantiate (1 := i). firstorder.
                constructor. apply H0. eauto. auto.
        (* function return *)
        * remember (st S2 i s :: st S2 j sk0 :: k) as xs.
          inversion Hs; subst.
          -- inv H2.
          -- remember (st S2 (existT J i0 j0) s0) as x.
             remember (st S2 i s) as y. inv H3.
             inversion H4. subst. apply foo in H4. subst.

             remember (st S2 j sk0) as xs. inversion H1; subst.
             ++ inversion H2. subst. apply foo in H2. subst.
                eexists. split.
                eapply step_pop. constructor. eauto.
                constructor. eauto. auto.
             ++ inversion H2. subst. apply foo in H2. subst.
                eexists. split.
                eapply step_pop. constructor. eauto.
                constructor. eauto. auto.
          -- remember (st S2 (existT J i0 j0) s0) as x.
             remember (st S2 i s) as y. inv H3.
             inversion H4. subst. apply foo in H4. subst.

             remember (st S2 j sk0) as xs. inv H1.
             ++ inversion H7. subst. apply foo in H7.
                subst_dep. eexists. split.
                eapply step_internal. eapply step_pop.
                eauto. eauto. auto.
             ++ inversion H7. subst. apply foo in H7.
                subst_dep. eexists. split.
                eapply step_internal. eapply step_pop.
                eauto. eauto. auto.
    - apply well_founded_ltof.
  Qed.

End LEVEL.

Require Import Coq.Logic.FinFun.

Lemma bij_surj {A B} (f: A -> B): Bijective f -> Surjective f.
Proof.
  intros [g [H1 H2]] b. exists (g b). easy.
Qed.

Lemma bij_inj {A B} (f: A -> B): Bijective f -> Injective f.
Proof.
  intros [g [H1 H2]] x y H.
  rewrite <- (H1 x).
  rewrite <- (H1 y). congruence.
Qed.

Section MAP.

  Context {I li} (L: I -> Smallstep.semantics li li).
  Context {J} {F: J -> I} (HF: Bijective F).
  Variable (sk: AST.program unit unit).

  Let LF := semantics' (fun i => L (F i)) sk.

  Inductive match_bijection: state (semantics' L sk) -> state LF -> Prop :=
  | match_bijection_cons i j s s' k k':
      @existT I (fun i => state (L i)) i s = @existT I (fun i => state (L i)) (F j) s' ->
      match_bijection k k' ->
      match_bijection (st L i s :: k) (st (fun i => L (F i)) j s'  :: k')
  | match_bijection_nils: match_bijection nil nil.

  Hint Constructors match_bijection.

  Definition switch_index {i j} (H: i = F j) (s: state (L i)): state (L (F j)).
  Proof.
    rewrite <- H. exact s.
  Defined.

  Lemma bijective_map_simulation1: forward_simulation 1 1 (semantics' L sk) LF.
  Proof.
    constructor. econstructor. reflexivity.
    - intros id. split; intros [i Hi].
      + apply bij_surj in HF.
        specialize (HF i) as [x Hx].
        exists x. congruence.
      + exists (F i). auto.
    - intros se ? [ ] [ ] Hse.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      apply bij_surj in HF.
      eapply forward_simulation_step with (match_states := match_bijection).
      + intros q ? s [ ] H. inv H.
        specialize (HF i) as [j Hj]. subst.
        eexists; split; constructor; eauto.
      + intros s1 s2 r Hs H. inv H. inv Hs. inv H5.
        inv H4. subst_dep. exists r. split; constructor; auto.
      + intros s1 s2 q Hs H. inv H. inv Hs. inv H5.
        subst_dep. exists tt, q. repeat apply conj; try constructor; auto.
        intros r ? s1' [ ] H. inv H. subst_dep.
        eexists. split; constructor; eauto.
      + intros s1 t s1' Hstep s2 Hs. inv Hstep; inv Hs.
        * inv H4. subst_dep. eexists; split.
          eapply step_internal; eauto.
          constructor; eauto.
        * specialize (HF j) as [x Hx]. subst.
          inv H6. subst_dep. eexists. split.
          eapply step_push; eauto. auto.
        * inv H5. subst_dep. inv H6. inv H5. subst_dep.
          eexists. split. eapply step_pop; eauto. auto.
    - apply well_founded_ltof.
  Qed.

  Lemma bijective_map_simulation2: forward_simulation 1 1 LF (semantics' L sk).
  Proof.
    constructor. econstructor. reflexivity.
    - intros id. split; intros [i Hi].
      + exists (F i). auto.
      + apply bij_surj in HF.
        specialize (HF i) as [x Hx].
        exists x. congruence.
    - intros se ? [ ] [ ] Hse.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      eapply forward_simulation_step
        with (match_states := fun s1 s2 => match_bijection s2 s1).
      + intros q ? s [ ] H. inv H.
        eexists; split; constructor; eauto.
      + intros s1 s2 r Hs H. inv H. inv Hs.
        inv H3. subst_dep. inv H5.
        eexists; split; constructor; auto.
      + intros s1 s2 q Hs H. inv H.
        inv Hs. inv H4. subst_dep.
        exists tt, q. repeat apply conj; try constructor; auto.
        * intros j. apply bij_surj in HF.
          specialize (HF j) as [x <-]. easy.
        * intros r ? s1' [ ] H. inv H. subst_dep.
          eexists; split; constructor; auto. auto.
      + intros s1 t s1' Hstep s2 Hs. inv Hstep; inv Hs.
        * inv H3. subst_dep. eexists; split.
          apply step_internal; eauto. auto.
        * inv H5. subst_dep. eexists; split.
          eapply step_push; eauto. auto.
        * inv H4. subst_dep. inv H6. inv H4. subst_dep.
          eexists; split.
          eapply step_pop; eauto. auto.
    - apply well_founded_ltof.
  Qed.

End MAP.
