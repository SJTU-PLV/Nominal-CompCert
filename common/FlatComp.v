Require Import Relations List Coqlib.
Require Import SmallstepLinking_.
Require Import AST LanguageInterface_ Events Globalenvs Smallstep_.
Require Import Linking.
Require Import CategoricalComp CallconvAlgebra_.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Axiom EquivThenEqual: prop_extensionality.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Section FLAT_COMP.
  Context {liA liB} (L1: semantics liA liB) (L2: semantics liA liB).
  Section WITH_SE.
    Context (se: Genv.symtbl) (qset: ident -> Prop).

    Variant flat_state :=
    | flat_st1 (s: state L1)
    | flat_st2 (s: state L2).

    Inductive flat_step: flat_state -> trace -> flat_state -> Prop :=
    | step1 s t s':
        Step (L1 se) s t s' -> flat_step (flat_st1 s) t (flat_st1 s')
    | step2 s t s':
        Step (L2 se) s t s' -> flat_step (flat_st2 s) t (flat_st2 s').

    Inductive flat_initial_state (q: query liB): flat_state -> Prop :=
    | initial_state1 s:
        initial_state (L1 se) q s ->
        flat_initial_state q (flat_st1 s)
    | initial_state2 s:
        initial_state (L2 se) q s ->
        flat_initial_state q (flat_st2 s).

    Inductive flat_at_external: flat_state -> query liA -> Prop :=
    | at_external1 s q:
        at_external (L1 se) s q ->
        flat_at_external (flat_st1 s) q
    | at_external2 s q:
        at_external (L2 se) s q ->
        flat_at_external (flat_st2 s) q.

    Inductive flat_after_external: flat_state -> reply liA -> flat_state -> Prop :=
    | after_external1 s r s':
        after_external (L1 se) s r s' ->
        flat_after_external (flat_st1 s) r (flat_st1 s')
    | after_external2 s r s':
        after_external (L2 se) s r s' ->
        flat_after_external (flat_st2 s) r (flat_st2 s').

    Inductive flat_final_state: flat_state -> reply liB -> Prop :=
    | final_state1 s r:
        final_state (L1 se) s r ->
        flat_final_state (flat_st1 s) r
    | final_state2 s r:
        final_state (L2 se) s r ->
        flat_final_state (flat_st2 s) r.

    Lemma star_internal1 s t s':
      Star (L1 se) s t s' ->
      star (fun _ => flat_step) tt (flat_st1 s) t (flat_st1 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal1 s t s':
      Plus (L1 se) s t s' ->
      plus (fun _ => flat_step) tt (flat_st1 s) t (flat_st1 s').
    Proof.
      destruct 1; econstructor; eauto using step1, star_internal1.
    Qed.

    Lemma star_internal2 s t s':
      Star (L2 se) s t s' ->
      star (fun _ => flat_step) tt (flat_st2 s) t (flat_st2 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal2 s t s':
      Plus (L2 se) s t s' ->
      plus (fun _ => flat_step) tt (flat_st2 s) t (flat_st2 s').
    Proof.
      destruct 1; econstructor; eauto using step2, star_internal2.
    Qed.

  End WITH_SE.

  Program Definition flat_comp_semantics' sk: semantics liA liB :=
    {|
      activate se :=
        {|
          Smallstep_.step ge:= flat_step se;
          Smallstep_.initial_state := flat_initial_state se;
          Smallstep_.at_external := flat_at_external se;
          Smallstep_.after_external := flat_after_external se;
          Smallstep_.final_state := flat_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint i := footprint L1 i \/ footprint L2 i;
    |}.

End FLAT_COMP.

Definition flat_comp_semantics {liA liB} (L1: semantics liA liB)
           (L2: semantics liA liB): option (semantics liA liB) :=
  option_map (flat_comp_semantics' L1 L2) (link (skel L1) (skel L2)).

Notation "L1 ⊎ L2" :=  (flat_comp_semantics L1 L2)(at level 40, left associativity): lts_scope.

Section FSIM.
  Context {liA1 liA2 liB1 liB2}
          (cc1: callconv liA1 liB1)
          (cc2: callconv liA2 liB2)
          (L1 L2: semantics liA1 liA2)
          (L1' L2': semantics liB1 liB2).
  Context (HL1: fsim_components cc1 cc2 L1 L1')
          (HL2: fsim_components cc1 cc2 L2 L2')
          (se1 se2: Genv.symtbl) (w : ccworld cc2)
          (Hse: match_senv cc2 w se1 se2)
          (Hse1: Genv.valid_for (skel L1) se1)
          (Hse2: Genv.valid_for (skel L2) se1).

  Variant index := | index1 (i: fsim_index HL1) | index2 (i: fsim_index HL2).
  Variant order: index -> index -> Prop :=
  | order1 i1 i1': fsim_order HL1 i1 i1' -> order (index1 i1) (index1 i1')
  | order2 i2 i2': fsim_order HL2 i2 i2' -> order (index2 i2) (index2 i2').

  Variant match_states: index -> flat_state L1 L2 -> flat_state L1' L2' -> Prop :=
  | match_st1 i s1 s1':
      fsim_match_states HL1 se1 se2 w i s1 s1' ->
      match_states (index1 i) (flat_st1 L1 L2 s1) (flat_st1 L1' L2' s1')
  | match_st2 i s2 s2':
      fsim_match_states HL2 se1 se2 w i s2 s2' ->
      match_states (index2 i) (flat_st2 L1 L2 s2) (flat_st2 L1' L2' s2').

  Local Lemma flat_compose_simulation' sk sk':
    fsim_properties cc1 cc2 se1 se2 w
                    (flat_comp_semantics' L1 L2 sk se1)
                    (flat_comp_semantics' L1' L2' sk' se2)
                    index order match_states.
  Proof.
    split; cbn.
    - intros q1 q2 s1 Hq H.
      inv H;
        [ pose proof (fsim_lts HL1 _ _ Hse Hse1)
        | pose proof (fsim_lts HL2 _ _ Hse Hse2)
        ];
        edestruct @fsim_match_initial_states as (idx & s' & Hs' & Hs);
        eauto; eexists _, _; split; econstructor; eauto.
    - intros i s1 s2 r1 Hs H.
      inv H; inv Hs;
        [ pose proof (fsim_lts HL1 _ _ Hse Hse1)
        | pose proof (fsim_lts HL2 _ _ Hse Hse2)
        ];
        edestruct @fsim_match_final_states as (r' & H' & Hr');
        eauto; eexists; split; try econstructor; eauto.
    - intros i s1 s2 q1 Hs H.
      inv H; inv Hs;
        [ pose proof (fsim_lts HL1 _ _ Hse Hse1)
        | pose proof (fsim_lts HL2 _ _ Hse Hse2)
        ];
        edestruct @fsim_match_external as (w1 & q' & H' & Hq' & Hse' & HH);
        eauto; eexists _, _; repeat apply conj; eauto.
      + constructor; auto.
      + intros r1 r2 fs Hr Haft. inv Haft.
        exploit HH; eauto. intros (? & ? & ? & ?).
        eexists _, _; split; econstructor; eauto.
      + constructor; auto.
      + intros r1 r2 fs Hr Haft. inv Haft.
        exploit HH; eauto. intros (? & ? & ? & ?).
        eexists _, _; split; econstructor; eauto.
    - intros s1 t s1' Hstep i s2 Hs.
      inv Hstep; inv Hs;
        [ pose proof (fsim_lts HL1 _ _ Hse Hse1)
        | pose proof (fsim_lts HL2 _ _ Hse Hse2)
        ];
        edestruct @fsim_simulation as (idx' & ? & Hs2' & Hs');
        eauto.
      + eexists _, _; split.
        * destruct Hs2'; [left | right].
          -- apply plus_internal1. eauto.
          -- destruct a; split; [ | constructor ]; eauto.
             apply star_internal1. eauto.
        * now constructor.
      + eexists _, _; split.
        * destruct Hs2'; [left | right].
          -- apply plus_internal2. eauto.
          -- destruct a; split; [ | constructor ]; eauto.
             apply star_internal2. eauto.
        * now constructor.
  Qed.

End FSIM.

Lemma flat_compose_simulation
      {liA1 liA2 liB1 liB2}
      (cc1: callconv liA1 liB1) (cc2: callconv liA2 liB2)
      L1 L2 L1' L2' L L':
  forward_simulation cc1 cc2 L1 L1' ->
  forward_simulation cc1 cc2 L2 L2' ->
  L1 ⊎ L2 = Some L -> L1' ⊎ L2' = Some L' ->
  forward_simulation cc1 cc2 L L'.
Proof.
  unfold flat_comp_semantics. unfold option_map.  intros [HL1] [HL2] H1 H2.
  destruct (link (skel L1) (skel L2)) as [sk1|] eqn:Hsk1; try discriminate.
  inv H1.
  destruct (link (skel L1') (skel L2')) as [sk2|] eqn:Hsk2; try discriminate.
  inv H2.
  constructor.
  eapply Forward_simulation
    with (order cc1 cc2 L1 L2 L1' L2' HL1 HL2)
         (match_states cc1 cc2 L1 L2 L1' L2' HL1 HL2).
  - cbn. destruct HL1, HL2. congruence.
  - cbn. intros i. destruct HL1, HL2.
    rewrite fsim_footprint, fsim_footprint0. reflexivity.
  - intros se1 se2 w Hse Hse1.
    pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
    eapply flat_compose_simulation'; eauto.
    eapply Genv.valid_for_linkorder; eauto.
    eapply Genv.valid_for_linkorder; eauto.
  - clear - HL1 HL2. intros [|].
    + induction (fsim_order_wf HL1 i). constructor.
      intros. inv H1. apply H0. auto.
    + induction (fsim_order_wf HL2 i). constructor.
      intros. inv H1. apply H0. auto.
Qed.

Section APPROX.

  Context {li} (L1 L2: semantics li li).
  Context (sk: AST.program unit unit).

  Let L := fun i => match i with true => L1 | false => L2 end.

  Inductive match_frame: flat_state L1 L2 -> list (SmallstepLinking_.frame L) -> Prop :=
  | match_frame1 s:
      match_frame (flat_st1 L1 L2 s) (st L true s :: nil)
  | match_frame2 s:
      match_frame (flat_st2 L1 L2 s) (st L false s :: nil).

  Hypothesis flat_linking1:
    forall se s q, at_external (L2 se) s q -> ~ valid_query L1 se q.
  Hypothesis flat_linking2:
    forall se s q, at_external (L1 se) s q -> ~ valid_query L2 se q.
  Hypothesis extcall_invalid:
    forall i se s q, Smallstep_.at_external (L i se) s q -> ~ valid_query (L i) se q.
  Hypothesis valid_initial_state:
    forall i se q s, initial_state (L i se) q s -> valid_query (L i) se q.
  (* Hypothesis flat_linking: *)
  (*   forall i j se q, valid_query (li := li) (L i) se q -> valid_query (L j) se q -> i = j. *)

  Lemma flat_composition_approximation:
    flat_comp_semantics' L1 L2 sk ≤ SmallstepLinking_.semantics L sk.
  Proof.
    constructor. econstructor; eauto.
    {
      intros. split.
      - intros [|]; [exists true | exists false]; eauto.
      - intros [[|] ?]; [left | right]; eauto.
    }
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_frame).
    - intros q ? s1 [ ] Hs.
      inv Hs; eexists; split; econstructor; eauto.
    - intros s1 s2 r Hs H.
      inv H; inv Hs; eexists; split; econstructor; eauto.
    - intros s1 s2 q1 Hs H.
      inv H; inv Hs; eexists tt, _; repeat apply conj; try constructor; auto.
      + intros [|].
        eapply extcall_invalid. eauto.
        eapply flat_linking2. eauto.
      + intros r1 ? s1' [ ] H. inv H.
        eexists; split; constructor; auto.
      + intros [|].
        eapply flat_linking1. eauto.
        eapply extcall_invalid. eauto.
      + intros r1 ? s1' [ ] H. inv H.
        eexists; split; constructor; auto.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv Hs;
        eexists; (split; [ | econstructor]; constructor; auto).
    - apply well_founded_ltof.
  Qed.

End APPROX.

Section DIST.
  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liB liC)
          (L: semantics liA liB).
  Context (sk: AST.program unit unit).
  Let Lh := flat_comp_semantics' L1 L2 sk.
  Let Lv1 := comp_semantics' L1 L sk.
  Let Lv2 := comp_semantics' L2 L sk.

  Inductive dist_match_state:
    (comp_state Lh L) -> (flat_state Lv1 Lv2) -> Prop :=
  | dist_match_state1 s1:
      dist_match_state (st1 Lh _ (flat_st1 _ L2 s1))
                       (flat_st1 Lv1 _ (st1 _ L s1))
  | dist_match_state2 s2:
      dist_match_state (st1 Lh _ (flat_st2 L1 _ s2))
                       (flat_st2 _ Lv2 (st1 L2 _ s2))
  | dist_match_state3 s1 s:
      dist_match_state (st2 Lh L (flat_st1 L1 L2 s1) s)
                       (flat_st1 Lv1 Lv2 (st2 L1 L s1 s))
  | dist_match_state4 s2 s:
      dist_match_state (st2 Lh L (flat_st2 L1 L2 s2) s)
                       (flat_st2 Lv1 Lv2 (st2 L2 L s2 s)).

  Ltac esca := eexists; split; repeat constructor; auto.

  (* (L1 ⊎ L2) ∘ L ≤ (L1 ∘ L) ⊎ (L2 ∘ L) *)
  Lemma distributivity1:
    comp_semantics' Lh L sk ≤ flat_comp_semantics' Lv1 Lv2 sk.
  Proof.
    constructor. econstructor; eauto. intros i. firstorder.
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := dist_match_state).
    - intros q1 ? s1 [ ] H.
      inv H; inv H0; eexists; split; constructor; auto.
      (* + destruct H as [? [? [? ?]]]. split; auto. *)
      (*   eexists; split; eauto. apply or_introl; auto. *)
      + now constructor.
      (* + destruct H as [? [? [? ?]]]. split; auto. *)
      (*   eexists; split; eauto. apply or_introl; auto. *)
      + now constructor.
    - intros s1 s2 r1 Hs H.
      inv H; inv H0; inv Hs; esca.
    - intros s1 s2 q1 Hs H.
      inv H; inv Hs; eexists tt, _; repeat apply conj; try constructor; auto.
      + constructor; auto.
      + intros r1 ? s1' [ ] H. inv H. esca.
      + constructor; auto.
      + intros r1 ? s1' [ ] H. inv H. esca.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv Hs.
      + inv H. esca.
      + inv H. esca.
      + esca.
      + esca.
      + inv H. eexists; split. constructor. eapply step_push; eauto.
        constructor.
      + inv H. eexists; split. constructor. eapply step_push; eauto.
        constructor.
      + inv H0. eexists; split. constructor. eapply step_pop; eauto.
        constructor.
      + inv H0. eexists; split. constructor. eapply step_pop; eauto.
        constructor.
    - apply well_founded_ltof.
  Qed.

  (* (* This is required because L1 ∘ L2 doesn't use valid_query to ensure the *) *)
  (* (*    query invokes execution is within the footprint. Otherwise, the identity *) *)
  (* (*    transition would be meaningless *) *)
  (* Hypothesis init_state_valid1: *)
  (*   forall se q s, initial_state (L1 se) q s -> valid_query L1 se q. *)
  (* Hypothesis init_state_valid2: *)
  (*   forall se q s, initial_state (L2 se) q s -> valid_query L2 se q. *)

  Ltac esca' := eexists; split; [ | constructor]; repeat constructor; auto.
  (* (L1 ∘ L) ⊎ (L2 ∘ L) ≤ (L1 ⊎ L2) ∘ L *)
  Lemma distributivity2:
    flat_comp_semantics' Lv1 Lv2 sk ≤ comp_semantics' Lh L sk.
  Proof.
    constructor. econstructor; eauto. intros i. firstorder.
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with
        (match_states := fun s1 s2 => dist_match_state s2 s1).
    - intros q1 ? s1 [ ] H. inv H; inv H0; esca'.
    - intros s1 s2 r1 Hs H. inv H; inv H0; inv Hs; esca'.
    - intros s1 s2 q1 Hs H.
      inv H; inv H0; inv Hs; eexists tt, _; repeat apply conj;
        try constructor; auto.
      + intros r1 ? s1' [ ] Hx. inv Hx. inv H1; esca'.
      + intros r1 ? s1' [ ] Hx. inv Hx. inv H1; esca'.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv H; inv Hs.
      + esca'.
      + esca'.
      + eexists. split; [ | constructor ].
        eapply step_push; eauto; try constructor; auto; firstorder.
      + eexists. split; [ | constructor ].
        eapply step_pop; eauto; try constructor; auto; firstorder.
      + esca'.
      + esca'.
      + esca'.
        eapply step_push; eauto; try constructor; auto; firstorder.
      + esca'.
        eapply step_pop; eauto; try constructor; auto; firstorder.
    - apply well_founded_ltof.
  Qed.

  Theorem flat_categorical_comp_distributivity:
    flat_comp_semantics' Lv1 Lv2 sk ≡ comp_semantics' Lh L sk.
  Proof.
    split; [ exact distributivity2 | exact distributivity1 ].
  Qed.
End DIST.
