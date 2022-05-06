Require Import Relations List Coqlib.
Require Import SmallstepLinking.
Require Import AST LanguageInterface Events Globalenvs Smallstep.
Require Import Linking.
Require Import CategoricalComp CallconvAlgebra.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Axiom EquivThenEqual: prop_extensionality.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Section FLAT_COMP.
  Context {I liA liB} (L: I -> semantics liA liB).
  Section WITH_SE.
    Context (se: Genv.symtbl).

    Variant flat_state := flat_st i (s: state (L i)).

    Inductive flat_step: flat_state -> trace -> flat_state -> Prop :=
    | step_internal i s t s':
        Step (L i se) s t s' -> flat_step (flat_st i s) t (flat_st i s').

    Inductive flat_initial_state (q: query liB): flat_state -> Prop :=
    | initial_state_intro i s:
        initial_state (L i se) q s ->
        flat_initial_state q (flat_st i s).

    Inductive flat_at_external: flat_state -> query liA -> Prop :=
    | at_external_intro i s q:
        at_external (L i se) s q -> flat_at_external (flat_st i s) q.

    Inductive flat_after_external: flat_state -> reply liA -> flat_state -> Prop :=
    | after_external_intro i s r s':
        after_external (L i se) s r s' ->
        flat_after_external (flat_st i s) r (flat_st i s').

    Inductive flat_final_state: flat_state -> reply liB -> Prop :=
    | final_state1 i s r:
        final_state (L i se) s r -> flat_final_state (flat_st i s) r.

    Lemma star_internal i s t s':
      Star (L i se) s t s' ->
      star (fun _ => flat_step) tt (flat_st i s) t (flat_st i s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal i s t s':
      Plus (L i se) s t s' ->
      plus (fun _ => flat_step) tt (flat_st i s) t (flat_st i s').
    Proof.
      destruct 1; econstructor; eauto using step_internal, star_internal.
    Qed.

  End WITH_SE.

  Program Definition flat_comp_semantics' sk: semantics liA liB :=
    {|
      activate se :=
        {|
          Smallstep.step ge:= flat_step se;
          Smallstep.initial_state := flat_initial_state se;
          Smallstep.at_external := flat_at_external se;
          Smallstep.after_external := flat_after_external se;
          Smallstep.final_state := flat_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint x := exists i, footprint (L i) x;
    |}.

  (* The external call from (L i) cannot be in the footprint of (L j) for i ≠ j *)
  Class FlatLinkable :=
    flat_linking:
      forall i j se s q, at_external (L i se) s q -> valid_query (L j) se q -> i = j.

End FLAT_COMP.

Section FSIM.
  Context {I liA1 liA2 liB1 liB2}
          (cc1: callconv liA1 liA2)
          (cc2: callconv liB1 liB2)
          (L1: I -> semantics liA1 liB1)
          (L2: I -> semantics liA2 liB2).
  Context (HL: forall i, fsim_components cc1 cc2 (L1 i) (L2 i))
          (se1 se2: Genv.symtbl) (w : ccworld cc2)
          (Hse: match_senv cc2 w se1 se2)
          (Hse1: forall i, Genv.valid_for (skel (L1 i)) se1).

  Notation index := {i & fsim_index (HL i)}.
  Variant order: index -> index -> Prop :=
  | order_intro i x y: fsim_order (HL i) x y -> order (existT _ i x) (existT _ i y).

  Variant match_states: index -> flat_state L1 -> flat_state L2 -> Prop :=
  | match_flat_st i idx s1 s2:
      fsim_match_states (HL i) se1 se2 w idx s1 s2 ->
      match_states (existT _ i idx) (flat_st L1 i s1) (flat_st L2 i s2).

  Local Lemma flat_compose_simulation' sk sk':
    fsim_properties cc1 cc2 se1 se2 w
                    (flat_comp_semantics' L1 sk se1)
                    (flat_comp_semantics' L2 sk' se2)
                    index order match_states.
  Proof.
    split; cbn.
    - intros q1 q2 s1 Hq H.
      inv H; pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
      edestruct @fsim_match_initial_states as (idx & s' & Hs' & Hs);
        eauto; eexists _, _; split; econstructor; eauto.
    - intros idx s1 s2 r1 Hs H.
      inv H. inv Hs. subst_dep.
      pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
      edestruct @fsim_match_final_states as (r' & H' & Hr');
        eauto; eexists; split; try econstructor; eauto.
    - intros idx s1 s2 q1 Hs H.
      inv H. inv Hs. subst_dep.
      pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
      edestruct @fsim_match_external as (w1 & q' & H' & Hq' & Hse' & HH);
        eauto; eexists _, _; repeat apply conj; eauto.
      + constructor; auto.
      + intros r1 r2 fs Hr Haft. inv Haft. subst_dep.
        exploit HH; eauto. intros (? & ? & ? & ?).
        eexists _, _; split; econstructor; eauto.
    - intros s1 t s1' Hstep idx s2 Hs.
      inv Hstep. inv Hs. subst_dep.
      pose proof (fsim_lts (HL i) _ _ Hse (Hse1 i)).
      edestruct @fsim_simulation as (idx' & ? & Hs2' & Hs'); eauto.
      + eexists _, _; split.
        * destruct Hs2'; [left | right].
          -- apply plus_internal. eauto.
          -- destruct a; split; [ | constructor ]; eauto.
             apply star_internal. eauto.
        * now constructor.
  Qed.

End FSIM.

Require Import ClassicalEpsilon.

Section FLAT_FSIM.

  Context {I liA1 liA2 liB1 liB2}
          (cc1: callconv liA1 liA2)
          (cc2: callconv liB1 liB2)
          (L1: I -> semantics liA1 liB1)
          (L2: I -> semantics liA2 liB2).
  Hypothesis (H: forall i, forward_simulation cc1 cc2 (L1 i) (L2 i)).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk: forall i, linkorder (skel (L1 i)) sk).

  Lemma flat_composition_simulation':
    forward_simulation cc1 cc2 (flat_comp_semantics' L1 sk) (flat_comp_semantics' L2 sk).
  Proof.
    assert (HL: forall i, fsim_components cc1 cc2 (L1 i) (L2 i)).
    {
      intros i. specialize (H i).
      apply epsilon. auto. exact (fun _ => True).
    }
    constructor.
    eapply Forward_simulation
      with (order cc1 cc2 L1 L2 HL)
           (match_states cc1 cc2 L1 L2 HL); auto.
    - cbn. intros id.
      split; intros [i Hi]; exists i; rewrite (fsim_footprint (HL i)) in *; auto.
    - intros se1 se2 w Hse Hse1.
      eapply flat_compose_simulation'; eauto.
      intros; eapply Genv.valid_for_linkorder; eauto.
    - clear - HL. intros [i x].
      induction (fsim_order_wf (HL i) x) as [x Hx IHx].
      constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
  Qed.

End FLAT_FSIM.

Definition flat_comp_semantics {liA liB} (L1: semantics liA liB)
           (L2: semantics liA liB): option (semantics liA liB) :=
  let L i := match i with true => L1 | false => L2 end in
  option_map (flat_comp_semantics' L) (link (skel L1) (skel L2)).

Notation "L1 ⊎ L2" :=  (flat_comp_semantics L1 L2)(at level 40, left associativity): lts_scope.

Lemma flat_compose_simulation
      {liA1 liA2 liB1 liB2}
      (cc1: callconv liA1 liB1) (cc2: callconv liA2 liB2)
      L1a L2a L1b L2b L1 L2:
  forward_simulation cc1 cc2 L1a L2a ->
  forward_simulation cc1 cc2 L1b L2b ->
  L1a ⊎ L1b = Some L1 -> L2a ⊎ L2b = Some L2 ->
  forward_simulation cc1 cc2 L1 L2.
Proof.
  unfold flat_comp_semantics. unfold option_map.  intros [HL1] [HL2] H1 H2.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1;
    try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2;
    try discriminate. inv H2.
  replace sk2 with sk1.
  apply flat_composition_simulation'.
  - intros [|]; constructor; auto.
  - intros [|]; pose proof (link_linkorder _ _ _ Hsk1) as [? ?]; auto.
  - destruct HL1, HL2. congruence.
Qed.

Section APPROX.

  Context {I li} (L: I -> semantics li li).
  Context (sk: AST.program unit unit).
  Context {HP: forall i, ProgramSem (L i)}.
  Context `{!FlatLinkable L}.

  Hypothesis I_dec: forall (i j : I), {i = j} + {i <> j}.

  Inductive match_frame: flat_state L -> list (SmallstepLinking.frame L) -> Prop :=
  | match_frame_intro i s:
      match_frame (flat_st L i s) (st L i s :: nil).

  Lemma flat_composition_approximation:
    flat_comp_semantics' L sk ≤ SmallstepLinking.semantics' L sk.
  Proof.
    constructor. econstructor; eauto. intros. reflexivity.
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_frame).
    - intros q ? s1 [ ] Hs.
      inv Hs; eexists; split; econstructor; eauto.
      eapply incoming_query_valid; eauto.
    - intros s1 s2 r Hs H.
      inv H. inv Hs. subst_dep.
      eexists; split; econstructor; eauto.
    - intros s1 s2 q1 Hs H.
      inv H. inv Hs. subst_dep.
      eexists tt, _; repeat apply conj; try constructor; auto.
      + intros j. destruct (I_dec i j) eqn: HI.
        * subst. eapply outgoing_query_invalid. eauto.
        * intros X. apply n. eapply flat_linking; eauto.
      + intros r1 ? s1' [ ] H. inv H. subst_dep.
        eexists; split; constructor; auto.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep. inv Hs. subst_dep.
      eexists; (split; [ | econstructor]; constructor; auto).
    - apply well_founded_ltof.
  Qed.

End APPROX.

Section DIST.
  Context {I liA liB liC} (Li: I -> semantics liB liC) (L: semantics liA liB).
  Context (sk skh: AST.program unit unit) (skv: I -> AST.program unit unit).
  Let Lh := flat_comp_semantics' Li skh.
  Let Lv i := comp_semantics' (Li i) L (skv i).
  Hypothesis non_empty: inhabited I.

  (* (L1 ⊎ L2 ⊎ ... ) ∘ L ≅ (L1 ∘ L) ⊎ (L2 ∘ L) ⊎ ... *)
  Inductive dist_match_state: comp_state Lh L -> flat_state Lv -> Prop :=
  | dist_match_state1 i s:
      dist_match_state (st1 Lh _ (flat_st Li i s))
                       (flat_st Lv i (st1 _ L s))
  | dist_match_state2 i s1 s2:
      dist_match_state (st2 Lh L (flat_st Li i s1) s2)
                       (flat_st Lv i (st2 (Li i) L s1 s2)).

  Hint Constructors dist_match_state
       flat_initial_state flat_at_external
       flat_final_state flat_after_external
       comp_initial_state comp_at_external
       comp_after_external comp_final_state.

  Ltac esca := eexists; split; repeat constructor; auto.
  (* (L1 ⊎ L2) ∘ L ≤ (L1 ∘ L) ⊎ (L2 ∘ L) *)
  Lemma distributivity1:
    comp_semantics' Lh L sk ≤ flat_comp_semantics' Lv sk.
  Proof.
    constructor. econstructor; eauto. intros id. firstorder.
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := dist_match_state).
    - intros q1 ? s1 [ ] H.
      inv H. inv H0. eexists; split; auto.
      repeat constructor. auto.
    - intros s1 s2 r1 Hs H. inv H; inv H0; inv Hs. subst_dep. esca.
    - intros s1 s2 q1 Hs H.
      inv H. inv Hs.
      eexists tt, _; repeat apply conj; try constructor; auto.
      + constructor; auto.
      + intros r1 ? s1' [ ] H. inv H. esca.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv Hs.
      + inv H. subst_dep. esca.
      + esca.
      + inv H. subst_dep.
        eexists; split; auto. constructor. eapply step_push; eauto.
      + inv H0. subst_dep.
        eexists; split; auto. constructor. eapply step_pop; eauto.
    - apply well_founded_ltof.
  Qed.

  Ltac esca' := eexists; split; [ | constructor]; repeat constructor; auto.
  (* (L1 ∘ L) ⊎ (L2 ∘ L) ≤ (L1 ⊎ L2) ∘ L *)
  Lemma distributivity2:
    flat_comp_semantics' Lv sk ≤ comp_semantics' Lh L sk.
  Proof.
    constructor. econstructor; eauto. intros i. firstorder.
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with
        (match_states := fun s1 s2 => dist_match_state s2 s1).
    - intros q1 ? s1 [ ] H. inv H; inv H0; esca'.
    - intros s1 s2 r1 Hs H. inv H; inv H0; inv Hs; subst_dep; esca'.
    - intros s1 s2 q1 Hs H.
      inv H; inv H0; inv Hs; eexists tt, _; repeat apply conj;
        try constructor; auto. subst_dep.
      intros r1 ? s1' [ ] Hx. inv Hx.
      subst_dep. inv H4. esca'.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv H; inv Hs; subst_dep.
      + esca'.
      + esca'.
      + esca'. eapply step_push; eauto. now constructor.
      + esca'. eapply step_pop; eauto. now constructor.
    - apply well_founded_ltof.
  Qed.

  Theorem flat_categorical_comp_distributivity:
    flat_comp_semantics' Lv sk ≡ comp_semantics' Lh L sk.
  Proof.
    split; [ exact distributivity2 | exact distributivity1 ].
  Qed.
End DIST.
