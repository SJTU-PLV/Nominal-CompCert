Require Import Relations.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface.
Require Import Events.
Require Import Globalenvs.
Require Import SmallstepLinking.
Require Import Smallstep_.
Require Import Integers.
Require Import Linking.
Require Import AST.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Section COMP.
  Context {liA liB liC} (Lsem1: semantics liB liC) (Lsem2: semantics liA liB).
  Context (se: Genv.symtbl) (qset: ident -> Prop).
  Let L1 := Lsem1 se.
  Let Li1 := Lsem1 se qset.
  Let L2 := Lsem2 se.
  Let Li2 := Lsem2 se (fun i => footprint L1 i \/ qset i).

  Definition valid_query' {li} (q: query li): Prop :=
    exists i, qset i /\ Genv.symbol_address se i Ptrofs.zero = entry q.

  Variant comp_state :=
  | st1 (s: state Lsem1) | st2 (s1: state Lsem1) (s2: state Lsem2).

  Inductive comp_step: comp_state -> trace -> comp_state -> Prop :=
  | step1 s1 t s1':
      Step Li1 s1 t s1' ->
      comp_step (st1 s1) t (st1 s1')
  | step2 s1 s2 t s2':
      Step Li2 s2 t s2' ->
      comp_step (st2 s1 s2) t (st2 s1 s2')
  | step_push s1 q s2:
      at_external L1 s1 q ->
      initial_state L2 q s2 ->
      not (valid_query L1 se q) ->
      not (valid_query' q) ->
      comp_step (st1 s1) E0 (st2 s1 s2)
  | step_pop s1 r s2 s1':
      final_state L2 s2 r ->
      after_external L1 s1 r s1' ->
      comp_step (st2 s1 s2) E0 (st1 s1').

  Inductive comp_initial_state (q: query liC): comp_state -> Prop :=
  | comp_initial_state_intro s:
      initial_state L1 q s ->
      comp_initial_state q (st1 s).

  Inductive comp_at_external: comp_state -> query liA -> Prop :=
  | comp_at_external_intro s1 s2 (q: query liA):
      not (valid_query L1 se q) ->
      not (valid_query L2 se q) ->
      at_external L2 s2 q ->
      comp_at_external (st2 s1 s2) q.

  Inductive comp_after_external: comp_state -> reply liA -> comp_state -> Prop :=
  | comp_after_external_intro s1 s2 r s2':
      after_external L2 s2 r s2' ->
      comp_after_external (st2 s1 s2) r (st2 s1 s2').

  Inductive comp_final_state: comp_state -> reply liC -> Prop :=
  | comp_final_state_intro s r:
      final_state L1 s r ->
      comp_final_state (st1 s) r.

  Definition comp_lts_internal :=
    {|
    step ge := comp_step;
    globalenv := tt;
    |}.
  Definition comp_lts_external :=
    {|
    footprint i := footprint L1 i \/ footprint L2 i;
    initial_state := comp_initial_state;
    at_external := comp_at_external;
    after_external := comp_after_external;
    final_state := comp_final_state;
    |}.
End COMP.

Definition comp_semantics' {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB) sk: semantics liA liC :=
  {|
  activate se :=
    {|
      steps p := comp_lts_internal L1 L2 se p;
      events := comp_lts_external L1 L2 se;
    |};
    skel := sk;
  |}.

Definition comp_semantics {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB): option (semantics liA liC) :=
  option_map (comp_semantics' L1 L2) (link (skel L1) (skel L2)).

(* Section ID. *)
(*   Context {li: language_interface}. *)
(*   Variant id_state := *)
(*   | st_q (q: query li) *)
(*   | st_r (r: reply li). *)

(*   Inductive id_step: id_state -> trace -> id_state -> Prop := . *)

(*   Inductive id_initial_state: query li -> id_state -> Prop := *)
(*   | id_initial_state_intro q: *)
(*       id_initial_state q (st_q q). *)

(*   Inductive id_at_external: id_state -> query li -> Prop := *)
(*   | id_at_external_intro q: *)
(*       id_at_external (st_q q) q. *)

(*   Inductive id_after_external: id_state -> reply li -> id_state -> Prop := *)
(*   | id_after_external_intro q r: *)
(*       id_after_external (st_q q) r (st_r r). *)

(*   Inductive id_final_state: id_state -> reply li -> Prop := *)
(*   | id_final_state_intro r: *)
(*       id_final_state (st_r r) r. *)

(*   Definition id_lts := *)
(*     {| *)
(*     step ge := id_step; *)
(*     footprint q := False; *)
(*     initial_state := id_initial_state; *)
(*     at_external := id_at_external; *)
(*     after_external := id_after_external; *)
(*     final_state := id_final_state; *)
(*     globalenv := tt; *)
(*     |}. *)
(* End ID. *)

(* Definition id_semantics {li} sk: semantics li li := *)
(*   {| *)
(*   activate se qset := id_lts; *)
(*   skel := sk; *)
(*   |}. *)


(* Definition fsim_lts {liA liB S1 S2} (L1: lts liA liB S1) (L2: lts liA liB S2) := *)
(*   exists index order ms, forall se,fsim_properties 1 1 se se tt L1 L2 index order ms. *)
(* Definition equiv_lts {liA liB S1 S2} (L1: lts liA liB S1) (L2: lts liA liB S2) := *)
(*   fsim_lts L1 L2 /\ fsim_lts L2 L1. *)

(* Lemma fsim_lts_trivial_order {liA liB S1 S2} (L1: lts liA liB S1) (L2: lts liA liB S2): *)
(*   (exists ms, forall se, fsim_properties 1 1 se se tt L1 L2 S1 (ltof _ (fun _ => O)) ms) -> fsim_lts L1 L2. *)
(* Proof. *)
(*   intros H. exists S1, (ltof _ (fun _ => O)). apply H. *)
(* Qed. *)

(* Definition forward_simulation' {liA liB} (L1 L2: semantics liA liB) := *)
(*   forward_simulation 1 1 L1 L2. *)
(* Definition equiv_simulation {liA liB} (L1 L2: semantics liA liB) := *)
(*   forward_simulation' L1 L2 /\ forward_simulation' L2 L1. *)

Notation "L1 ≤ L2" :=  (forward_simulation 1 1 L1 L2)(at level 70): lts_scope.
Open Scope lts_scope.
Delimit Scope lts_scope with lts.

Definition equiv_simulation {liA liB} (L1 L2: semantics liA liB) :=
  L1 ≤ L2 /\ L2 ≤ L1.

Notation "L1 ≡ L2" :=  (equiv_simulation L1 L2)(at level 90): lts_scope.
Notation "L1 ∘ L2" :=  (comp_semantics L1 L2)(at level 40, left associativity): lts_scope.
(* Notation " 1 " :=  (id_semantics): lts_scope. *)

Section IDENTITY.
  Context {liA liB} (L : semantics liA liB).

  (* src q --initial_state--> ι1(ι1(q)) --step-->ι2(ι1(q),s)

     tgt q --------------initial_state----------> s

     There's no appropriate way to match the intermediate state in the source
     program with the target program states *)
  (* Lemma identity1: 1 ∘ L ≤ L. *)
  (* Admitted. *)

  (* src s ------------------final_state---------------> r

     tgt ι2(ι1(s)) ---step--> ι1(ι2(r)) --final_state--> r

     Similar issue with `final_state` being too strict *)
  (* Lemma identity2: L ≤ 1 ∘ L. *)
  (* Admitted. *)

  (* Theorem categorical_comp_left_identity: 1 ∘ L ≡ L. *)
  (* Admitted. *)
  (* Dually, the right identity law suffers from the same problem with
     `at_external` and `after_external` being too strict *)
  (* Theorem categorical_comp_right_identity: L ∘ 1 ≡ L. *)
  (* Admitted. *)

End IDENTITY.

Lemma qset_step {liA liB S} (L: lts liA liB S) p1 p2 s t s':
  Step (L p1) s t s' -> p1 = p2 -> Step (L p2) s t s'.
Proof.
  now intros H [ ].
Qed.

Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Axiom EquivThenEqual: prop_extensionality.

Section ASSOC.

  Context {liA liB liC liD} (L1: semantics liC liD)
          (L2: semantics liB liC) (L3: semantics liA liB).
  Context (sk1 sk2 sk: AST.program unit unit).

  Let L12 := comp_semantics' L1 L2 sk1.
  Let L23 := comp_semantics' L2 L3 sk2.
  Let L := comp_semantics' L12 L3 sk.
  Let L' := comp_semantics' L1 L23 sk.

  Arguments st1 {_ _ _}.
  Arguments st2 {_ _ _}.

  Inductive assoc_state_match: comp_state L1 L23 -> comp_state L12 L3 -> Prop :=
  | assoc_match1 s1: assoc_state_match
                       (st1 L1 L23 s1)
                       (st1 L12 L3 (st1 L1 L2 s1))
  | assoc_match2 s1 s2: assoc_state_match
                          (st2 L1 L23 s1 (st1 L2 L3 s2))
                          (st1 L12 L3 (st2 L1 L2 s1 s2))
  | assoc_match3 s1 s2 s3: assoc_state_match
                             (st2 L1 L23 s1 (st2 L2 L3 s2 s3))
                             (st2 L12 L3 (st2 L1 L2 s1 s2) s3).

  (* Lemma assoc1: L1 ∘ (L2 ∘ L3) ≤ L1 ∘ L2 ∘ L3. *)
  Lemma assoc1: L' ≤ L.
  Proof.
    constructor. econstructor. reflexivity.
    intros se _ [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step
      with (match_states := assoc_state_match); cbn.
    - intros. now rewrite or_assoc.
    - intros q _ s1 [ ] H. inv H.
      eexists. split; try repeat constructor; auto.
    - intros s1 s2 r Hs H. inv H. inv Hs.
      eexists. split; try repeat constructor; auto.
    - intros s1 s2 q Hs Hext. inv Hext. inv H1. inv Hs.
      eexists tt, _. repeat apply conj; try repeat constructor; auto.
      intros [i [[Hi1 | Hi2] ?]];
        [ apply H; eexists; split; eauto |
          apply H2; eexists; split; eauto ].
      intros r _ s1' [ ] Haft. inv Haft. inv H8.
      eexists. split; try repeat constructor; auto.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep.
      + inv Hs. eexists; split; try repeat constructor; auto.
      + inv H; inv Hs; eexists; (split; [ | constructor ]).
        * apply step1. now apply step2.
        * apply step2. eapply qset_step. eauto.
          apply functional_extensionality. intros x.
          apply EquivThenEqual.
          cbn. rewrite <- or_assoc. apply or_iff_compat_r.
          apply or_comm.
        * (* eapply step_push; try constructor; eauto. *)
          eapply step_push; eauto.
          constructor; auto.
          -- intros [x [? ?]]. apply H3. eexists; split; eauto.
          -- intros [x [[? | ?] ?]].
             apply H3. eexists; split; eauto.
             apply H2. eexists; split; eauto.
          -- intros [x [? ?]]. apply H3. eexists; split; eauto.
        * eapply step_pop; try constructor; eauto.
      + inv H0. eexists; split; [ | constructor ].
        inv Hs. constructor. eapply step_push; eauto.
      + inv H. eexists; split; [ | constructor].
        inv Hs. constructor. econstructor; eauto.
    - apply well_founded_ltof.
  Qed.

  (* Lemma assoc2: L1 ∘ L2 ∘ L3 ≤ L1 ∘ (L2 ∘ L3). *)
  Lemma assoc2: L ≤ L'.
  Proof.
    constructor. econstructor. reflexivity.
    intros se _ [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step
      with (match_states := fun s1 s2 => assoc_state_match s2 s1); cbn.
    - intros i. now rewrite or_assoc.
    - intros q _ s1 [ ] H. inv H. inv H0.
      eexists; split; constructor; auto.
    - intros s1 s2 r Hs H. inv H. inv H0. inv Hs.
      eexists; split; constructor; auto.
    - intros s1 s2 q Hs Hext. inv Hext. inv Hs.
      eexists tt, _. repeat apply conj; try repeat constructor; auto.
      + intros [x [? ?]]. apply H. eexists; split; eauto.
        left; auto.
      + intros [x [[|]]].
        apply H. eexists; split; eauto. right. auto.
        apply H0. eexists; split; eauto.
      + intros [x [? ?]].  apply H. eexists; split; eauto.
        right; auto.
      + intros r _ s1' [ ] Haft. inv Haft.
        eexists; split; repeat constructor; auto.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep.
      + inv H; inv Hs; eexists; (split; [ | constructor ]).
        * now apply step1.
        * apply step2. now apply step1.
        * eapply step_push; try constructor; eauto.
        * eapply step_pop; try constructor; eauto.
      + inv Hs. eexists; split; repeat constructor; auto.
        eapply qset_step. eauto.
        apply functional_extensionality. intros x.
        apply EquivThenEqual.
        cbn. rewrite <- or_assoc. apply or_iff_compat_r.
        apply or_comm.
      + inv H. inv Hs. eexists; split; constructor.
        eapply step_push; eauto.
        intros [x [[|]]].
        apply H3. eexists; split; eauto.
        apply H2. eexists; split; eauto.
      + inv H0. inv Hs. eexists; split; constructor.
        eapply step_pop; eauto.
    - apply well_founded_ltof.
  Qed.

  (* Theorem categorical_comp_assoc: L1 ∘ (L2 ∘ L3) ≡ L1 ∘ L2 ∘ L3. *)
  Theorem categorical_comp_assoc: L' ≡ L.
  Proof.
    split; [ exact assoc1 | exact assoc2 ].
  Qed.
End ASSOC.

Section FSIM.
  Context {liA1 liA2 liB1 liB2 liC1 liC2}
          (cc1: callconv liA1 liA2)
          (cc2: callconv liB1 liB2)
          (cc3: callconv liC1 liC2)
          (L1: semantics liB1 liC1) (L2: semantics liA1 liB1)
          (L1': semantics liB2 liC2) (L2': semantics liA2 liB2).
  Context (HL1: fsim_components cc2 cc3 L1 L1')
          (HL2: fsim_components cc1 cc2 L2 L2')
          (se1 se2: Genv.symtbl) (w : ccworld cc3) (qset: ident -> Prop)
          (Hse: match_senv cc3 w se1 se2)
          (Hse1: Genv.valid_for (skel L1) se1)
          (Hse2: Genv.valid_for (skel L1') se1).

  Variant index := | index1: fsim_index HL1 -> index
  | index2: fsim_index HL1 -> fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
  | order1 i1 i1': fsim_order HL1 i1 i1' ->
      order (index1 i1) (index1 i1')
  | order2 i1 i1' i2 i2': fsim_order HL2 i2 i2' ->
      order (index2 i1 i2) (index2 i1' i2').

  Inductive match_states: index -> comp_state L1 L2 -> comp_state L1' L2' -> Prop :=
  | match_st1 i1 s1 s1':
      fsim_match_states HL1 se1 se2 w i1 s1 s1' ->
      match_states (index1 i1) (st1 L1 L2 s1) (st1 L1' L2' s1')
  | match_st2 i1 i2 s1 s1' s2 s2' w':
      fsim_match_states HL1 se1 se2 w i1 s1 s1' ->
      fsim_match_states HL2 se1 se2 w' i2 s2 s2' ->
      match_states (index2 i1 i2) (st2 L1 L2 s1 s2) (st2 L1' L2' s1' s2').

  Lemma comp_semantics_simulation sk sk':
    fsim_properties cc1 cc3 se1 se2 w qset
                    (comp_semantics' L1 L2 sk se1)
                    (comp_semantics' L1' L2' sk' se2)
                    index order match_states.
  Proof.
    split; cbn.
  Admitted.

End FSIM.

Section APPROX.
  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Context (sk: AST.program unit unit).



End APPROX.

Section CALL_CONV_REF.

  Context {li1 li2} {cc cc': LanguageInterface_.callconv li1 li2}
          (ref: ccref cc cc').

  Inductive cc_state_match (w: ccworld cc): @id_state li1 -> @id_state li2 -> Prop :=
  | cc_match_query q1 q2:
      match_query cc w q1 q2 ->
      cc_state_match w (st_q q1) (st_q q2)
  | cc_match_reply r1 r2:
      match_reply cc w r1 r2 ->
      cc_state_match w (st_r r1) (st_r r2).

  Lemma ccref_to_fsim:
    exists index order ms,
    forall w se1 se2, match_senv cc w se1 se2 ->
                 Smallstep_.fsim_properties cc' cc se1 se2 w 1 1 index order (ms w se1 se2).
  Proof.
    exists unit%type. exists (ltof _ (fun _ => O)).
    exists (fun w _ _ _ => cc_state_match w).
    intros w se1 se2 Hse. constructor.
    - intros q1 q2 Hq. now cbn.
    - intros q1 q2 s1 Hq Hs.
      inv Hs. exists tt. exists (st_q q2).
      split; econstructor; eauto.
    - intros _ s1 s2 r1 Hs Hr.
      inv Hr. inv Hs. exists r2. split. constructor. auto.
    - intros _ s1 s2 q1 Hs Hq. inv Hq. inv Hs.
      specialize (ref _ _ _ _ _ Hse H0).
      destruct ref as (w' & Hse' & Hq' & Hr).
      exists w'. exists q2. repeat apply conj; try constructor; auto.
      exact tt.
      inv H1. exists (st_r r2). split. constructor.
      constructor. apply Hr. auto.
    - intros. inv H.
  Qed.

End CALL_CONV_REF.
