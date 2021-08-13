Require Import Relations.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface_.
Require Import Events.
Require Import Globalenvs.
Require Import SmallstepLinking_.
Require Import Smallstep_.
Require Import Integers.
Require Import Linking.
Require Import AST.
Require Import CallconvAlgebra_.

Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Axiom EquivThenEqual: prop_extensionality.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Section COMP.
  Context {liA liB liC} (Lsem1: semantics liB liC) (Lsem2: semantics liA liB).
  Section WITH_SE.
    Context (se: Genv.symtbl) (qset: ident -> Prop).
    Let L1 := Lsem1 se.
    Let L2 := Lsem2 se.
    Let qset1 := qset.
    (* The query set passed to L2 *)
    Let qset2 := (fun i => footprint Lsem1 i \/ qset i).

    (* Whether the query is permitted by the inherited footprint *)
    Definition valid_query_inh {li} (q: query li): Prop :=
      entry q <> Values.Vundef /\
      exists i, qset i /\ Genv.symbol_address se i Ptrofs.zero = entry q.

    Variant comp_state :=
    | st1 (s: state Lsem1) | st2 (s1: state Lsem1) (s2: state Lsem2).

    Inductive comp_step: comp_state -> trace -> comp_state -> Prop :=
    | step1 s1 t s1':
        Step L1 qset1 s1 t s1' ->
        comp_step (st1 s1) t (st1 s1')
    | step2 s1 s2 t s2':
        Step L2 qset2 s2 t s2' ->
        comp_step (st2 s1 s2) t (st2 s1 s2')
    | step_push s1 q s2:
        at_external L1 s1 q ->
        initial_state L2 q s2 ->
        not (valid_query Lsem1 se q) ->
        not (valid_query_inh q) ->
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
        not (valid_query Lsem1 se q) ->
        not (valid_query Lsem2 se q) ->
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

    Lemma star_internal1 s t s':
      Star L1 qset1 s t s' ->
      star (fun _ => comp_step) tt (st1 s) t (st1 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal1 s t s':
      Plus L1 qset1 s t s' ->
      plus (fun _ => comp_step) tt (st1 s) t (st1 s').
    Proof.
      destruct 1; econstructor; eauto using step1, star_internal1.
    Qed.

    Lemma star_internal2 s1 s t s':
      Star L2 qset2 s t s' ->
      star (fun _ => comp_step) tt (st2 s1 s) t (st2 s1 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal2 s1 s t s':
      Plus L2 qset2 s t s' ->
      plus (fun _ => comp_step) tt (st2 s1 s) t (st2 s1 s').
    Proof.
      destruct 1; econstructor; eauto using step2, star_internal2.
    Qed.

  End WITH_SE.

  Program Definition comp_semantics' sk: semantics liA liC :=
    {|
      activate se :=
        {|
          step p ge:= comp_step se p;
          initial_state := comp_initial_state se;
          at_external := comp_at_external se;
          after_external := comp_after_external se;
          final_state := comp_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint i := footprint Lsem1 i \/ footprint Lsem2 i;
    |}.
  Next Obligation.
    inv H0.
    - apply step1. eapply steps_monotone; eauto.
    - apply step2. eapply steps_monotone; eauto.
      cbn. intros i [ left | right ]; auto.
    - eapply step_push; eauto. intros [? [i [Hi Hix]]].
      apply H4. split; auto. exists i. split; auto.
    - eapply step_pop; eauto.
  Qed.

End COMP.

Definition comp_semantics {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB): option (semantics liA liC) :=
  option_map (comp_semantics' L1 L2) (link (skel L1) (skel L2)).

Section ID.
  Context {li: language_interface}.
  Variant id_state :=
  | st_q (q: query li)
  | st_r (r: reply li).

  Inductive id_step: id_state -> trace -> id_state -> Prop := .

  Inductive id_initial_state: query li -> id_state -> Prop :=
  | id_initial_state_intro q:
      id_initial_state q (st_q q).

  Inductive id_at_external: id_state -> query li -> Prop :=
  | id_at_external_intro q:
      id_at_external (st_q q) q.

  Inductive id_after_external: id_state -> reply li -> id_state -> Prop :=
  | id_after_external_intro q r:
      id_after_external (st_q q) r (st_r r).

  Inductive id_final_state: id_state -> reply li -> Prop :=
  | id_final_state_intro r:
      id_final_state (st_r r) r.
End ID.

Program Definition id_semantics {li} sk: semantics li li :=
  {|
  activate se :=
    {|
      step _ _ := id_step;
      initial_state := id_initial_state;
      at_external := id_at_external;
      after_external := id_after_external;
      final_state := id_final_state;
      globalenv := tt;
    |};
  skel := sk;
  footprint i := False;
  |}.

Notation "L1 ∘ L2" :=  (comp_semantics L1 L2)(at level 40, left associativity): lts_scope.

(* Notation " 1 " :=  (id_semantics): lts_scope. *)

(* Section IDENTITY. *)

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

(* End IDENTITY. *)

Lemma qset_step {liA liB S} (L: lts liA liB S) p1 p2 s t s':
  (Step L p1) s t s' -> p1 = p2 -> (Step L p2) s t s'.
Proof.
  now intros H [ ].
Qed.

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
    constructor. econstructor.
    - reflexivity.
    - intros. cbn. now rewrite or_assoc.
    - { intros se _ [ ] qset [ ] Hse.
        instantiate (1 := fun _ _ _ => _). cbn beta.
        apply forward_simulation_step
          with (match_states := assoc_state_match); cbn.
        - intros q _ s1 [ ] H. inv H.
          eexists. split; try repeat constructor; auto.
        - intros s1 s2 r Hs H. inv H. inv Hs.
          eexists. split; try repeat constructor; auto.
        - intros s1 s2 q Hs Hext. inv Hext. inv H1. inv Hs.
          eexists tt, _. repeat apply conj; try repeat constructor; auto.
          intros [? [i [[Hi1 | Hi2] ?]]];
            [ apply H; split; auto; eexists; split; eauto |
              apply H2; split; auto; eexists; split; eauto ].
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
              -- intros [? [x [? ?]]]. apply H3.
                 split; auto. eexists; split; eauto.
              -- intros [? [x [[? | ?] ?]]].
                 apply H3. split; auto; eexists; split; eauto.
                 apply H2. split; auto; eexists; split; eauto.
              -- intros [? [x [? ?]]].
                 apply H3. split; auto; eexists; split; eauto.
            * eapply step_pop; try constructor; eauto.
          + inv H0. eexists; split; [ | constructor ].
            inv Hs. constructor. eapply step_push; eauto.
          + inv H. eexists; split; [ | constructor].
            inv Hs. constructor. econstructor; eauto.
      }
    - apply well_founded_ltof.
  Qed.

  (* Lemma assoc2: L1 ∘ L2 ∘ L3 ≤ L1 ∘ (L2 ∘ L3). *)
  Lemma assoc2: L ≤ L'.
  Proof.
    constructor. econstructor.
    - reflexivity.
    - intros. cbn. now rewrite or_assoc.
    - { intros se _ [ ] qset [ ] Hse.
        instantiate (1 := fun _ _ _ => _). cbn beta.
        apply forward_simulation_step
          with (match_states := fun s1 s2 => assoc_state_match s2 s1); cbn.
        - intros q _ s1 [ ] H. inv H. inv H0.
          eexists; split; constructor; auto.
        - intros s1 s2 r Hs H. inv H. inv H0. inv Hs.
          eexists; split; constructor; auto.
        - intros s1 s2 q Hs Hext. inv Hext. inv Hs.
          eexists tt, _. repeat apply conj; try repeat constructor; auto.
          + intros [? [x [? ?]]].
            apply H. split; auto; eexists; split; eauto.
            left; auto.
          + intros [? [x [[|]]]].
            apply H. split; auto; eexists; split; eauto. right. auto.
            apply H0. split; auto; eexists; split; eauto.
          + intros [? [x [? ?]]].
            apply H. split; auto; eexists; split; eauto.
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
            intros [? [x [[|]]]].
            apply H3. split; auto; eexists; split; eauto.
            apply H2. split; auto; eexists; split; eauto.
          + inv H0. inv Hs. eexists; split; constructor.
            eapply step_pop; eauto.
      }
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
          (Hse2: Genv.valid_for (skel L2) se1).

  Variant index := | index1: fsim_index HL1 -> index
                   | index2: fsim_index HL1 -> fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
             | order1 i1 i1': fsim_order HL1 i1 i1' ->
                              order (index1 i1) (index1 i1')
             | order2 i1 i2 i2': fsim_order HL2 i2 i2' ->
                                 order (index2 i1 i2) (index2 i1 i2').

  Inductive match_states: index -> comp_state L1 L2 -> comp_state L1' L2' -> Prop :=
  | match_st1 i1 s1 s1':
      fsim_match_states HL1 se1 se2 w i1 s1 s1' ->
      match_states (index1 i1) (st1 L1 L2 s1) (st1 L1' L2' s1')
  | match_st2 i1 i2 s1 s1' s2 s2' w':
      match_senv cc2 w' se1 se2 ->
      fsim_match_states HL2 se1 se2 w' i2 s2 s2' ->
      (forall r1 r2 (s2 : state L1),
          match_reply cc2 w' r1 r2 ->
          after_external (L1 se1) s1 r1 s2 ->
          exists (i' : fsim_index HL1) (s2' : state L1'),
            after_external (L1' se2) s1' r2 s2' /\
            fsim_match_states HL1 se1 se2 w i' s2 s2') ->
      match_states (index2 i1 i2) (st2 L1 L2 s1 s2) (st2 L1' L2' s1' s2').

  Local Lemma semantics_simulation sk sk':
    fsim_properties cc1 cc3 se1 se2 w qset
                    (comp_semantics' L1 L2 sk se1)
                    (comp_semantics' L1' L2' sk' se2)
                    index order match_states.
  Proof.
    split; cbn.
    - intros q1 q2 s1 Hq H. inv H.
      pose proof (fsim_lts HL1 _ _ qset Hse Hse1).
      edestruct @fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
      exists (index1 idx), (st1 L1' L2' s'). split; econstructor; eauto.
    - intros i s1 s2 r1 Hs H. inv H. inv Hs.
      pose proof (fsim_lts HL1 _ _ qset Hse Hse1).
      edestruct @fsim_match_final_states as (r' & H' & Hr'); eauto.
      exists r'. split; auto. constructor; auto.
    - intros i s1 s2 q1 Hs H. inv H. inv Hs.
      pose proof (fsim_lts HL2 _ _ qset H4 Hse2).
      edestruct @fsim_match_external as (w1 & q' & H' & Hq' & Hse' & HH); eauto.
      exists w1, q'. repeat apply conj; auto.
      + constructor; auto.
        erewrite <- match_valid_query; [ | constructor; apply HL1 | .. ]; eauto.
        erewrite <- match_valid_query; [ | constructor; apply HL2 | .. ]; eauto.
      + intros r1 r2 xs1 Hr HH'. inv HH'.
        specialize (HH _ _ _ Hr H10) as (i2' & xs2 & Haft & Hss).
        eexists (index2 i1 i2'), (st2 L1' L2' _ _). split.
        * econstructor. eauto.
        * econstructor; eauto.
    - intros s1 t s2 Hstep idx s1' Hs.
      inv Hstep; inv Hs.
      + pose proof (fsim_lts HL1 _ _ qset Hse Hse1).
        edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        exists (index1 idx'), (st1 L1' L2' s2'). split.
        * destruct Hs2'; [ left | right ].
          apply plus_internal1. auto.
          split. apply star_internal1. apply H1. constructor; apply H1.
        * constructor. auto.
      + pose proof (fsim_lts HL2 _ _ (fun i => footprint L1 i \/ qset i) H2 Hse2).
        edestruct @fsim_simulation as (idx' & xs2' & Hs2' & Hs'); eauto.
        exists (index2 i1 idx'), (st2 L1' L2' s1'0 xs2'). split.
        * destruct Hs2'; [ left | right ].
          -- apply plus_internal2.
             replace (fun i : ident => footprint L1' i \/ qset i) with
                 (fun i : ident => footprint L1 i \/ qset i); auto.
             apply functional_extensionality. intros x.
             apply EquivThenEqual.
             apply or_iff_compat_r.
             eapply fsim_footprint. eauto.
          -- split. apply star_internal2.
             destruct H1.
             replace (fun i : ident => footprint L1' i \/ qset i) with
                 (fun i : ident => footprint L1 i \/ qset i); auto.
             apply functional_extensionality. intros x.
             apply EquivThenEqual.
             apply or_iff_compat_r.
             eapply fsim_footprint. eauto.
             constructor. apply H1.
        * econstructor; eauto.
      + pose proof (fsim_lts HL1 _ _ qset Hse Hse1).
        edestruct @fsim_match_external as (w' & q' & H' & Hq' & Hse' & HH); eauto.
        pose proof (fsim_lts HL2 _ _ (fun i => footprint L1 i \/ qset i) Hse' Hse2).
        edestruct @fsim_match_initial_states as (i2 & s2' & Hs2' & Hs'); eauto.
        exists (index2 i1 i2), (st2 L1' L2' s1'0 s2'). split.
        * left. apply plus_one. eapply step_push; eauto.
          erewrite <- match_valid_query; [ | constructor; apply HL1 | .. ]; eauto.
          intros [? [i [Hi Hix]]].
          apply H2. split. erewrite match_query_defined; eauto.
          exists i. split; auto.
          erewrite match_senv_symbol_address; eauto.
        * econstructor; eauto.
      + pose proof (fsim_lts HL2 _ _ (fun i => footprint L1 i \/ qset i) H3 Hse2).
        edestruct @fsim_match_final_states as (r' & H' & Hr'); eauto.
        edestruct H7 as (idx & xs2' & HH & Hs2'); eauto.
        exists (index1 idx), (st1 L1' L2' xs2'). split.
        * left. apply plus_one. eapply step_pop; eauto.
        * constructor. auto.
  Qed.

End FSIM.

Lemma categorical_compose_simulation
      {liA1 liA2 liB1 liB2 liC1 liC2}
      (cc1: callconv liA1 liA2) (cc2: callconv liB1 liB2) (cc3: callconv liC1 liC2)
      L1a L1b L1 L2a L2b L2:
  forward_simulation cc2 cc3 L1a L2a ->
  forward_simulation cc1 cc2 L1b L2b ->
  L1a ∘ L1b = Some L1 -> L2a ∘ L2b = Some L2 ->
  forward_simulation cc1 cc3 L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold comp_semantics in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  constructor.
  eapply Forward_simulation
    with (order cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb)
         (match_states cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb).
  - cbn. destruct Ha, Hb. congruence.
  - cbn. intros i. destruct Ha, Hb.
    rewrite fsim_footprint, fsim_footprint0. reflexivity.
  - intros se1 se2 w qset Hse Hse1.
    pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
    eapply semantics_simulation; eauto.
    eapply Genv.valid_for_linkorder; eauto.
    eapply Genv.valid_for_linkorder; eauto.
  - clear - Ha Hb. intros [|].
    + induction (fsim_order_wf Ha f). constructor.
      intros. inv H1. apply H0. auto.
    + induction (fsim_order_wf Hb f0). constructor.
      intros. inv H1. apply H0. auto.
Qed.

Section APPROX.
  Context {li} (L1 L2: semantics li li).
  Context (sk: AST.program unit unit).

  Let L := fun i => match i with true => L1 | false => L2 end.

  Inductive match_frame: comp_state L1 L2 -> list (SmallstepLinking_.frame L) -> Prop :=
  | match_frame1 s:
      match_frame (st1 L1 L2 s) (st L true s :: nil)
  | match_frame2 s1 s2:
      match_frame (st2 L1 L2 s1 s2) (st L false s2 :: st L true s1 :: nil).

  Hypothesis valid_initial_state:
    forall i se q s, initial_state (L i se) q s -> valid_query (L i) se q.

  Lemma categorical_compose_approximation:
    forward_simulation 1 1 (comp_semantics' L1 L2 sk) (SmallstepLinking_.semantics L sk).
  Proof.
    constructor. econstructor; eauto.
    {
      intros i. split.
      - intros [|]; [exists true | exists false]; firstorder.
      - intros [[|] ?]; [left | right]; firstorder.
    }
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_frame).
    - intros q ? s1 [ ] H. inv H.
      exists (st L true s :: nil). split; constructor.
      eapply valid_initial_state; eauto. auto.
    - intros s1 s2 r Hs H. inv H. inv Hs.
      exists r. split; constructor; auto.
    - intros s s' q Hs H. inv H. inv Hs.
      exists tt, q. repeat apply conj; try constructor; auto.
      + intros [|]; auto.
      + intros. inv H3. inv H. eexists. split; econstructor; eauto.
    - intros s1 t s2 Hstep s1' Hs. inv Hstep; inv Hs.
      + eexists (st L true _ :: nil). split; constructor; auto.
      + eexists (st L false _ :: st L true _ :: nil). split; constructor.
        eapply steps_monotone; [ | eauto ]. cbn.
        intros. right; auto.
      + eexists (st L false _ :: st L true _ :: nil). split.
        eapply SmallstepLinking_.step_push; eauto.
        constructor.
      + eexists (st L true _ :: nil). split.
        eapply SmallstepLinking_.step_pop; eauto.
        constructor.
    - apply well_founded_ltof.
  Qed.

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

  Lemma ccref_to_fsim sk:
    forward_simulation cc' cc (id_semantics sk) (id_semantics sk).
  Proof.
    constructor. econstructor. reflexivity. reflexivity.
    intros se1 se2 w qset Hse Hse1.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step
      with (match_states := cc_state_match w); cbn.
    - intros q1 q2 s1 Hq Hs.
      inv Hs. exists (st_q q2).
      split; econstructor; eauto.
    - intros s1 s2 r1 Hs Hr.
      inv Hr. inv Hs. exists r2. split. constructor. auto.
    - intros s1 s2 q1 Hs Hq. inv Hq. inv Hs.
      specialize (ref _ _ _ _ _ Hse H0).
      destruct ref as (w' & Hse' & Hq' & Hr).
      exists w'. exists q2. repeat apply conj; try constructor; auto.
      intros. inv H1. exists (st_r r2). split; constructor.
      apply Hr. auto.
    - intros. inv H.
    - apply well_founded_ltof.
  Qed.

End CALL_CONV_REF.

Section HCOMP_IDENTITY.

  Context {li} (L: semantics li li).
  Variable (sk: AST.program unit unit).

  (* I suppose this holds for Clight semantics *)
  Hypothesis extcall_invalid:
    forall se s q, Smallstep_.at_external (L se) s q -> ~ valid_query L se q.

  Hypothesis initial_state_valid:
    forall se q s, Smallstep_.initial_state (L se) q s -> valid_query L se q.

  Let L1 := fun b => match b with | true => id_semantics sk | false => L end.

  Local Inductive state_match1: list (SmallstepLinking_.frame L1) -> Smallstep_.state L -> Prop :=
  | state_match_intro1 s:
      state_match1 (SmallstepLinking_.st L1 false s :: nil) s.

  Lemma hcomp_left_identity1: (SmallstepLinking_.semantics L1 (skel L)) ≤ L.
  Proof.
    constructor. econstructor. reflexivity.
    {
      intros id. split.
      - intros [[|] ?]; firstorder.
      - intros. exists false. firstorder.
    }
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := state_match1).
    - intros q _ s1 [ ] H. inv H.
      destruct i; cbn in *.
      + firstorder.
      + eexists. split; try econstructor; auto.
    - intros s1 s2 r Hs H. inv H. inv Hs.
      SmallstepLinking_.subst_dep.
      eexists. split; try econstructor; auto.
    - intros s1 s2 q Hs H. inv H. inv Hs.
      SmallstepLinking_.subst_dep.
      eexists tt, _. repeat apply conj; try constructor; eauto.
      intros r _ s1' [ ] H. inv H.
      SmallstepLinking_.subst_dep.
      eexists. split; try econstructor; eauto.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv Hs; SmallstepLinking_.subst_dep.
      + eexists; split; eauto. constructor.
      + destruct j; exfalso.
        * firstorder.
        * apply extcall_invalid in H. apply H. auto.
    - apply well_founded_ltof.
  Qed.

  Lemma hcomp_left_identity2: L ≤ (SmallstepLinking_.semantics L1 (skel L)).
  Proof.
    constructor. econstructor. reflexivity.
    {
      intros id. split.
      - intros. exists false. firstorder.
      - intros [[|] ?]; firstorder.
    }
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := fun s1 s2 => state_match1 s2 s1).
    - intros q _ s1 [ ] H.
      eexists; split; econstructor; eauto.
    - intros s1 s2 r1 Hs H. inv Hs.
      eexists; split; econstructor; eauto.
    - intros s1 s2 q1 Hs H. inv Hs.
      eexists tt, _. repeat apply conj; try econstructor; auto.
      + intros j. destruct j.
        * unfold valid_query. firstorder.
        * apply extcall_invalid in H. apply H.
      + inv H0. split; cbn; econstructor; auto.
    - intros s1 t s1' Hstep s2 Hs. inv Hs.
      eexists; split; [ | constructor].
      cbn. apply SmallstepLinking_.step_internal. auto.
    - apply well_founded_ltof.
  Qed.

  Lemma hcomp_left_identity: (SmallstepLinking_.semantics L1 (skel L)) ≡ L.
  Proof.
    split; [ exact hcomp_left_identity1 | exact hcomp_left_identity2].
  Qed.

  Let L2 := fun b => match b with | true => L | false => id_semantics sk end.

  Local Inductive state_match2: list (SmallstepLinking_.frame L2) -> Smallstep_.state L -> Prop :=
  | state_match_intro2 s:
      state_match2 (SmallstepLinking_.st L2 true s :: nil) s.

  Lemma hcomp_right_identity1: (SmallstepLinking_.semantics L2 (skel L)) ≤ L.
  Proof.
    constructor. econstructor. reflexivity.
    {
      intros id. split.
      - intros [[|] ?]; firstorder.
      - intros. exists true. firstorder.
    }
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := state_match2).
    - intros q ? s1 [ ] H. inv H.
      destruct i.
      + eexists; split; eauto. constructor.
      + firstorder.
    - intros s1 s2 r Hs H. inv H. inv Hs.
      SmallstepLinking_.subst_dep.
      eexists; split; eauto. constructor.
    - intros s1 s2 q Hs H. inv H. inv Hs.
      SmallstepLinking_.subst_dep.
      eexists tt, _. repeat apply conj; try constructor. auto.
      intros r1 r2 s1' [ ] H.
      inv H. SmallstepLinking_.subst_dep.
      eexists; split; eauto. constructor.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep; inv Hs; SmallstepLinking_.subst_dep.
      + eexists; split; eauto. constructor.
      + exfalso. destruct j.
        * apply extcall_invalid in H. firstorder.
        * firstorder.
    - apply well_founded_ltof.
  Qed.

  Lemma hcomp_right_identity2: L ≤ (SmallstepLinking_.semantics L2 (skel L)).
  Proof.
    constructor. econstructor. reflexivity.
    {
      intros id. split.
      - intros. exists true. firstorder.
      - intros [[|] ?]; firstorder.
    }
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := fun s1 s2 => state_match2 s2 s1).
    - intros q ? s1 [ ] H. eexists; split.
      2: econstructor. constructor; auto.
      eapply initial_state_valid; eauto.
    - intros s1 s2 r1 Hs H. eexists; split.
      2: econstructor. inv Hs. constructor. auto.
    - intros s1 s2 q Hs H. inv Hs.
      eexists tt, _. repeat apply conj; try constructor; auto.
      + intros [|].
        * eapply extcall_invalid; eauto.
        * firstorder.
      + intros r ? s [ ] Hx.
        eexists; split; constructor; auto.
    - intros s1 t s1' Hstep s2 Hs. inv Hs.
      eexists; split; constructor; auto.
    - apply well_founded_ltof.
  Qed.

  Lemma hcomp_right_identity: (SmallstepLinking_.semantics L2 (skel L)) ≡ L.
  Proof.
    split; [ exact hcomp_right_identity1 | exact hcomp_right_identity2].
  Qed.

End HCOMP_IDENTITY.
