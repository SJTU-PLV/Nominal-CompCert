Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Linking.
Require Import Classical.

Require Import Smallstep Callconv ForwardSim.


Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.

Section LINK.

  Context {li} (L: bool -> semantics li li).
  Let I := bool.

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
          valid_query (L j se) q = true ->
          Smallstep.initial_state (L j se) q s' ->
          step (st i s :: k) E0 (st j s' :: st i s :: k)
      | step_pop i j s sk r s' k :
          Smallstep.final_state (L i se) s r ->
          Smallstep.after_external (L j se) sk r s' ->
          step (st i s :: st j sk :: k) E0 (st j s' :: k).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s :
          valid_query (L i se) q = true ->
          Smallstep.initial_state (L i se) q s ->
          initial_state q (st i s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro i s q k:
          Smallstep.at_external (L i se) s q ->
          (forall j, valid_query (L j se) q = false) ->
          at_external (st i s :: k) q.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro i s r s' k:
          Smallstep.after_external (L i se) s r s' ->
          after_external (st i s :: k) r (st i s' :: k).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro i s r :
          Smallstep.final_state (L i se) s r ->
          final_state (st i s :: nil) r.

    Definition valid_query q :=
      valid_query (L true se) q || valid_query (L false se) q.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics: semantics li li :=
    {|
      activate se :=
        {|
          Smallstep.step ge := step se;
          Smallstep.valid_query := valid_query se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external se;
          Smallstep.after_external := after_external se;
          Smallstep.final_state := final_state se;
          Smallstep.globalenv := tt;
        |};
      skel := sk;
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
    receptive semantics.
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
    forall i j se q,
      Smallstep.valid_query (L i se) q = true ->
      Smallstep.valid_query (L j se) q = true ->
      i = j.

  Lemma semantics_determinate:
    (forall i, determinate (L i)) ->
    determinate semantics.
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
  Context {li1 li2} (cc: callconv' li1 li2).

  Notation I := bool.
  Context (L1 : I -> Smallstep.semantics li1 li1).
  Context (L2 : I -> Smallstep.semantics li2 li2).
  Context (HL : forall i, fsim_components' cc cc (L1 i) (L2 i)).
  Context (se1 se2: Genv.symtbl) (w : ccworld' cc).
  Context (Hse: match_senv' cc w se1 se2).
  Context (Hcompat: forall i, Genv.skel_symtbl_compatible (skel (L1 i)) (skel (L2 i)) se1 se2).
  Notation index := {i & fsim_index' (HL i)}.

  Inductive match_topframes wk: index -> frame L1 -> frame L2 -> Prop :=
    match_topframes_intro i s1 s2 idx:
      match_senv' cc wk se1 se2 ->
      Genv.valid_for (skel (L1 i)) se1 ->
      fsim_match_states' (HL i) se1 se2 wk idx s1 s2 ->
      match_topframes wk
        (existT _ i idx)
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_contframes wk wk': frame L1 -> frame L2 -> Prop :=
    match_contframes_intro i s1 s2:
      match_senv' cc wk' se1 se2 ->
      (forall r1 r2 s1', match_reply' cc wk r1 r2 ->
       Smallstep.after_external (L1 i se1) s1 r1 s1' ->
       exists idx s2',
         Smallstep.after_external (L2 i se2) s2 r2 s2' /\
         fsim_match_states' (HL i) se1 se2 wk' idx s1' s2') ->
      match_contframes wk wk'
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_states: index -> list (frame L1) -> list (frame L2) -> Prop :=
    | match_states_cons wk idx f1 f2 k1 k2:
        match_topframes wk idx f1 f2 ->
        match_cont wk k1 k2 ->
        match_states idx (f1 :: k1) (f2 :: k2)
  with match_cont: ccworld' cc -> _ -> _ -> Prop :=
    | match_cont_cons wk wk' f1 f2 k1 k2:
        match_contframes wk wk' f1 f2 ->
        match_cont wk' k1 k2 ->
        match_cont wk (f1 :: k1) (f2 :: k2)
    | match_cont_nil:
        match_cont w nil nil.

  Inductive order: index -> index -> Prop :=
    order_intro i x y: fsim_order' (HL i) x y -> order (existT _ i x) (existT _ i y).

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
      edestruct @fsim_simulation_1 as (idx' & s2' & Hs2' & Hs'); eauto using fsim_lts'.
      eexists (existT _ i idx'), _. split.
      * destruct Hs2'; [left | right]; intuition eauto using star_internal, plus_internal.
        constructor. auto.
      * econstructor; eauto. econstructor; eauto.
    - (* cross-component call *)
      inv H5; subst_dep. clear idx0.
      edestruct @fsim_match_external' as (wx & qx2 & Hqx2 & Hqx & Hsex & Hrx); eauto using fsim_lts'.
      pose proof (fsim_lts' (HL j) _ Hsex (Hcompat j)).
      edestruct @fsim_match_initial_states' as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_push; eauto 1.
        erewrite fsim_match_valid_query'; eauto.
      + destruct (Hcompat j) as (A & B & C).
        repeat (econstructor; eauto).
    - (* cross-component return *)
      inv H4; subst_dep. clear idx0.
      pose proof (fsim_lts' (HL i) _ H3 (Hcompat i)).
      edestruct @fsim_match_final_states' as (r2 & Hr2 & Hr); eauto.
      inv H6. inv H8; subst_dep. edestruct H10 as (idx' & s2' & Hs2'& Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_pop; eauto.
      + destruct (Hcompat j) as (A & B & C).
        repeat (econstructor; eauto).
  Qed.

  Lemma initial_states_simulation:
    forall q1 q2 s1, match_query' cc w q1 q2 -> initial_state L1 se1 q1 s1 ->
    exists idx s2, initial_state L2 se2 q2 s2 /\ match_states idx s1 s2.
  Proof.
    intros q1 q2 _ Hq [i s1 Hq1 Hs1]. destruct (Hcompat i) as (A & B & C).
    pose proof (fsim_lts' (HL i) _  Hse (Hcompat i)).
    edestruct @fsim_match_initial_states' as (idx & s2 & Hs2 & Hs); eauto.
    exists (existT _ i idx), (st L2 i s2 :: nil).
    split; econstructor; eauto.
    + erewrite fsim_match_valid_query'; eauto.
    + econstructor; eauto.
    + constructor.
  Qed.

  Lemma final_states_simulation:
    forall idx s1 s2 r1, match_states idx s1 s2 -> final_state L1 se1 s1 r1 ->
    exists r2, final_state L2 se2 s2 r2 /\ match_reply' cc w r1 r2.
  Proof.
    intros idx s1 s2 r1 Hs Hr1. destruct Hr1 as [i s1 r1 Hr1].
    inv Hs. inv H4. inv H2. subst_dep. clear idx0.
    pose proof (fsim_lts' (HL i) _ H1 (Hcompat i)).
    edestruct @fsim_match_final_states' as (r2 & Hr2 & Hr); eauto.
    exists r2. split; eauto. constructor; eauto.
  Qed.

  Lemma external_simulation:
    forall idx s1 s2 qx1, match_states idx s1 s2 -> at_external L1 se1 s1 qx1 ->
    exists wx qx2, at_external L2 se2 s2 qx2 /\ match_query' cc wx qx1 qx2 /\ match_senv' cc wx se1 se2 /\
    forall rx1 rx2 s1', match_reply' cc wx rx1 rx2 -> after_external L1 se1 s1 rx1 s1' ->
    exists idx' s2', after_external L2 se2 s2 rx2 s2' /\ match_states idx' s1' s2'.
  Proof.
    intros idx s1 s2 q1 Hs Hq1. destruct Hq1 as [i s1 qx1 k1 Hqx1 Hvld].
    inv Hs. inv H2. subst_dep. clear idx0.
    pose proof (fsim_lts' (HL i) _ H1 (Hcompat i)) as Hi.
    edestruct @fsim_match_external' as (wx & qx2 & Hqx2 & Hqx & Hsex & H); eauto.
    exists wx, qx2. intuition idtac.
    + constructor. eauto.
      intros j. pose proof (fsim_lts' (HL j)  _ Hsex (Hcompat j)).
      erewrite fsim_match_valid_query'; eauto.
    + inv H2; subst_dep.
      edestruct H as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ i idx'), _.
      split; repeat (econstructor; eauto).
  Qed.

  Lemma semantics_simulation sk1 sk2:
    fsim_properties' cc cc se1 se2 w
      (semantics L1 sk1 se1)
      (semantics L2 sk2 se2)
      index order match_states.
  Proof.
    split; cbn.
    - intros. unfold valid_query. f_equal.
      + eapply (fsim_lts' (HL true)); eauto.
      + eapply (fsim_lts' (HL false)); eauto.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using step_simulation.
  Qed.
End FSIM.

(** * Linking operator *)

Local Unset Program Cases.

Definition compose {li} (La Lb: Smallstep.semantics li li) :=
  let L i := match i with true => La | false => Lb end in
  option_map (semantics L) (link (skel La) (skel Lb)).

(*
Lemma link_def_inv_var : forall (v1 v2: AST.globvar unit) v',
    link_def (AST.Gvar v1) (AST.Gvar v2) = Some v' ->
    exists v, v' = (AST.Gvar v) /\ link v1 v2 = Some v.
Proof.
  intros. unfold link_def in H. destruct link; try discriminate.
  inv H. eauto.
Qed.

Lemma link_vardef_inv:
  forall (v1 v2: AST.globvar unit) v,
    link_vardef v1 v2 = Some v ->
    exists info init,
    link v1.(AST.gvar_info) v2.(AST.gvar_info) = Some info
    /\ link_varinit v1.(AST.gvar_init) v2.(AST.gvar_init) = Some init
    /\ v1.(AST.gvar_readonly) = v2.(AST.gvar_readonly)
    /\ v1.(AST.gvar_volatile) = v2.(AST.gvar_volatile)
    /\ v = {| AST.gvar_info := info;
            AST.gvar_init := init;
            AST.gvar_readonly := v1.(AST.gvar_readonly);
            AST.gvar_volatile := v1.(AST.gvar_volatile) |}.
Proof.
  unfold link_vardef; intros.
  destruct (link (AST.gvar_info v1) (AST.gvar_info v2)); try discriminate.
  destruct (link (AST.gvar_init v1) (AST.gvar_init v2)) eqn:Hi; try discriminate.
  apply link_varinit_inv in Hi.
  destruct eqb eqn:E1; try discriminate.
  destruct (eqb (AST.gvar_volatile v1) (AST.gvar_volatile v2)) eqn:E2; try discriminate.
  cbn in H. inv H. exists u,l. repeat apply conj; eauto.
  eapply eqb_prop; eauto.
  eapply eqb_prop; eauto.
Qed.

Lemma link_linkorder1:
  forall (A : Type) (Linker : Linker A) (x y z : A), link x y = Some z -> linkorder x z.
Proof. intros. exploit link_linkorder; eauto. intros. apply H0. Qed.

Lemma link_linkorder2:
  forall (A : Type) (Linker : Linker A) (x y z : A), link x y = Some z -> linkorder y z.
Proof. intros. exploit link_linkorder; eauto. intros. apply H0. Qed.                                                                                              
Lemma linkorder_link_linkorder: forall (g1 g2 g1' g2' g g': AST.globdef unit unit),
    linkorder g1 g1' -> linkorder g2 g2' ->
    link g1 g2 = Some g -> link g1' g2' = Some g' ->
    linkorder g g'.
Proof.
  intros.
  destruct g1.
  - (* unit function *)
    inv H. destruct f. inv H4.
    destruct fd2. destruct g2; inv H1.
    destruct f. inv H0. simpl. destruct fd2.
    rewrite H2. apply linkorder_refl.
  - (* unit variable *)
    inv H. destruct g2. inv H1. inv H0.
(*    inv H4. destruct info1. destruct info2. inv H.
    inv H3. destruct info1. destruct info2. inv H. *)
    apply link_def_inv_var in H1. destruct H1 as (tv & H1 & Link1).
    apply link_vardef_inv in Link1.
    destruct Link1 as (info & init & _ & Hinit1 & A & B & Htv).
    apply link_def_inv_var in H2. destruct H2 as (sv & H2 & Link2).
    apply link_vardef_inv in Link2.
    destruct Link2 as (sinfo & sinit & _ & Hinit2 & C & D & Hsv).
    subst. inv H4. cbn in *. inv H3. cbn in *.
    constructor. constructor.
    + (*info*)
      destruct info. destruct sinfo. apply linkorder_refl.
    + (*init*) clear C D H H1.
      unfold link_varinit in Hinit1.
      destruct (classify_init i1) eqn: Hi1.
      * inv H0.
        ++ cbn in Hinit2. inv Hinit1. inv Hinit2. eauto.
        ++ inv Hinit1.
           eapply linkorder_trans; eauto. eapply link_linkorder; eauto.
      * destruct (classify_init i0) eqn: Hi2; try discriminate.
        ++ (*size, extern*)
          inv Hinit1. eapply linkorder_trans; eauto using link_linkorder1.
        ++ (*size, size *)
          cbn in Hinit1. destruct zeq; try discriminate. inv Hinit1.
          eapply linkorder_trans; eauto using link_linkorder2.
        ++ (*size, def*)
          destruct zeq; try discriminate. inv Hinit1.
          eapply linkorder_trans; eauto using link_linkorder2.
      * destruct (classify_init i0) eqn: Hi2; try discriminate.
        ++ (*def, extern*)
          inv Hinit1. eapply linkorder_trans; eauto using link_linkorder1.
        ++ (*def, size*)
          destruct zeq; try discriminate. inv Hinit1.
          eapply linkorder_trans; eauto using link_linkorder1.
Qed.
*)

Lemma prog_nodef_nopublic: forall (p : AST.program unit unit) id,
    Maps.PTree.get id (AST.prog_defmap p) = None ->
    ~ In id (AST.prog_public p).
Proof.
Admitted. (*need to be added to AST or Axiomized *)

Lemma skel_le_compose : forall (sk1a sk1b sk2a sk2b sk1 sk2: AST.program unit unit),
    link sk1a sk1b = Some sk1 -> link sk2a sk2b = Some sk2 ->
    Genv.skel_le sk2a sk1a -> Genv.skel_le sk2b sk1b ->
    Genv.skel_le sk2 sk1.
Proof.
  intros until sk2. intros Hsk1 Hsk2 [Ha1 [Ha2 Hpa]] [Hb1 [Hb2 Hpb]].
  edestruct link_prog_inv as [Hm1 [Hd1 H1]]. apply Hsk1.
  edestruct link_prog_inv as [Hm2 [Hd2 H2]]. apply Hsk2.
  repeat apply conj.
  - intros.
    rewrite H1. rewrite prog_defmap_elements.
    erewrite Maps.PTree.gcombine; eauto.
    rewrite H2 in H. rewrite prog_defmap_elements in H.
    erewrite Maps.PTree.gcombine in H; eauto.
    unfold link_prog_merge in *.    
    destruct (Maps.PTree.get id (AST.prog_defmap (sk2a))) eqn:FIND2a;
      destruct (Maps.PTree.get id (AST.prog_defmap (sk2b))) eqn:FIND2b;
      try discriminate.
    + (* exploit Hd1; eauto. intros (PUB1a & PUB1b & _). *)
      apply Ha1 in FIND2a as FIND1a.
      apply Hb1 in FIND2b as FIND1b.
      rewrite FIND1a, FIND1b. eauto.
    + apply Ha1 in FIND2a as FIND1a. rewrite FIND1a. 
      destruct (Maps.PTree.get id (AST.prog_defmap sk1b)) eqn:FIND1b.
      exploit Hd1; eauto. intros (PUB1a & PUB1b & _).
      exploit Hb2; eauto. intro HH. congruence. congruence.
    + apply Hb1 in FIND2b as FIND1b. rewrite FIND1b. 
      destruct (Maps.PTree.get id (AST.prog_defmap sk1a)) eqn:FIND1a.
      exploit Hd1; eauto. intros (PUB1a & PUB1b & _).
      exploit Ha2; eauto. intro HH. congruence. congruence.
  - intros.
    rewrite H2. rewrite prog_defmap_elements.
    erewrite Maps.PTree.gcombine; eauto.
    rewrite H1 in H. rewrite prog_defmap_elements in H.
    erewrite Maps.PTree.gcombine in H; eauto.
    unfold link_prog_merge in *.
    destruct (Maps.PTree.get id (AST.prog_defmap (sk1a))) eqn:FIND1a;
      destruct (Maps.PTree.get id (AST.prog_defmap (sk1b))) eqn:FIND1b;
      try discriminate.
    + exploit Hd1; eauto. intros (PUB1a & PUB1b & _).
      apply Ha2 in FIND1a as FIND2a; eauto. rewrite FIND2a.
      apply Hb2 in FIND1b as FIND2b; eauto. rewrite FIND2b. eauto.
    + destruct (Maps.PTree.get id (AST.prog_defmap sk2b)) eqn:FIND2b.
      * apply Hb1 in FIND2b as FIND1b'. congruence.
      * assert (~In id (AST.prog_public sk1b)).
        eapply prog_nodef_nopublic; eauto.
        assert (In id (AST.prog_public sk1a)).
        rewrite H1 in H0. cbn in H0.
        apply in_app_or in H0. destruct H0; try discriminate; eauto.
        exfalso. eauto.
        apply Ha2 in FIND1a as FIND2a; eauto. rewrite FIND2a.
        eauto.
    + destruct (Maps.PTree.get id (AST.prog_defmap sk2a)) eqn:FIND2a.
      * apply Ha1 in FIND2a as FIND1a'. congruence.
      * assert (~In id (AST.prog_public sk1a)).
        eapply prog_nodef_nopublic; eauto.
        assert (In id (AST.prog_public sk1b)).
        rewrite H1 in H0. cbn in H0.
        apply in_app_or in H0. destruct H0; try discriminate; eauto.
        exfalso. eauto.
        apply Hb2 in FIND1b as FIND2b; eauto. rewrite FIND2b.
        eauto.
  - subst. cbn. congruence.
Qed.

Lemma find_in_names{F V:Type}: forall (sk: AST.program F V) id g,
    Maps.PTree.get id (AST.prog_defmap sk) = Some g ->
    In id (AST.prog_defs_names sk).
Proof.
  intros.
  eapply Memory.Mem.in_map_fst_2.
  eapply AST.in_prog_defmap; eauto.
Qed.

Lemma in_names_linkorder: forall sk1 sk2 id,
        linkorder sk1 sk2 ->
        In id (AST.prog_defs_names sk1) ->
        In id (AST.prog_defs_names sk2).
Proof.
  intros. destruct H as [A [B C]].
  edestruct AST.prog_defmap_dom as [g F]. apply H0.
  exploit C; eauto.
  intros [g' [F' G]].
  eapply find_in_names; eauto.
Qed.

Lemma in_names_link_or : forall sk1 sk2 sk id,
    link sk1 sk2 = Some sk ->
    In id (AST.prog_defs_names sk) ->
    In id (AST.prog_defs_names sk1) \/ In id (AST.prog_defs_names sk2).
Proof.
  intros. edestruct link_prog_inv as [A [B C]]. apply H.
  edestruct AST.prog_defmap_dom as [g F]. apply H0.
  rewrite C in F.
  rewrite prog_defmap_elements in F.
  erewrite Maps.PTree.gcombine in F; eauto.
  unfold link_prog_merge in F.
  destruct ( Maps.PTree.get id (AST.prog_defmap sk1)) eqn:F1.
  - left. eapply find_in_names; eauto.
  - right. eapply find_in_names; eauto.
Qed.
                                         
Lemma compatible_link1: forall se1 se2 sk1a sk1b sk2a sk2b sk1 sk2,
    link sk1a sk1b = Some sk1 ->
    link sk2a sk2b = Some sk2 ->
    Genv.skel_le sk2a sk1a ->
    Genv.skel_le sk2b sk1b ->
    Genv.skel_symtbl_compatible sk1 sk2 se1 se2 ->
    Genv.skel_symtbl_compatible sk1a sk2a se1 se2.
Proof.
  intros until sk2. intros Hsk1 Hsk2 Hlea Hleb Hcom.
  pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
  pose proof (link_linkorder _ _ _ Hsk2) as [Hsk2a Hsk2b].
  edestruct link_prog_inv as [Hm1 [Hd1 H1]]. apply Hsk1.
  edestruct link_prog_inv as [Hm2 [Hd2 H2]]. apply Hsk2.
  destruct Hcom as (A & B & C & D). cbn in *.
  repeat apply conj.
  - eapply Genv.valid_for_linkorder; eauto.
  - eapply Genv.valid_for_linkorder; eauto.
  - intros. exploit C; eauto.
    eapply in_names_linkorder. apply Hsk1a. eauto.
    intro Hsk2id. apply AST.prog_defmap_dom in Hsk2id as Hsk2id'.
    destruct Hsk2id' as [g2 FIND2].
    apply AST.prog_defmap_dom in H as Hsk1aid'.
    destruct Hsk1aid' as [g1a FIND1a].
    destruct (Maps.PTree.get id (AST.prog_defmap (sk1b))) eqn:FIND1b.
    ++ (*id is public, thus l1a -> l2a*)          
      apply link_prog_inv in Hsk1 as INV1. destruct INV1 as ( _ & PUB &  _) .
      exploit PUB; eauto. intros (PUB1a & PUB1b & LINKg).
      clear - Hlea PUB1a H.
      edestruct AST.prog_defmap_dom as [g FIND1a]. apply H.
      eapply Memory.Mem.in_map_fst_2.
      eapply AST.in_prog_defmap.
      destruct Hlea as (_ & Hp & _).
      eapply Hp; eauto.
    ++
      assert (~ In id (AST.prog_defs_names (sk2b))).
      intro. edestruct AST.prog_defmap_dom as [g FIND2b]. eauto.
      destruct Hleb as [HH _]. exploit HH; eauto.
      intro. congruence.
      edestruct in_names_link_or. apply Hsk2. eauto.
      eauto. congruence.
  - destruct Hsk1a. rewrite H. eauto.
Qed.

Lemma compatible_link2: forall se1 se2 sk1a sk1b sk2a sk2b sk1 sk2,
    link sk1a sk1b = Some sk1 ->
    link sk2a sk2b = Some sk2 ->
    Genv.skel_le sk2a sk1a ->
    Genv.skel_le sk2b sk1b ->
    Genv.skel_symtbl_compatible sk1 sk2 se1 se2 ->
    Genv.skel_symtbl_compatible sk1b sk2b se1 se2.
Proof.
  intros until sk2. intros Hsk1 Hsk2 Hlea Hleb Hcom.
  pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
  pose proof (link_linkorder _ _ _ Hsk2) as [Hsk2a Hsk2b].
  edestruct link_prog_inv as [Hm1 [Hd1 H1]]. apply Hsk1.
  edestruct link_prog_inv as [Hm2 [Hd2 H2]]. apply Hsk2.
  destruct Hcom as (A & B & C & D). cbn in *.
  repeat apply conj.
  - eapply Genv.valid_for_linkorder; eauto.
  - eapply Genv.valid_for_linkorder; eauto.
  - intros. exploit C; eauto.
    eapply in_names_linkorder. apply Hsk1b. eauto.
    intro Hsk2id. apply AST.prog_defmap_dom in Hsk2id as Hsk2id'.
    destruct Hsk2id' as [g2 FIND2].
    apply AST.prog_defmap_dom in H as Hsk1bid'.
    destruct Hsk1bid' as [g1b FIND1b].
    destruct (Maps.PTree.get id (AST.prog_defmap (sk1a))) eqn:FIND1a.
    ++ (*id is public, thus l1b -> l2b*)          
      apply link_prog_inv in Hsk1 as INV1. destruct INV1 as ( _ & PUB &  _) .
      exploit PUB; eauto. intros (PUB1a & PUB1b & LINKg).
      clear - Hleb PUB1b H.
      edestruct AST.prog_defmap_dom as [g FIND1b]. apply H.
      eapply Memory.Mem.in_map_fst_2.
      eapply AST.in_prog_defmap.
      destruct Hleb as (_ & Hp & _).
      eapply Hp; eauto.
    ++
      assert (~ In id (AST.prog_defs_names (sk2a))).
      { intro. edestruct AST.prog_defmap_dom as [g FIND2a]. eauto.
      destruct Hlea as [HH _]. exploit HH; eauto.
      intro. congruence. }
      edestruct in_names_link_or. apply Hsk2. eauto.
      congruence. eauto.
  - destruct Hsk1b. rewrite H. eauto.
Qed.
        
  Lemma compose_simulation' {li1 li2} (cc: callconv' li1 li2) L1a L1b L1 L2a L2b L2:
  forward_simulation' cc cc L1a L2a ->
  forward_simulation' cc cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  forward_simulation' cc cc L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  set (L1 := fun i:bool => if i then L1a else L1b).
  set (L2 := fun i:bool => if i then L2a else L2b).
  assert (HL: forall i, fsim_components' cc cc (L1 i) (L2 i)) by (intros [|]; auto).
  constructor.
  eapply Forward_simulation' with (order cc L1 L2 HL) (match_states cc L1 L2 HL).
  - destruct Ha, Hb. cbn.
    eapply skel_le_compose; eauto.
  - intros se1 se2 w Hse Hse1.
    eapply semantics_simulation; eauto.
    generalize (fsim_skel' Ha). intro Hlea.
    generalize (fsim_skel' Hb). intro Hleb.
    intros [|].
    eapply compatible_link1; eauto.
    eapply compatible_link2; eauto.
  - clear - HL. intros [i x].
    induction (fsim_order_wf' (HL i) x) as [x Hx IHx].
    constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
Qed.
