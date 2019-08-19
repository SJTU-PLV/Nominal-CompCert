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

Section LINK.
  Context {li} (L1 L2 : Smallstep.open_sem li li).
  Notation L i := (if i:bool then L1 else L2).

  Ltac subst_dep :=
    subst;
    lazymatch goal with
      | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
        apply inj_pair2 in H; subst_dep
      | _ =>
        idtac
    end.

  Section WITH_SE.
    Context (se: Senv.t).

    Variant frame := st (i: bool) (q: query li) (s: Smallstep.state (L i se q)).
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

  Definition semantics: option (open_sem li li) :=
    option_map
      (fun sk =>
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
        |})
      (link (skel L1) (skel L2)).

  Lemma semantics_receptive L:
    open_receptive L1 ->
    open_receptive L2 ->
    semantics = Some L ->
    open_receptive L.
  Proof.
    intros HL1 HL2 HL se q. unfold semantics in HL.
    destruct link as [sk|]; inversion HL; clear HL; subst.
    assert (forall i q, receptive (L i se q) se) by (intros [|]; auto); clear - H.
    constructor; cbn.
    - intros s t1 s1 t2 STEP Ht. destruct STEP.
      + edestruct @sr_receptive as (s2 & Hs2); eauto. 
        eexists. eapply step_internal; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_push; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_pop; eauto.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sr_traces; eauto.
  Qed.

  Lemma semantics_determinate L:
    open_determinate L1 ->
    open_determinate L2 ->
    semantics = Some L ->
    open_determinate L.
  Proof.
    intros HL1 HL2 HL se q. unfold semantics in HL.
    destruct link as [sk|] eqn:Hsk; inversion HL; clear HL; subst.
    assert (forall i q, determinate (L i se q) se) by (intros [|]; auto).
    assert (forall i j q, valid_query (L i) se q -> valid_query (L j) se q -> i = j).
    { intros. destruct i, j; eauto; eelim valid_query_determ; eauto. }
    clear HL1 HL2. constructor; cbn.
    - destruct 1; inversion 1; subst_dep.
      + edestruct (sd_determ (H i q0) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_at_external_nostep; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_at_external_nostep; eauto.
      + destruct (sd_at_external_determ (H i q0) s qx qx0); eauto.
        assert (j0 = j) by eauto; subst.
        destruct (sd_initial_determ (H j qx) s' s'0); eauto.
        intuition auto. constructor.
      + eelim sd_final_noext; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_final_noext; eauto.
      + edestruct (sd_final_determ (H i qx) s r r0); eauto.
        edestruct (sd_after_external_determ (H j q0) sk0 r s' s'0); eauto.
        intuition auto. constructor.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sd_traces; eauto.
    - destruct 1; inversion 1; subst. assert (i0 = i) by eauto; subst.
      edestruct (sd_initial_determ (H i q) s s0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_at_external_nostep; eauto.
      + edestruct (sd_at_external_determ (H i q0) s qx qx0); eauto. eapply H2; eauto.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_after_external_determ (H i q0) s r s' s'0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_final_nostep; eauto.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_determ; eauto.
  Qed.

End LINK.

Instance Linker_open_sem li: Linker (open_sem li li) :=
  {
    link L1 L2 := semantics L1 L2;
    linkorder := open_fsim cc_id cc_id;
  }.
(* Need to prove: identity and composition for fsim,
  fsim between component and linked program. *)    
Admitted.
