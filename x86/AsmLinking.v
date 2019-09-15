Require Import AST.
Require Import Coqlib.
Require Import Integers.
Require Import Globalenvs.
Require Import Memory.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.
Require Import SmallstepLinking.
Require Import Values.
Require Import Asmgenproof0.
Require Import Asm.


Lemma find_def_linkorder se (p p': program) b gd:
  linkorder p p' ->
  Genv.find_def (Genv.globalenv se p) b = Some gd ->
  exists gd',
    Genv.find_def (Genv.globalenv se p') b = Some gd' /\
    linkorder gd gd'.
Proof.
Admitted.

Lemma find_funct_ptr_linkorder se (p p': program) b fd:
  Genv.find_funct_ptr (Genv.globalenv se p) b = Some fd ->
  linkorder p p' ->
  exists fd',
    Genv.find_funct_ptr (Genv.globalenv se p') b = Some fd' /\
    linkorder fd fd'.
Proof.
  intros. unfold Genv.find_funct_ptr in *; cbn in *.
  destruct (Genv.find_def (Genv.globalenv se p)) eqn:Hf; try discriminate.
  edestruct find_def_linkorder as (fd' & Hfd & Hlo); eauto. rewrite Hfd.
  destruct g; try discriminate. inv Hlo. inv H. eauto.
Qed.

Lemma find_internal_ptr_linkorder se (p p': program) b f:
  Genv.find_funct_ptr (Genv.globalenv se p) b = Some (Internal f) ->
  linkorder p p' ->
  Genv.find_funct_ptr (Genv.globalenv se p') b = Some (Internal f).
Proof.
  intros. edestruct find_funct_ptr_linkorder as (? & ? & ?); eauto.
  inv H2. eauto.
Qed.

Lemma find_funct_linkorder se (p p': program) vf fd:
  Genv.find_funct (Genv.globalenv se p) vf = Some fd ->
  linkorder p p' ->
  exists fd',
    Genv.find_funct (Genv.globalenv se p') vf = Some fd' /\
    linkorder fd fd'.
Proof.
  intros. unfold Genv.find_funct in *.
  destruct vf; try discriminate.
  destruct Ptrofs.eq_dec; try discriminate.
  eapply find_funct_ptr_linkorder; eauto.
Qed.

Lemma find_internal_linkorder se (p p': program) vf f:
  Genv.find_funct (Genv.globalenv se p) vf = Some (Internal f) ->
  linkorder p p' ->
  Genv.find_funct (Genv.globalenv se p') vf = Some (Internal f).
Proof.
  intros. unfold Genv.find_funct in *.
  destruct vf; try discriminate.
  destruct Ptrofs.eq_dec; try discriminate.
  eapply find_internal_ptr_linkorder; eauto.
Qed.

Section FOO.
  Context (p1 p2 p: program) (Hp: link p1 p2 = Some p).
  (*Context L (HL: link (semantics p1) (semantics p2) = Some L).*)

  Let p_ i := match i with true => p1 | false => p2 end.
  Let L i := semantics (p_ i).

  Lemma p_linkorder i:
    linkorder (p_ i) p.
  Proof.
    apply link_linkorder in Hp as [? ?].
    destruct i; cbn; auto.
  Qed.

  Lemma leb_refl b:
    leb b b.
  Proof.
    destruct b; cbn; auto.
  Qed.

  Lemma leb_true b:
    leb b true.
  Proof.
    destruct b; cbn; auto.
  Qed.

  Hint Resolve p_linkorder leb_refl leb_true.

  Section SE.
    Context (se: Genv.symtbl) (init_nb: block).

    (** ** Simulation relation *)

    (** The following predicate asserts that the composite
      semantics' activation stack is well-formed, with a given
      top-level "inner block" threshold. This threshold is the
      initial value of [Mem.nextblock] for the current activation.
      ... *)

    Inductive match_stack : list (frame L se) -> block -> Prop :=
      | match_stack_top :
          match_stack nil init_nb
      | match_stack_cons i (q: query li_asm) S s b :
          match_stack s (Mem.nextblock (snd q)) ->
          Ple (Mem.nextblock (snd q)) b ->
          match_stack (st L se i q S :: s) b.

    Lemma match_stack_nextblock k b:
      match_stack k b ->
      Ple init_nb b.
    Proof.
      induction 1; xomega.
    Qed.

    (** Liveness of the current component vs. whole program.
      Most of the time, the currently executing component and
      the whole program will both be running. They can also
      simultaneously reach a final state, in which case the
      composed semantics will unwind all current activations and
      eventually reach a final state as a whole. However,
      during cross-component returns it is usually the case that
      the currently executing component reaches a final state
      while the whole program is still running (presumably after
      an internal return). This can only happen when the stack
      contains more than one activation, that is when the current
      component's "inner block" threshold is strictly greater
      than the whole program one.

      The definition below formalizes these cases. *)

    Inductive match_liveness (nb: block) (sp: val): bool -> bool -> Prop :=
      | match_liveness_refl live:
          match_liveness nb sp live live
      | match_liveness_return:
          inner_sp nb sp = false ->
          inner_sp init_nb sp = true ->
          match_liveness nb sp false true.

    Lemma match_inner_sp nb sp:
      Ple init_nb nb ->
      match_liveness nb sp (inner_sp nb sp) (inner_sp init_nb sp).
    Proof.
      intros Hnb. unfold inner_sp. destruct sp; try constructor.
      repeat destruct plt; eauto using match_liveness_refl; try xomega.
      constructor; cbn; destruct plt; auto; xomega.
    Qed.

    Hint Constructors match_liveness.
    Hint Resolve match_inner_sp.

    (** To match the state of the composite semantics with that
      of the whole program, we require that the activation stack
      be well-formed, that liveness follow the above discipline,
      and that the top-level state be otherwise equal to the
      whole-program state. *)

    Inductive match_states : list (frame L se) -> Asm.state -> Prop :=
      | match_states_intro i q k (rs: regset) m live1 live2 :
          match_stack k (Mem.nextblock (snd q)) ->
          match_liveness (Mem.nextblock (snd q)) rs#SP live1 live2 ->
          Ple (Mem.nextblock (snd q)) (Mem.nextblock m) ->
          leb (inner_sp init_nb rs#SP) live2 ->
          match_states (st L se i q (State rs m live1) :: k) (State rs m live2).

    (** ** Simulation properties *)

    (** *** [exec_instr] *)

    Lemma exec_load_nextblock nb chunk m a rs rd rs' m' live:
      exec_load se chunk m a rs rd = Next' rs' m' live ->
      Ple nb (Mem.nextblock m) ->
      Ple nb (Mem.nextblock m').
    Proof.
      unfold exec_load. destruct Mem.loadv; congruence.
    Qed.

    Lemma exec_load_live b chunk m a rs rd rs' m' live:
      exec_load se chunk m a rs rd = Next' rs' m' live ->
      leb b live.
    Proof.
      intros. cut (live = true); [intro; subst; auto | ].
      unfold exec_load in *. destruct Mem.loadv; congruence.
    Qed.

    Lemma exec_store_nextblock nb chunk m a rs rd lr rs' m' live:
      exec_store se chunk m a rs rd lr = Next' rs' m' live ->
      Ple nb (Mem.nextblock m) ->
      Ple nb (Mem.nextblock m').
    Proof.
      unfold exec_store, Mem.storev.
      destruct eval_addrmode; try discriminate.
      destruct Mem.store eqn:Hm'; inversion 1; clear H; subst.
      apply Mem.nextblock_store in Hm'. congruence.
    Qed.

    Lemma exec_store_live b chunk m a rs rd lr rs' m' live:
      exec_store se chunk m a rs rd lr = Next' rs' m' live ->
      leb b live.
    Proof.
      intros. cut (live = true); [intro; subst; auto using leb_true | ].
      unfold exec_store in *. destruct Mem.storev; congruence.
    Qed.

    Lemma goto_label_nextblock nb f l rs m rs' m' live:
      goto_label f l rs m = Next' rs' m' live ->
      Ple nb (Mem.nextblock m) ->
      Ple nb (Mem.nextblock m').
    Proof.
      unfold goto_label.
      destruct label_pos, (rs PC); congruence.
    Qed.

    Lemma goto_label_live b f l rs m rs' m' live:
      goto_label f l rs m = Next' rs' m' live ->
      leb b live.
    Proof.
      intros. cut (live = true); [intro; subst; auto using leb_true | ].
      unfold goto_label in *. destruct label_pos, (rs PC); congruence.
    Qed.

    Hint Resolve
      exec_load_nextblock exec_store_nextblock goto_label_nextblock
      exec_load_live exec_store_live goto_label_live.

    Lemma exec_instr_match nb f instr rs m rs' m' live:
      Ple init_nb nb ->
      Ple nb (Mem.nextblock m) ->
      exec_instr nb se f instr rs m = Next' rs' m' live ->
      exists live',
        exec_instr init_nb se f instr rs m = Next' rs' m' live' /\
        match_liveness nb rs'#SP live live' /\
        Ple nb (Mem.nextblock m') /\
        leb (inner_sp init_nb (rs' RSP)) live'.
    Proof.
      intros Hnb Hm H.
      destruct instr; cbn in H |- *;
      repeat
        lazymatch type of H with
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          | Stuck = _ => inv H
          | Next' _ _ _ = _ => inv H
        end;
      eauto 10 using match_liveness_refl.
      - (* Pallocframe *)
        apply Mem.nextblock_store in Heqo0. rewrite Heqo0.
        apply Mem.nextblock_store in Heqo. rewrite Heqo.
        apply Mem.nextblock_alloc in Heqp0. rewrite Heqp0.
        eexists. intuition (eauto; xomega).
      - (* Pfreeframe *)
        apply Mem.nextblock_free in Heqo1. rewrite Heqo1.
        eexists. intuition (eauto; xomega).
    Qed.

    (** *** [step] *)

    Lemma step_match i nb rs m live1 live2 live1' t rs' m':
      step nb (Genv.globalenv se (p_ i)) (State rs m live1) t (State rs' m' live1') ->
      match_liveness nb rs#SP live1 live2 ->
      Ple init_nb nb ->
      Ple nb (Mem.nextblock m) ->
      exists live2',
        step init_nb (Genv.globalenv se p) (State rs m live2) t (State rs' m' live2') /\
        Ple nb (Mem.nextblock m') /\
        match_liveness nb rs'#SP live1' live2' /\
        leb (inner_sp init_nb rs'#SP) live2'.
    Proof.
      intros H Hlive Hnb Hm. inv H; inv Hlive; subst.
      - (* instruction *)
        eapply find_internal_ptr_linkorder in H8; eauto.
        edestruct exec_instr_match as (? & ? & ? & ? & ?); eauto.
        eauto 10 using exec_step_internal.
      - (* builtin *)
        eapply find_internal_ptr_linkorder in H8; eauto. cbn in *.
        exists true. intuition eauto using exec_step_builtin.
        apply Events.external_call_nextblock in H11. xomega.
      - (* external *)
        assert (Genv.find_funct_ptr (Genv.globalenv se p) b = Some (External ef)).
        {
          edestruct find_funct_ptr_linkorder as (fd & Hfd & Hlo); eauto.
          destruct ef; try contradiction; inv Hlo; auto.
        }
        replace (Pregmap.set _ _ _ RSP) with rs#SP
          by (destruct ef_sig, sig_res as [[]|]; reflexivity).
        eexists. intuition eauto using exec_step_external.
        apply Events.external_call_nextblock in H10. xomega.
    Qed.

  End SE.

  Lemma foo:
    open_fsim cc_id cc_id
      (SmallstepLinking.semantics L (erase_program p))
      (semantics p).
  Proof.
    split; [reflexivity | ]. cbn.
    intros [ ] se _ q _ Hse1 _ [ ] [ ].
    set (ms := match_states se (Mem.nextblock (snd q))).
    eapply forward_simulation_star with ms (@length _); cbn.
    - (* initial states *)
      intros s1 Hs1. destruct Hs1 as [i S Hq HS]. cbn in *.
      exists S. destruct HS. split.
      + econstructor; eauto using find_internal_linkorder.
      + econstructor; cbn; eauto.
        * econstructor.
        * constructor.
        * reflexivity.
    - (* final states *)
      intros _ _ r [i qi k rs m l1 l2 Hk Hl Hb Hsp] Hr; inv Hr.
      inv H4. inv Hk. inv Hl.
      + eexists; split; eauto. constructor.
      + congruence.
    - (* external states *)
      intros _ _ qx [i qi k rs m l1 l2 Hk Hl Hb Hsp] Hqx; inv Hqx; cbn in *.
      exists tt, qx. repeat apply conj; auto.
      + inv H4. edestruct find_funct_linkorder as (? & ? & ?); eauto. inv H0.
        * inv Hl. econstructor; eauto.
        * admit. (* excluded by valid_query *)
      + intros r _ s' [ ] Hs'. inv Hs'. cbn in *. inv H7.
        eexists. split. econstructor.
        econstructor; eauto.
        * eapply match_inner_sp.
          eapply match_stack_nextblock; eauto.
        * admit. (* nextblock vs. external *)
    - (* simulation *)
      intros s1 t s1' Hstep1 s2 Hs. red in Hs.
      destruct Hstep1; inv Hs; cbn in *.
      + (* internal step *)
        destruct s' as [rs' m' live1'].
        edestruct step_match as (live2' & Hstep2 & Hs' & Hl' & ?);
          eauto using match_stack_nextblock.
        left. eexists; split; eauto 10 using plus_one.
        constructor; eauto.
      + (* push *)
        inv H. inv H1. eapply find_internal_linkorder in H3; eauto.
        left. exists (State rs m true). split.
        * admit. (* XXX Need to find a measure that works for zero steps here *)
          (* maybe PC points to external block -> +2 *)
        * constructor; cbn; eauto using match_liveness_refl, Ple_refl.
          constructor; eauto.
      + (* pop *)
        right. intuition auto.
        inv H. inv H0. inv H5. inv H7.
        * constructor; eauto using Ple_trans.
          destruct rs#SP; cbn; try constructor.
          destruct plt; try constructor.
          apply match_stack_nextblock in H4.
          cbn in H9. destruct plt. xomega. discriminate H9.
        * constructor; eauto using Ple_trans.
          rewrite <- H0. eapply match_inner_sp, match_stack_nextblock; eauto.
  Admitted.
End FOO.
