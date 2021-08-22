Require Import Maps.
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface_.
Require Import Integers.
Require Import AST.
Require Import Values.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

  Variable genv: Type.
  Variable state: Type.

  (** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

  Variable step: genv -> state -> trace -> state -> Prop.

  (** No transitions: stuck state *)

  Definition nostep (ge: genv) (s: state) : Prop :=
    forall t s', ~(step ge s t s').

  (** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

  Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

  Lemma star_one:
    forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
  Proof.
    intros. eapply star_step; eauto. apply star_refl. traceEq.
  Qed.

  Lemma star_two:
    forall ge s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.
  Proof.
    intros. eapply star_step; eauto. apply star_one; auto.
  Qed.

  Lemma star_three:
    forall ge s1 t1 s2 t2 s3 t3 s4 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
      star ge s1 t s4.
  Proof.
    intros. eapply star_step; eauto. eapply star_two; eauto.
  Qed.

  Lemma star_four:
    forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 ->
      step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
      star ge s1 t s5.
  Proof.
    intros. eapply star_step; eauto. eapply star_three; eauto.
  Qed.

  Lemma star_trans:
    forall ge s1 t1 s2, star ge s1 t1 s2 ->
                   forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
  Proof.
    induction 1; intros.
    rewrite H0. simpl. auto.
    eapply star_step; eauto. traceEq.
  Qed.

  Lemma star_left:
    forall ge s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.
  Proof star_step.

  Lemma star_right:
    forall ge s1 t1 s2 t2 s3 t,
      star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.
  Proof.
    intros. eapply star_trans. eauto. apply star_one. eauto. auto.
  Qed.

  Lemma star_E0_ind:
    forall ge (P: state -> state -> Prop),
      (forall s, P s s) ->
      (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
      forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
  Proof.
    intros ge P BASE REC.
    assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
    eauto.
  Qed.

  (** One or several transitions.  Also known as the transitive closure. *)

  Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

  Lemma plus_one:
    forall ge s1 t s2,
      step ge s1 t s2 -> plus ge s1 t s2.
  Proof.
    intros. econstructor; eauto. apply star_refl. traceEq.
  Qed.

  Lemma plus_two:
    forall ge s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.
  Proof.
    intros. eapply plus_left; eauto. apply star_one; auto.
  Qed.

  Lemma plus_three:
    forall ge s1 t1 s2 t2 s3 t3 s4 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
      plus ge s1 t s4.
  Proof.
    intros. eapply plus_left; eauto. eapply star_two; eauto.
  Qed.

  Lemma plus_four:
    forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
      step ge s1 t1 s2 -> step ge s2 t2 s3 ->
      step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
      plus ge s1 t s5.
  Proof.
    intros. eapply plus_left; eauto. eapply star_three; eauto.
  Qed.

  Lemma plus_star:
    forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
  Proof.
    intros. inversion H; subst.
    eapply star_step; eauto.
  Qed.

  Lemma plus_right:
    forall ge s1 t1 s2 t2 s3 t,
      star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.
  Proof.
    intros. inversion H; subst. simpl. apply plus_one. auto.
    rewrite Eapp_assoc. eapply plus_left; eauto.
    eapply star_right; eauto.
  Qed.

  Lemma plus_left':
    forall ge s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.
  Proof.
    intros. eapply plus_left; eauto. apply plus_star; auto.
  Qed.

  Lemma plus_right':
    forall ge s1 t1 s2 t2 s3 t,
      plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.
  Proof.
    intros. eapply plus_right; eauto. apply plus_star; auto.
  Qed.

  Lemma plus_star_trans:
    forall ge s1 t1 s2 t2 s3 t,
      plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
  Proof.
    intros. inversion H; subst.
    econstructor; eauto. eapply star_trans; eauto.
    traceEq.
  Qed.

  Lemma star_plus_trans:
    forall ge s1 t1 s2 t2 s3 t,
      star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
  Proof.
    intros. inversion H; subst.
    simpl; auto.
    rewrite Eapp_assoc.
    econstructor. eauto. eapply star_trans. eauto.
    apply plus_star. eauto. eauto. auto.
  Qed.

  Lemma plus_trans:
    forall ge s1 t1 s2 t2 s3 t,
      plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
  Proof.
    intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
  Qed.

  Lemma plus_inv:
    forall ge s1 t s2,
      plus ge s1 t s2 ->
      step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
  Proof.
    intros. inversion H; subst. inversion H1; subst.
    left. rewrite E0_right. auto.
    right. exists s3; exists t1; exists (t0 ** t3); split. auto.
    split. econstructor; eauto. auto.
  Qed.

  Lemma star_inv:
    forall ge s1 t s2,
      star ge s1 t s2 ->
      (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
  Proof.
    intros. inv H. left; auto. right; econstructor; eauto.
  Qed.

  Lemma plus_ind2:
    forall ge (P: state -> trace -> state -> Prop),
      (forall s1 t s2, step ge s1 t s2 -> P s1 t s2) ->
      (forall s1 t1 s2 t2 s3 t,
          step ge s1 t1 s2 -> plus ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
          P s1 t s3) ->
      forall s1 t s2, plus ge s1 t s2 -> P s1 t s2.
  Proof.
    intros ge P BASE IND.
    assert (forall s1 t s2, star ge s1 t s2 ->
            forall s0 t0, step ge s0 t0 s1 ->
            P s0 (t0 ** t) s2).
    induction 1; intros.
    rewrite E0_right. apply BASE; auto.
    eapply IND. eauto. econstructor; eauto. subst t. eapply IHstar; eauto. auto.
    intros. inv H0. eauto.
  Qed.

  Lemma plus_E0_ind:
    forall ge (P: state -> state -> Prop),
      (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
      forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
  Proof.
    intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
  Qed.

  (** Counted sequences of transitions *)

  Inductive starN (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s E0 s
  | starN_step: forall n s t t1 s' t2 s'',
      step ge s t1 s' -> starN ge n s' t2 s'' -> t = t1 ** t2 ->
      starN ge (S n) s t s''.

  Remark starN_star:
    forall ge n s t s', starN ge n s t s' -> star ge s t s'.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Remark star_starN:
    forall ge s t s', star ge s t s' -> exists n, starN ge n s t s'.
  Proof.
    induction 1.
    exists O; constructor.
    destruct IHstar as [n P]. exists (S n); econstructor; eauto.
  Qed.

  (** Infinitely many transitions *)

  CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

  Lemma star_forever:
    forall ge s1 t s2, star ge s1 t s2 ->
                  forall T, forever ge s2 T ->
                       forever ge s1 (t *** T).
  Proof.
    induction 1; intros. simpl. auto.
    subst t. rewrite Eappinf_assoc.
    econstructor; eauto.
  Qed.

  (** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

  Variable A: Type.
  Variable order: A -> A -> Prop.

  CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

  Hypothesis order_wf: well_founded order.

  Lemma forever_N_inv:
    forall ge a s T,
      forever_N ge a s T ->
      exists t, exists s', exists a', exists T',
              step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
  Proof.
    intros ge a0. pattern a0. apply (well_founded_ind order_wf).
    intros. inv H0.
    (* star case *)
    inv H1.
    (* no transition *)
    change (E0 *** T2) with T2. apply H with a2. auto. auto.
    (* at least one transition *)
    exists t1; exists s0; exists x; exists (t2 *** T2).
    split. auto. split. eapply forever_N_star; eauto.
    apply Eappinf_assoc.
    (* plus case *)
    inv H1.
    exists t1; exists s0; exists a2; exists (t2 *** T2).
    split. auto.
    split. inv H3. auto.
    eapply forever_N_plus. econstructor; eauto. eauto. auto.
    apply Eappinf_assoc.
  Qed.

  Lemma forever_N_forever:
    forall ge a s T, forever_N ge a s T -> forever ge s T.
  Proof.
    cofix COINDHYP; intros.
    destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
    rewrite R. apply forever_intro with s'. auto.
    apply COINDHYP with a'; auto.
  Qed.

  (** Yet another alternative definition of [forever]. *)

  CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 ->
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

  Lemma forever_plus_inv:
    forall ge s T,
      forever_plus ge s T ->
      exists s', exists t, exists T',
            step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
  Proof.
    intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
    split. auto.
    split. exploit star_inv; eauto. intros [[P Q] | R].
    subst. simpl. auto. econstructor; eauto.
    traceEq.
  Qed.

  Lemma forever_plus_forever:
    forall ge s T, forever_plus ge s T -> forever ge s T.
  Proof.
    cofix COINDHYP; intros.
    destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
    subst. econstructor; eauto.
  Qed.

  (** Infinitely many silent transitions *)

  CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

  (** An alternate definition. *)

  CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 ->
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

  Lemma forever_silent_N_inv:
    forall ge a s,
      forever_silent_N ge a s ->
      exists s', exists a',
          step ge s E0 s' /\ forever_silent_N ge a' s'.
  Proof.
    intros ge a0. pattern a0. apply (well_founded_ind order_wf).
    intros. inv H0.
    (* star case *)
    inv H1.
    (* no transition *)
    apply H with a2. auto. auto.
    (* at least one transition *)
    exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
    exists s0; exists x.
    split. auto. eapply forever_silent_N_star; eauto.
    (* plus case *)
    inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
    exists s0; exists a2.
    split. auto. inv H3. auto.
    eapply forever_silent_N_plus. econstructor; eauto. eauto.
  Qed.

  Lemma forever_silent_N_forever:
    forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
  Proof.
    cofix COINDHYP; intros.
    destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
    apply forever_silent_intro with s'. auto.
    apply COINDHYP with a'; auto.
  Qed.

  (** Infinitely many non-silent transitions *)

  CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

  Lemma star_forever_reactive:
    forall ge s1 t s2 T,
      star ge s1 t s2 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).
  Proof.
    intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
    eapply star_trans; eauto.
    red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
    auto.
  Qed.

End CLOSURES.

(* The footprint of a concrete program is the set of identifiers that correspond
   to internal function definitions. The calls to these functions are not
   allowed to escape to the environment. The definition, together with the valid
   query predicate, is equivalent to old valid query in the definition of LTS *)
Definition footprint_of_program {F G} `{FundefIsInternal F} (p: AST.program F G) (i: ident) : Prop :=
  match (prog_defmap p) ! i with
  | Some def =>
    match def with
    | Gfun f => fundef_is_internal f = true
    | _ => False
    end
  | _ => False
  end.

Lemma footprint_of_program_valid {F G} `{FundefIsInternal F} (p: AST.program F G) se {li} (q: query li):
  (entry q <> Vundef
   /\ exists i : ident, footprint_of_program p i /\ Genv.symbol_address se i Ptrofs.zero = entry q)
  <-> Genv.is_internal (Genv.globalenv se p) (entry q) = true.
Proof.
  split.
  - intros [Hq (i & Hi & Hx)].
    rewrite <- Hx in *. clear Hx.
    unfold Genv.is_internal. unfold Genv.symbol_address in *.
    destruct Genv.find_symbol eqn:Hsymbol; try congruence; cbn.
    destruct Ptrofs.eq_dec; try congruence; cbn.
    unfold Genv.find_funct_ptr.
    rewrite Genv.find_def_spec.
    erewrite Genv.find_invert_symbol; eauto.
    unfold footprint_of_program in Hi.
    destruct ((prog_defmap p) ! i).
    + destruct g; easy.
    + inversion Hi.
  - intros Hx. unfold Genv.is_internal in Hx.
    destruct Genv.find_funct eqn:H1; try congruence.
    unfold Genv.find_funct in H1.
    destruct (entry q) eqn: Hq; try congruence.
    split. intros X. discriminate X.
    destruct (Ptrofs.eq_dec i Ptrofs.zero) eqn: Hi; try congruence.
    clear Hi. subst.
    unfold Genv.find_funct_ptr in H1.
    destruct Genv.find_def eqn: H2; try congruence.
    destruct g eqn: Hf; try congruence. inv H1.
    rewrite Genv.find_def_spec in H2.
    destruct Genv.invert_symbol eqn:H3; try congruence.
    exists i. split.
    + unfold footprint_of_program. now rewrite H2.
    + unfold Genv.symbol_address.
      erewrite Genv.invert_find_symbol; eauto.
Qed.

(* Record internal state genvtype: Type := { *)
(*   step :> genvtype -> state -> trace -> state -> Prop; *)
(* }. *)

(* Record external liA liB state: Type := { *)
(*   initial_state: query liB -> state -> Prop; *)
(*   at_external: state -> query liA -> Prop; *)
(*   after_external: state -> reply liA -> state -> Prop; *)
(*   final_state: state -> reply liB -> Prop; *)
(* }. *)

(* Record lts liA liB state: Type := { *)
(*   genvtype: Type; *)
(*   globalenv: genvtype; *)
(*   steps :> (ident -> Prop) -> internal state genvtype; *)
(*   events :> external liA liB state; *)

(*   steps_monotone: *)
(*     forall (p1 p2: ident -> Prop) ge, (forall i, p2 i -> p1 i) -> *)
(*     forall s t s', steps p1 ge s t s' -> steps p2 ge s t s'; *)
(* }. *)

Record lts liA liB state: Type := {
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: query liB -> state -> Prop;
  at_external: state -> query liA -> Prop;
  after_external: state -> reply liA -> state -> Prop;
  final_state: state -> reply liB -> Prop;
  globalenv: genvtype;
}.

Record semantics liA liB := {
  skel: AST.program unit unit;
  state: Type;
  activate :> Genv.symtbl -> lts liA liB state;
  footprint: ident -> Prop;
}.

Definition valid_query {li liA liB} (L: semantics liA liB) se (q: query li): Prop :=
  entry q <> Vundef /\
  exists i, footprint L i /\ Genv.symbol_address se i Ptrofs.zero = entry q.

Class ProgramSem {liA liB} (L: semantics liA liB) :=
  {
    incoming_query_valid:
      forall se s q, initial_state (L se) q s -> valid_query L se q;
    outgoing_query_invalid:
      forall se s q, at_external (L se) s q -> ~ valid_query L se q;
  }.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1, L at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1, L at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1, L at level 1) : smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1, L at level 1) : smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1, L at level 1) : smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1, L at level 1) : smallstep_scope.

Open Scope smallstep_scope.

Notation Semantics_gen step initial_state at_ext after_ext final_state globalenv p :=
  {|
  skel := AST.erase_program p;
  activate se :=
    let ge := globalenv se p in
    {|
      step := step;
      initial_state := initial_state ge;
      at_external := at_ext ge;
      after_external := after_ext ge;
      final_state := final_state ge;
      globalenv := ge;
    |};
    footprint := footprint_of_program p;
  |}.

Section FSIM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
  Context {state1 state2: Type}.

  (** The general form of a forward simulation. *)

  Record fsim_properties (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
         (order: index -> index -> Prop)
         (match_states: index -> state1 -> state2 -> Prop) : Prop := {
    fsim_match_initial_states:
      forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists s2, initial_state L2 q2 s2 /\ match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r1, match_states i s1 s2 -> final_state L1 s1 r1 ->
      exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2;
    fsim_match_external:
      forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
      exists w q2, at_external L2 s2 q2 /\ match_query ccA w q1 q2 /\ match_senv ccA w se1 se2 /\
      forall r1 r2 s1', match_reply ccA w r1 r2 -> after_external L1 s1 r1 s1' ->
      exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2';
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
      (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments fsim_properties : clear implicits.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall i s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  intros. exploit @fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.

Variable match_states: state1 -> state2 -> Prop.

Hypothesis match_initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists s2, initial_state L2 q2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r1, match_states s1 s2 -> final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.

Hypothesis match_external:
  forall s1 s2 q1, match_states s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states s1' s2'.

Let ms idx s1 s2 := idx = s1 /\ match_states s1 s2.

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf:
  fsim_properties L1 L2 state1 order ms.
Proof.
  subst ms;
  constructor.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
  exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H. edestruct match_external as (w & q2 & H2 & Hq & Hw & Hr); eauto.
  exists w, q2. intuition auto. edestruct Hr as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star_wf.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.

Lemma simulation_plus:
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

End SIMULATION_SEQUENCES.

End FSIM.

Arguments fsim_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_match_states: _;

    fsim_skel:
      skel L1 = skel L2;
    fsim_footprint:
      forall i, footprint L1 i <-> footprint L2 i;
    fsim_lts se1 se2 wB:
      @match_senv liB1 liB2 ccB wB se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
        fsim_index fsim_order (fsim_match_states se1 se2 wB);
    fsim_order_wf:
      well_founded fsim_order;
  }.

Arguments Forward_simulation {_ _ ccA _ _ ccB L1 L2 fsim_index}.

Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
  inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

Lemma match_valid_query {liA liA' liB liB' li li'} cc1 cc2
      (L1: semantics liA liB) (L2: semantics liA' liB')
      (cc: callconv li li') w se1 se2 q1 q2:
  forward_simulation cc1 cc2 L1 L2 ->
  match_senv cc w se1 se2 ->
  match_query cc w q1 q2 ->
  valid_query L1 se1 q1 <-> valid_query L2 se2 q2.
Proof.
  intros [] Hse Hq. split.
  - intros [? (i & Hi & Hx)]. split.
    erewrite <- match_query_defined; eauto.
    exists i; split.
    + erewrite <- fsim_footprint; eauto.
    + erewrite <- match_senv_symbol_address; eauto.
  - intros [? (i & Hi & Hx)]. split.
    erewrite match_query_defined; eauto.
    exists i; split.
    + erewrite fsim_footprint; eauto.
    + erewrite match_senv_symbol_address; eauto.
Qed.

(** ** Identity simulation *)

Definition identity_fsim_components {liA liB} (L: semantics liA liB):
  fsim_components cc_id cc_id L L.
Proof.
  eapply Forward_simulation with _ (fun _ _ _ => _); auto.
  - firstorder.
  - intros se _ [ ] [ ] _.
    eapply forward_simulation_plus with (match_states := eq);
    cbn; intros; subst; eauto 10 using plus_one.
    exists tt, q1. intuition (subst; eauto).
  - apply well_founded_ltof.
Qed.

Lemma identity_forward_simulation {liA liB} (L: semantics liA liB):
  forward_simulation cc_id cc_id L L.
Proof.
  constructor. apply identity_fsim_components.
Qed.

(** ** Composing two forward simulations *)

Section COMPOSE_FORWARD_SIMULATIONS.

Context {liA1 liA2 liA3} {ccA12: callconv liA1 liA2} {ccA23: callconv liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv liB1 liB2} {ccB23: callconv liB2 liB3}.
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (L3: semantics liA3 liB3).

Lemma compose_fsim_components:
  fsim_components ccA12 ccB12 L1 L2 ->
  fsim_components ccA23 ccB23 L2 L3 ->
  fsim_components (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se3 '(se2, w, w') (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se2 w (snd i) s1 s2 /\
             match_states' se2 se3 w' (fst i) s2 s3).
  apply Forward_simulation with ff_order ff_match_states.
  4: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { congruence. }
  1: { firstorder. }
  intros se1 se3 [[se2 w] w'] (Hse12 & Hse23) Hse1. cbn in *.
  assert (Hse2: Genv.valid_for (skel L2) se2).
  { rewrite <- Hsk. eapply match_senv_valid_for; eauto. }
  constructor.
(* - (* valid query *) *)
(*   intros q1 q3 (q2 & Hq12 & Hq23). *)
(*   erewrite fsim_match_valid_query by eauto. *)
(*   eapply fsim_match_valid_query; eauto. *)
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3; auto.
Qed.

Lemma compose_forward_simulations:
  forward_simulation ccA12 ccB12 L1 L2 ->
  forward_simulation ccA23 ccB23 L2 L3 ->
  forward_simulation (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components; auto.
Qed.

End COMPOSE_FORWARD_SIMULATIONS.

(** * Receptiveness and determinacy *)

Definition single_events {liA liB st} (L: lts liA liB st) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record lts_receptive {liA liB st} (L: lts liA liB st) se: Prop :=
  Receptive {
      sr_receptive: forall s t1 s1 t2,
        Step L s t1 s1 -> match_traces se t1 t2 -> exists s2, Step L s t2 s2;
      sr_traces:
        single_events L
    }.

Record lts_determinate {liA liB st} (L: lts liA liB st) se: Prop :=
  Determinate {
      sd_determ: forall s t1 s1 t2 s2,
        Step L s t1 s1 -> Step L s t2 s2 ->
        match_traces se t1 t2 /\ (t1 = t2 -> s1 = s2);
      sd_traces:
        single_events L;
      sd_initial_determ: forall q s1 s2,
          initial_state L q s1 -> initial_state L q s2 -> s1 = s2;
      sd_at_external_nostep: forall s q,
          at_external L s q -> Nostep L s;
      sd_at_external_determ: forall s q1 q2,
          at_external L s q1 -> at_external L s q2 -> q1 = q2;
      sd_after_external_determ: forall s r s1 s2,
          after_external L s r s1 -> after_external L s r s2 -> s1 = s2;
      sd_final_nostep: forall s r,
          final_state L s r -> Nostep L s;
      sd_final_noext: forall s r q,
          final_state L s r -> at_external L s q -> False;
      sd_final_determ: forall s r1 r2,
          final_state L s r1 -> final_state L s r2 -> r1 = r2
    }.

Section DETERMINACY.

  Context {liA liB st} (L: lts liA liB st) (se: Genv.symtbl).
  Hypothesis DET: lts_determinate L se.

  Lemma sd_determ_1:
    forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 -> match_traces se t1 t2.
  Proof.
    intros. eapply sd_determ; eauto.
  Qed.

  Lemma sd_determ_2:
    forall s t s1 s2,
      Step L s t s1 -> Step L s t s2 -> s1 = s2.
  Proof.
    intros. eapply sd_determ; eauto.
  Qed.

  Lemma sd_determ_3:
    forall s t s1 s2,
      Step L s t s1 -> Step L s E0 s2 -> t = E0 /\ s1 = s2.
  Proof.
    intros. exploit (sd_determ DET). eexact H. eexact H0.
    intros [A B]. inv A. auto.
  Qed.

  Lemma star_determinacy:
    forall s t s', Star L s t s' ->
    forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
  Proof.
    induction 1; intros.
    auto.
    inv H2.
    right. eapply star_step; eauto.
    exploit sd_determ_1. eexact H. eexact H3. intros MT.
    exploit (sd_traces DET). eexact H. intros L1.
    exploit (sd_traces DET). eexact H3. intros L2.
    assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try omegaContradiction.
    destruct t0. inv MT. destruct t0; simpl in L2; try omegaContradiction.
    simpl in H5. split. congruence. congruence.
    destruct H1; subst.
    assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
    auto.
  Qed.

End DETERMINACY.

Definition receptive {liA liB} (L: semantics liA liB) :=
  forall se, lts_receptive (L se) se.

Definition determinate {liA liB} (L: semantics liA liB) :=
  forall se, lts_determinate (L se) se.
