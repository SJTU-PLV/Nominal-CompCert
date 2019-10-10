Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.
Require Export Smallstep.

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import CKLRAlgebra.
Require Import Extends.
Require Import Inject.
Require Import InjectNeutral.
Require Import InjectFootprint.

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

Definition ccref {li1 li2} (cc cc': callconv li1 li2) :=
  forall w q1 q2,
    match_query cc w q1 q2 ->
    exists w',
      match_query cc' w' q1 q2 /\
      forall r1 r2,
        match_reply cc' w' r1 r2 ->
        match_reply cc w r1 r2.

Definition cceqv {li1 li2} (cc cc': callconv li1 li2) :=
  ccref cc cc' /\ ccref cc' cc.

Global Instance ccref_preo li1 li2:
  PreOrder (@ccref li1 li2).
Proof.
  split.
  - intros cc w q1 q2 Hq.
    eauto.
  - intros cc cc' cc'' H' H'' w q1 q2 Hq.
    edestruct H' as (w' & Hq' & Hr'); eauto.
    edestruct H'' as (w'' & Hq'' & Hr''); eauto.
Qed.

Global Instance cceqv_equiv li1 li2:
  Equivalence (@cceqv li1 li2).
Proof.
  split.
  - intros cc.
    split; reflexivity.
  - intros cc1 cc2. unfold cceqv.
    tauto.
  - intros cc1 cc2 cc3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance ccref_po li1 li2:
  PartialOrder (@cceqv li1 li2) (@ccref li1 li2).
Proof.
  firstorder.
Qed.

(** ** Relation to forward simulations *)

(** To prove [forward_simulation_ccref] below, we need the axiom of
  choice. This is because to give the simulation relation [R'] for the
  new forward simulation, we need to extract the target world [w']
  from the existential in our [ccref] hypothesis. *)

Require Import Basics.
Require Import ClassicalChoice.

Inductive matching_query {li1 li2} (cc: callconv li1 li2) :=
  mqi w q1 q2: match_query cc w q1 q2 -> matching_query cc.

Lemma ccref_functional {li1 li2} (cc cc': callconv li1 li2):
  ccref cc cc' ->
  exists (f: matching_query cc -> ccworld cc'),
    forall w q1 q2 (Hq: match_query cc w q1 q2),
      match_query cc' (f (mqi cc w q1 q2 Hq)) q1 q2 /\
      forall r1 r2,
        match_reply cc' (f (mqi cc w q1 q2 Hq)) r1 r2 ->
        match_reply cc w r1 r2.
Proof.
  intros H. red in H.
  set (R := fun '(mqi w q1 q2 Hq) w' =>
         match_query cc' w' q1 q2 /\
         subrel (match_reply cc' w') (match_reply cc w)).
  assert (H': forall Q, exists w', R Q w') by (intros [w q1 q2 Hq]; eauto).
  apply choice in H'.
  destruct H' as (f & Hf).
  exists f.
  intros.
  specialize (Hf (mqi _ w q1 q2 Hq)).
  apply Hf.
Qed.

Global Instance forward_simulation_ccref {liA liB}:
  Monotonic
    (@forward_simulation liA liB)
    (ccref ++> ccref --> subrel).
Proof.
  intros ccA' ccA HA ccB' ccB HB L1 L2.
  apply ccref_functional in HA.
  apply ccref_functional in HB.
  revert HA HB.
  intros [fA HA] [fB HB] [I lt R H].
  set (R' := fun w i s1 s2 =>
               exists q1 q2 (Hq: match_query ccB w q1 q2),
                 R (fB (mqi _ w q1 q2 Hq)) i s1 s2 /\
                 forall r1 r2,
                   match_reply ccB' (fB (mqi _ w q1 q2 Hq)) r1 r2 ->
                   match_reply ccB w r1 r2).
  eexists I lt R'.
  destruct H.
  split; eauto.
  - intros w q1 q2 Hq.
    destruct (HB w q1 q2 Hq) as (Hq' & Hr').
    eapply fsim_match_valid_queries; eauto.
  - intros w q1 q2 Hq s1 Hs1.
    destruct (HB w q1 q2 Hq) as (Hq' & Hr').
    edestruct fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2; intuition eauto.
    exists q1, q2; intuition eauto.
  - intros w i s1 s2 (qB1 & qB2 & HqB & Hs & HrB) q1 Hs1.
    subst R'. simpl in *. edestruct (HB _ _ _ HqB) as [HBq HBr]; eauto.
    edestruct fsim_match_external as (wA' & q2 & Hq & Hs2 & Hr); eauto.
    edestruct (HA _ _ _ Hq) as [HAq HAr]; eauto.
    exists (fA (mqi _ wA' q1 q2 Hq)), q2.
    intuition eauto.
    edestruct Hr as (j & s2' & Hs2' & Hs'); eauto.
    exists j, s2'; intuition eauto.
  - intros w i s1 s2 r1 (q1 & q2 & Hq & Hs & HrB) Hr1.
    edestruct (HB _ _ _ Hq) as [HBq HBr]; eauto.
    edestruct fsim_match_final_states as (r2 & Hr & Hr2); eauto.
  - intros w s1 t s1' Hstep i s2 (q1 & q2 & Hq & Hs & HrB).
    subst R'. simpl in *. edestruct (HB _ _ _ Hq) as [HBq HBr]; eauto.
    edestruct fsim_simulation as (i' & s2' & Hstep' & Hs'); eauto 10.
Qed.

Global Instance forward_simulation_ccref_params:
  Params (@forward_simulation) 4.


(** * Properties of [cc_compose] *)

(** Language interfaces and calling conventions form a category, with
  [cc_id] as the identity arrow and [cc_compose] as the composition. *)

Lemma cc_compose_id_left {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc_id cc) cc.
Proof.
  split.
  - intros [[ ] w] q1 q3 (q2 & Hq12 & Hq23). simpl in *. subst.
    exists w; intuition eauto.
  - intros w q1 q2 Hq.
    exists (tt, w); split.
    + eexists; simpl; eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_id_right {li1 li2} (cc: callconv li1 li2):
  cceqv (cc_compose cc cc_id) cc.
Proof.
  split.
  - intros [w [ ]] q1 q3 (q2 & Hq12 & Hq23). simpl in *. subst.
    exists w; intuition eauto.
  - intros w q1 q2 Hq.
    exists (w, tt); split.
    + eexists; simpl; eauto.
    + intros r1 r3 (r2 & Hr12 & Hr23); simpl in *.
      congruence.
Qed.

Lemma cc_compose_assoc {A B C D} cc1 cc2 cc3:
  cceqv
    (@cc_compose A C D (cc_compose cc1 cc2) cc3)
    (@cc_compose A B D cc1 (cc_compose cc2 cc3)).
Proof.
  split.
  - intros [[w1 w2] w3] qa qd (qc & (qb & Hqab & Hqbc) & Hqcd).
    exists (w1, (w2, w3)). simpl in *. unfold rel_compose.
    split; eauto.
    intros ra rd (rb & Hrab & rc & Hrbc & Hrcd); eauto.
  - intros [w1 [w2 w3]] qa qd (qb & Hqab & qc & Hqbc & Hqcd).
    exists ((w1, w2), w3). simpl in *. unfold rel_compose.
    split; eauto.
    intros ra rd (rc & (rb & Hrab & Hrbc) & Hrcd); eauto.
Qed.

(** In addition, composition is monotonic under [cc_ref]. *)

Global Instance cc_compose_ref li1 li2 li3:
  Proper (ccref ++> ccref ++> ccref) (@cc_compose li1 li2 li3).
Proof.
  intros cc12 cc12' H12 cc23 cc23' H23 (w12, w23) q1 q3 (q2 & Hq12 & Hq23).
  simpl in *. unfold rel_compose.
  edestruct (H12 w12 q1 q2 Hq12) as (w12' & Hq12' & H12').
  edestruct (H23 w23 q2 q3 Hq23) as (w23' & Hq23' & H23').
  exists (w12', w23').
  split; eauto.
  intros r1 r3 (r2 & Hr12 & Hr23); eauto.
Qed.

Global Instance cc_compose_eqv li1 li2 li3:
  Proper (cceqv ==> cceqv ==> cceqv) (@cc_compose li1 li2 li3) | 10.
Proof.
  intros cc12 cc12' [H12 H21] cc23 cc23' [H23 H32].
  split; eapply cc_compose_ref; eauto.
Qed.

Global Instance cc_compose_ref_params:
  Params (@cc_compose) 2.


(** * Kleene algebra *)

(** At each language interface [li], we can equip the type of calling
  conventions [callconv li li] with (most of) the structure of a
  Kleene algebra. At the moment, the [match_dummy_query_def]
  requiement on calling conventions prevents us from defining a zero
  element. Otherwise, we largely follow Kozen'94. *)

(** ** Union *)

(** The union of two calling conventions [cc1] and [cc2] is defined
  in such a way that a [ccplus cc1 cc2]-simulation is both a
  [cc1]-simulation and a [cc2]-simulation. *)

Section JOIN.
  Context {li: language_interface}.

  (** *** Definition *)

  Definition copair {A B C} (f: A -> C) (g: B -> C) (x: A + B): C :=
    match x with
      | inl a => f a
      | inr b => g b
    end.

  Definition cc_join (cc1 cc2: callconv li li): callconv li li :=
    {|
      ccworld := ccworld cc1 + ccworld cc2;
      match_senv := copair (match_senv cc1) (match_senv cc2);
      match_query := copair (match_query cc1) (match_query cc2);
      match_reply := copair (match_reply cc1) (match_reply cc2);
    |}.

  (** *** Properties *)

  (** [cc_join] is the least upper bound with respect to [ccref]. *)

  Lemma cc_join_ub_l cc1 cc2:
    ccref cc1 (cc_join cc1 cc2).
  Proof.
    intros w q1 q2 Hq.
    exists (inl w).
    simpl; eauto.
  Qed.

  Lemma cc_join_ub_r cc1 cc2:
    ccref cc2 (cc_join cc1 cc2).
  Proof.
    intros w q1 q2 Hq.
    exists (inr w).
    simpl; eauto.
  Qed.

  Lemma cc_join_lub cc1 cc2 cc:
    ccref cc1 cc ->
    ccref cc2 cc ->
    ccref (cc_join cc1 cc2) cc.
  Proof.
    intros H1 H2 w q1 q2 Hq.
    destruct w; simpl in *; eauto.
  Qed.

  (** The following lemmas are useful as [auto] hints. *)

  Lemma cc_join_l cc cc1 cc2:
    ccref cc cc1 -> ccref cc (cc_join cc1 cc2).
  Proof.
    etransitivity; eauto using cc_join_ub_l.
  Qed.

  Lemma cc_join_r cc cc1 cc2:
    ccref cc cc2 -> ccref cc (cc_join cc1 cc2).
  Proof.
    etransitivity; eauto using cc_join_ub_r.
  Qed.

  (** Trivial consequences of the least upper bound property. *)

  Hint Resolve cc_join_lub cc_join_l cc_join_r (reflexivity (R:=ccref)).
  Hint Unfold cceqv.

  Global Instance cc_join_ref:
    Proper (ccref ++> ccref ++> ccref) cc_join.
  Proof.
    intros cc1 cc1' H1 cc2 cc2' H2; eauto 10.
  Qed.

  Global Instance cc_join_eqv:
    Proper (cceqv ==> cceqv ==> cceqv) cc_join.
  Proof.
    intros cc12 cc12' [H12 H21] cc23 cc23' [H23 H32]; eauto 10.
  Qed.

  Lemma cc_join_assoc cc1 cc2 cc3:
    cceqv (cc_join (cc_join cc1 cc2) cc3) (cc_join cc1 (cc_join cc2 cc3)).
  Proof.
    split; eauto 10.
  Qed.

  Lemma cc_join_comm cc1 cc2:
    cceqv (cc_join cc1 cc2) (cc_join cc2 cc1).
  Proof.
    split; eauto 10.
  Qed.

  Lemma cc_join_idemp cc:
    cceqv (cc_join cc cc) cc.
  Proof.
    split; eauto 10.
  Qed.

  Lemma ccref_join cc1 cc2:
    ccref cc1 cc2 <->
    cceqv (cc_join cc1 cc2) cc2.
  Proof.
    unfold cceqv; intuition.
    transitivity (cc_join cc1 cc2); eauto.
  Qed.

  (** *** Forward simulations *)

  Inductive cc_join_ms {A B C D E F} R1 R2: A + B -> C + D -> E -> F -> Prop :=
    | cc_join_ms_introl a b x y:
        R1 a b x y -> cc_join_ms R1 R2 (inl a) (inl b) x y
    | cc_join_ms_intror a b x y:
        R2 a b x y -> cc_join_ms R1 R2 (inr a) (inr b) x y.

  Hint Constructors cc_join_ms.

  Lemma cc_join_fsim (ccA: callconv li li) ccB1 ccB2 L1 L2:
    forward_simulation ccA ccB1 L1 L2 ->
    forward_simulation ccA ccB2 L1 L2 ->
    forward_simulation ccA (cc_join ccB1 ccB2) L1 L2.
  Proof.
    intros [index1 order1 ms1 H1] [index2 order2 ms2 H2].
    exists (index1 + index2)%type (order1 + order2)%rel (cc_join_ms ms1 ms2).
    split.
    - intros [x|x].
      + induction (fsim_order_wf H1 x).
        constructor. inversion 1. subst. eauto.
      + induction (fsim_order_wf H2 x).
        constructor. inversion 1. subst. eauto.
    - intros [w|w] q1 q2 Hq; simpl in *; eauto using fsim_match_valid_queries.
    - intros [w|w] q1 q2 Hq s1 Hs1; simpl in *.
      edestruct (fsim_match_initial_states H1) as (i & s2 & Hs2 & Hs); eauto.
      edestruct (fsim_match_initial_states H2) as (i & s2 & Hs2 & Hs); eauto.
    - intros _ _ _ _ [w i s1 s2 Hs | w i s1 s2 Hs] q1 Hq1.
      + edestruct (fsim_match_external H1) as (wA & q2 & ? & ? & H); eauto.
        exists wA, q2. intuition auto.
        edestruct H as (j & s2' & Hs2' & Hs'); eauto.
      + edestruct (fsim_match_external H2) as (wA & q2 & ? & ? & H); eauto.
        exists wA, q2. intuition auto.
        edestruct H as (j & s2' & Hs2' & Hs'); eauto.
    - intros _ _ _ _ r1 [w i s1 s2 Hs | w i s1 s2 Hs] Hs1; simpl;
        eauto using fsim_match_final_states.
    - intros w s1 t s1' Hstep1 i s2 Hs.
      destruct Hs as [w i s1 s2 Hs | w i s1 s2 Hs].
      + edestruct (fsim_simulation H1) as (i' & s2' & Hstep2 & Hs'); eauto.
        exists (inl i'), s2'. intuition auto.
        right. split; eauto. constructor; eauto.
      + edestruct (fsim_simulation H2) as (i' & s2' & Hstep2 & Hs'); eauto.
        exists (inr i'), s2'. intuition auto.
        right. split; eauto. constructor; eauto.
    - eauto using fsim_public_preserved.
  Qed.
End JOIN.

Infix "+" := cc_join : cc_scope.

(** ** Superposition *)

(** In addition to the union, we can define a superposition operator
  which requires that both calling conventions are satisfied. This is
  particularly useful with [cc_id] to enforce invariants. *)

Definition cc_both {liA liB} (cc1 cc2: callconv liA liB): callconv liA liB :=
  {|
    ccworld := ccworld cc1 * ccworld cc2;
    match_senv := fun '(w1, w2) => match_senv cc1 w1 /\ match_senv cc2 w2;
    match_query := fun '(w1, w2) => match_query cc1 w1 /\ match_query cc2 w2;
    match_reply := fun '(w1, w2) => match_reply cc1 w1 /\ match_reply cc2 w2;
  |}%rel.

Global Instance cc_both_ref:
  Monotonic (@cc_both) (forallr -, forallr -, ccref ++> ccref ++> ccref).
Proof.
  intros liA liB cc1 cc1' H1 cc2 cc2' H2 [w1 w2] q q' [Hq1 Hq2].
  specialize (H1 w1 q q' Hq1) as (w1' & Hq1' & H1).
  specialize (H2 w2 q q' Hq2) as (w2' & Hq2' & H2).
  exists (w1', w2'). split.
  - split; eauto.
  - intros r r' [Hr1 Hr2].
    split; eauto.
Qed.

Lemma cc_both_assoc {liA liB} (cc1 cc2 cc3: callconv liA liB):
  cceqv (cc_both (cc_both cc1 cc2) cc3) (cc_both cc1 (cc_both cc2 cc3)).
Abort.

Lemma cc_both_comm {liA liB} (cc1 cc2: callconv liA liB):
  cceqv (cc_both cc1 cc2) (cc_both cc2 cc1).
Abort.

Lemma cc_both_idemp {liA liB} (cc: callconv liA liB):
  cceqv (cc_both cc cc) cc.
Abort.

Infix "&&" := cc_both : cc_scope.

(** ** Iteration *)

Require Import KLR.

Section STAR.
  Context {li: language_interface} (cc: callconv li li).

  (** *** Definition *)

  (** We define n-fold self-composition [cc_pow cc n], then use it as
    a base to define [cc_star cc]. This makes it easier to prove that
    self-simulation entails self-simulation by the starred calling
    convention: we first show self-simulation by [cc ^ n] for an
    arbitrary [n]; then with that intermediate result we can reuse
    [compose_forward_simulations], which deals with the complexity of
    composing the general forward simulation diagram, in our proof of
    the [cc_star] simulation. *)

  Fixpoint cc_pow (n: nat): callconv li li :=
    match n with
      | O => cc_id
      | S m => cc @ cc_pow m
    end.

  Definition cc_star: callconv li li :=
    {|
      ccworld := { n : nat & ccworld (cc_pow n) };
      match_senv := fun '(existT n w) => match_senv (cc_pow n) w;
      match_query := fun '(existT n w) => match_query (cc_pow n) w;
      match_reply := fun '(existT n w) => match_reply (cc_pow n) w;
    |}.

  (** *** Properties *)

  Lemma cc_star_fold_l:
    ccref (1 + cc @ cc_star) cc_star.
  Proof.
    intros [[ ] | [w [n ws]]] q1 q2 Hq; simpl in *.
    - exists (existT _ O tt).
      simpl; eauto.
    - exists (existT _ (S n) (w, ws)).
      simpl; eauto.
  Qed.

  Lemma cc_star_fold_r:
    ccref (1 + cc_star @ cc) cc_star.
  Proof.
    intros [[ ] | [[n ws] w]] q1 q3; simpl.
    - intros [ ].
      exists (existT _ O tt). simpl. tauto.
    - intros (q2 & Hqs & Hq).
      revert q1 Hqs.
      induction n as [ | n IHn]; simpl in *; intros.
      + exists (existT _ 1%nat (w, tt)). simpl. subst.
        unfold rel_compose. split; eauto.
        intros r1 r3 (r2 & Hr12 & Hr23). subst. eauto.
      + destruct ws as [w0 ws], Hqs as (qI & Hq1I & HqI2). simpl in *.
        specialize (IHn ws qI HqI2) as ([n' ws'] & HqI3' & ?). clear HqI2.
        exists (existT _ (S n') (w0, ws')). simpl.
        unfold rel_compose. split; eauto.
        intros r1 r3 (r2 & Hr12 & Hr23).
        edestruct H as (rI & Hr1I & HrI2); eauto.
  Qed.

  Lemma cc_id_star:
    ccref 1 cc_star.
  Proof.
    rewrite <- cc_star_fold_r.
    apply cc_join_ub_l.
  Qed.

  Lemma cc_one_star:
    ccref cc cc_star.
  Proof.
    rewrite <- cc_star_fold_r.
    rewrite <- cc_join_ub_r.
    rewrite <- cc_star_fold_r.
    rewrite <- cc_join_ub_l.
    rewrite cc_compose_id_left.
    reflexivity.
  Qed.

  Lemma cc_pow_star n:
    ccref (cc_pow n) cc_star.
  Proof.
    induction n; simpl.
    - apply cc_id_star.
    - rewrite <- cc_star_fold_l.
      rewrite <- cc_join_ub_r.
      rauto.
  Qed.
End STAR.

Infix "^" := cc_pow : cc_scope.
Notation "cc ^{*}" := (cc_star cc) (at level 30) : cc_scope.

Global Instance cc_pow_ref:
  Monotonic (@cc_pow) (forallr -, ccref ++> - ==> ccref).
Proof.
  intros li cc1 cc2 Hcc n.
  induction n; simpl cc_pow; rauto.
Qed.

Global Instance cc_star_ref li:
  Proper (ccref ++> ccref) (@cc_star li).
Proof.
  intros cc cc' Hcc [n ws] q1 q2 Hq.
  destruct (cc_pow_ref li cc cc' Hcc n ws q1 q2 Hq) as (ws' & Hq' & H).
  exists (existT _ n ws'); simpl. eauto.
Qed.

(** *** Proving simulations *)

Lemma cc_pow_fsim_intro {li ccA ccB} (L: semantics li) n:
  forward_simulation ccA ccB L L ->
  forward_simulation (ccA ^ n) (ccB ^ n) L L.
Proof.
  intros HL.
  induction n; simpl.
  - eapply forward_simulation_identity.
  - eapply compose_forward_simulations; eauto.
Qed.

Lemma cc_star_pow_fsim {li ccA ccB} (L: semantics li) n:
  forward_simulation ccA ccB L L ->
  forward_simulation (ccA ^{*}) (ccB ^ n) L L.
Proof.
  intros HL.
  rewrite <- cc_pow_star.
  apply cc_pow_fsim_intro; eauto.
Qed.

(** The lemma proved below is the fundamental way of building
  simulations with a [cc_star] incoming calling convention: if we can
  show a simulation in terms of [cc_pow n] for all [n], then the
  simulation holds for [cc_star] as well. This is simple in principle,
  but somewhat technical to prove, and it requires dependent
  functional choice.

  This could be formulated in terms of strategy refinement instead,
  which would make it both more general and would probably avoid much
  of the complexity. *)

Section CC_POW_STAR_FSIM.
  Context {li} {ccA: callconv li li} {ccB: callconv li li}.
  Context (L1: Smallstep.semantics li).
  Context (L2: Smallstep.semantics li).

  (** We will need to have packaged the components of the simulations
    so as to feed them through our choice axiom. *)

  Record simulation_components {n} :=
    {
      sc_index: Type;
      sc_order: relation sc_index;
      sc_match_states: ccworld (ccB^n) -> sc_index -> rel (state L1) (state L2);
    }.

  Arguments simulation_components : clear implicits.

  Definition simulation_holds n (c: simulation_components n) :=
    fsim_properties ccA (ccB^n) L1 L2 (sc_order c) (sc_match_states c).

  (** We will use [ChoiceFacts.FunctionalDependentChoice] to obtain
    the following data, from which we can construct the composite
    simulation. *)

  Variable (sc: forall n, simulation_components n).
  Hypothesis (Hsc: forall n, simulation_holds n (sc n)).

  (** First, we must define our index type. *)

  Definition pow_star_index :=
    { n: nat & sc_index (sc n) }.

  Inductive pow_star_order: relation pow_star_index :=
    pso_intro n x y:
      sc_order (sc n) x y ->
      pow_star_order (existT _ n x) (existT _ n y).

  Lemma pow_star_order_wf:
    well_founded pow_star_order.
  Proof.
    intros [n i].
    assert (Acc (sc_order (sc n)) i) by eapply fsim_order_wf, Hsc.
    induction H.
    constructor.
    inversion 1; subst.
    eapply H0.
    apply inj_pair2 in H5.
    congruence.
  Qed.

  (** Now we can define the simulation relation and prove its properties. *)

  Inductive pow_star_match: ccworld (ccB^{*}) -> pow_star_index -> rel _ _ :=
    psms_intro n w i s1 s2:
      sc_match_states (sc n) w i s1 s2 ->
      pow_star_match (existT _ n w) (existT _ n i) s1 s2.

  Lemma pow_star_fsim_properties:
    fsim_properties ccA (cc_star ccB) L1 L2 pow_star_order pow_star_match.
  Proof.
    unfold simulation_holds in Hsc.
    split.
    - apply pow_star_order_wf.
    - intros [n w] q1 q2 Hq. simpl in *.
      eauto using fsim_match_valid_queries.
    - intros [n w] q1 q2 Hq s1 Hs1. simpl in *.
      edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
      exists (existT _ n i), s2. split; auto.
      constructor; auto.
    - intros _ _ _ _ [n w i s1 s2 Hs] q1 Hs1.
      edestruct @fsim_match_external as (wA & q2 & Hq & Hs2 & HAE); eauto.
      exists wA, q2. intuition auto.
      edestruct HAE as (j & s2' & Hs2' & Hs'); eauto.
      exists (existT _ n j), s2'. intuition auto.
      constructor; auto.
    - intros _ _ _ _ r1 [n w i s1 s2 Hs] Hs1.
      edestruct @fsim_match_final_states as (r2 & Hr & Hs2); eauto.
      exists r2. simpl. eauto.
    - intros nw s1 t s1' Hstep1 i s2 Hs. destruct Hs as [n w i s1 s2 Hs].
      edestruct @fsim_simulation as (i' & s2' & Hstep2 & Hs'); eauto.
      intuition eauto 10 using pso_intro, psms_intro.
    - specialize (Hsc 0).
      eapply fsim_public_preserved; eauto.
  Qed.
End CC_POW_STAR_FSIM.

Require Import ChoiceFacts.
Axiom AC_dep_fun: DependentFunctionalChoice.

Lemma cc_pow_star_fsim {li ccA ccB} L1 L2:
  (forall n, forward_simulation ccA (ccB ^ n) L1 L2) ->
  @forward_simulation li li ccA (cc_star ccB) L1 L2.
Proof.
  intros HL.
  assert (forall n, exists s, simulation_holds (ccA:=ccA) (ccB:=ccB) L1 L2 n s).
  {
    intros n.
    specialize (HL n) as [index order ms H].
    exists {| sc_order := order; sc_match_states := ms |}.
    eauto.
  }
  clear HL.
  apply AC_dep_fun in H as [sc Hsc].
  econstructor.
  eapply pow_star_fsim_properties; eauto.
Qed.

Lemma cc_star_fsim {li ccA ccB} (L: semantics li):
  forward_simulation ccA ccB L L ->
  forward_simulation (cc_star ccA) (cc_star ccB) L L.
Proof.
  intros HL.
  apply cc_pow_star_fsim. intros n.
  apply cc_star_pow_fsim; eauto.
Qed.


(** * Invariants *)

Require Import Invariant.

(** ** Composition *)

(** Composition of invariant-derived calling conventions is
  essentially the conjunction of the underlying invariants, and as
  such it is commutative and idempotent. *)

Lemma cc_inv_commut {li} (I1 I2: invariant li):
  ccref (I1 @ I2) (I2 @ I1).
Proof.
  intros [xq q] q1 q3 (q2 & (H1 & Hq2 & HqI1) & (H2 & Hq2I & Hq3)).
  simpl in * |- . subst.
  exists (q, q). split; simpl.
  - eexists; eauto 10.
  - intros r _ (_ & [Hr2] & [Hr1]).
    eexists; split; constructor; eauto.
Qed.

Lemma cc_inv_idemp {li} (I: invariant li):
  cceqv (I @ I) I.
Proof.
  split.
  - intros [xq q] q1 q3 (q2 & (H1 & Hq2 & HqI1) & (H2 & Hq2I & Hq3)).
    simpl in * |- . subst.
    exists q. split; simpl; eauto.
    intros r _ [Hr].
    eexists; split; constructor; eauto.
  - intros q q1 q2 (Hq & Hq1 & Hq2). subst.
    exists (q, q). split; simpl.
    + eexists; split; constructor; eauto.
    + intros r _ (_ & [Hr] & [_]).
      constructor; eauto.
Qed.

(** ** Commutation with rectangular diagrams *)

(** Typing is contravariant with injections and extensions. We can use
  such properties to show a partial commutation property with
  rectangular diagrams. Since we need to transport the invariant in
  opposite directions for queries and replies (which, at least for
  typing, we can't), we cannot prove full commutation, however we can
  strengthen the calling convention in the following way. *)

Lemma cc_inv_c_commut I R:
  (forall w q1 q2,
      match_query (cc_c R) w q1 q2 ->
      query_inv I q2 ->
      query_inv I q1) ->
  (forall w q1 q2 r1 r2,
      match_query (cc_c R) w q1 q2 ->
      match_reply (cc_c R) w r1 r2 ->
      query_inv I q1 ->
      query_inv I q2 ->
      reply_inv I q2 r2 ->
      reply_inv I q1 r1) ->
  ccref (cc_c R @ I) (I @ cc_c R @ I).
Proof.
  intros HIq HIr [w q2] q1 qx2 (qxx2 & Hq & Hq1 & Hqx1 & Hqxx1).
  cbn [fst snd] in *. subst.
  exists (q1, (w, q2)). split.
  - simpl. unfold rel_compose. eauto 10.
  - intros r1 r2 (r1I & [Hr1] & r2I & Hr & [Hr2]). cbn [fst snd] in *.
    eexists. cbn [fst snd]. split; eauto.
    constructor; eauto.
Qed.

Lemma wt_c_commut R:
  ccref (cc_c R @ wt_c) (wt_c @ cc_c R @ wt_c).
Proof.
  apply cc_inv_c_commut.
  - intros w _ _ [id sg vargs1 vargs2 m1 m2 Hvargs Hm].
    simpl in *. subst.
    generalize (sig_args sg). revert Hvargs. generalize (mi R w). clear.
    induction 1; simpl in *; intros [ | t ts]; intuition eauto.
    revert H1; rauto.
  - simpl. intros w _ _ r1 r2 [id sg v1 v2 m1 m2 _ _] (f & _ & Hv & _) _ _.
    generalize (proj_sig_res sg). red in Hv. simpl in *.
    clear -Hv. intro. rauto.
Qed.


(** * Composition theorems *)

(* XXX should go to cklr.Inject *)
Global Instance meminj_dom_incr:
  Monotonic (@meminj_dom) (inject_incr ++> inject_incr).
Proof.
  intros f1 f2 Hf b b' delta.
  unfold meminj_dom, inject_incr in *.
  destruct (f1 b) as [[xb xdelta] | ] eqn:H; try discriminate.
  erewrite Hf; eauto.
Qed.

Lemma match_c_query_dom f q1 q2:
  match_c_query inj f q1 q2 ->
  match_c_query inj (meminj_dom f) q1 q1.
Proof.
  intros [id sg vargs1 vargs2 m1 m2 Hargs Hm]; simpl in *.
  constructor; simpl; eauto using block_inject_dom, mem_inject_dom.
  - apply val_inject_list_rel.
    eapply val_inject_list_dom.
    apply val_inject_list_rel.
    eassumption.
  - destruct Hm. split; eauto using mem_inject_dom, meminj_dom_wf.
Qed.

(** ** Rectangular diagrams *)

Lemma match_c_query_compose R12 R23 w12 w23:
  eqrel
    (match_c_query (R12 @ R23) (w12, w23))
    (rel_compose (match_c_query R12 w12) (match_c_query R23 w23)).
Proof.
  split.
  - intros _ _ [id sg vargs1 vargs3 m1 m3 Hvargs Hm].
    simpl in *.
    rewrite val_inject_compose in Hvargs. apply list_rel_compose in Hvargs.
    destruct Hvargs as (vargs2 & Hvargs12 & Hvargs23).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (cq id sg vargs2 m2); split; constructor; simpl; rauto.
  - intros q1 q3 (q2 & Hq12 & Hq23).
    destruct Hq23 as [id sg vargs2 vargs3 m2 m3 Hvargs23 Hm23]. inv Hq12.
    constructor; simpl.
    + rewrite val_inject_compose.
      apply list_rel_compose.
      eexists; split; eauto.
    + eexists; split; eauto.
Qed.

Global Instance cc_c_ref:
  Monotonic (@cc_c) (subcklr ++> ccref).
Proof.
  intros Q R HQR. red in HQR |- *.
  intros w _ _ [id sg vargs1 vargs2 m1 m2 Hvargs Hm].
  specialize (HQR w m1 m2 Hm) as (wr & HmR & Hincr & HQR').
  exists wr.
  simpl in *.
  split.
  - constructor; simpl; rauto.
  - intros [vres1 m1'] [vres2 m2'] (wr' & Hw' & Hvres & Hm'). simpl in *.
    specialize (HQR' wr' m1' m2' Hm' Hw') as (w' & HmQ' & HwQ' & Hincr').
    rauto.
Qed.

Lemma cc_c_compose R12 R23:
  cceqv (cc_c (R12 @ R23)) (cc_c R12 @ cc_c R23).
Proof.
  split.
  - intros [w12 w23] q1 q3 Hq.
    apply match_c_query_compose in Hq.
    exists (w12, w23).
    split; eauto.
    intros [vres1 m1'] [vres3 m3'] ([vres2 m2'] & H12 & H23).
    destruct H12 as (w12' & Hw12' & Hvres12 & Hm12').
    destruct H23 as (w23' & Hw23' & Hvres23 & Hm23').
    simpl in *.
    exists (w12', w23'); split; repeat rstep; simpl.
    + rauto.
    + apply val_inject_compose. eexists; eauto.
    + eexists; eauto.
  - intros [w12 w23] q1 q3 Hq.
    apply match_c_query_compose in Hq.
    simpl in *.
    exists (w12, w23).
    split; eauto.
    intros [vres1 m1'] [vres3 m3'] ([w12' w23'] & [Hw12' Hw23'] & Hvres & Hm').
    red in Hvres. simpl in *.
    apply val_inject_compose in Hvres.
    destruct Hvres as (vres2 & Hvres12 & Hvres23).
    destruct Hm' as (m2' & Hm12' & Hm23').
    exists (vres2, m2'); split; rauto.
Qed.

Lemma flat_inj_wf thr:
  Block.le Block.init thr ->
  meminj_wf (Mem.flat_inj thr).
Proof.
  intros Hthr.
  split.
  - rauto.
  - intros b1 b2 [delta Hb] Hb2.
    unfold Mem.flat_inj in Hb.
    destruct Block.lt_dec; inv Hb.
    auto.
Qed.

Global Instance block_inject_refl:
  Reflexive (block_inject inject_id).
Proof.
  intro.
  exists 0.
  reflexivity.
Qed.

Global Instance mem_extends_refl:
  Reflexive Mem.extends.
Proof.
  intro. apply Mem.extends_refl.
Qed.

Lemma match_c_query_injn_inj nb q1 q2:
  match_c_query injn nb q1 q2 <->
  match_c_query inj (Mem.flat_inj nb) q1 q2 /\
  Mem.nextblock (cq_mem q1) = nb /\
  Mem.nextblock (cq_mem q2) = nb.
Proof.
  split.
  - intros [id sg vargs1 vargs2 m1 m2 Hvargs [Hm Hnb]].
    simpl in *. red in Hnb. destruct Hnb.
    split; eauto.
    constructor; eauto.
  - intros ([id sg v1 v2 m1 m2 Hv Hm] & Hnb1 & Hnb2). simpl in *.
    constructor; simpl; eauto.
    split; eauto.
    red. rewrite Hnb1, Hnb2. constructor.
Qed.

Lemma compose_flat_inj f m1 m2:
  Mem.inject f m1 m2 ->
  compose_meminj (Mem.flat_inj (Mem.nextblock m1)) f = f.
Proof.
  intros Hf.
  apply functional_extensionality; intro b.
  unfold compose_meminj, Mem.flat_inj.
  destruct Block.lt_dec.
  - destruct (f b) as [[b' delta] | ]; eauto.
  - destruct (f b) as [[b' delta] | ] eqn:Hb; eauto.
    elim n. eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma match_c_query_injn_l nb q1 q2:
  match_c_query injn nb q1 q2 ->
  match_c_query injn nb q1 q1.
Proof.
  intros Hq.
  apply match_c_query_injn_inj in Hq.
  destruct Hq as (Hq & Hnb & _).
  apply match_c_query_injn_inj.
  split; eauto.
  rewrite <- meminj_dom_flat_inj.
  eapply match_c_query_dom; eauto.
Qed.

(** * Locset languages *)

Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Allocproof.

(** ** [cc_alloc] *)

(** *** Commutation with rectangular diagrams *)

(** In the following, we seek to prove that [cc_alloc] commutes with
  arbitrary rectangular CKLR diagrams. Since the memory components are
  equal under [cc_alloc], this part of the proof is easy. The
  challenge is to show that the way arguments are encoded into
  registers is compatible with the commutation property.

  More precisely, we seek to prove the property
  [ccref (cc_c R @ cc_alloc) (cc_alloc @ cc_locset R)]. This means
  that given arguments [args1] injecting into [args2], where the
  [args2] are read from the location set [rs2], we need to give
  a location set [rs1], such that the [args1] can be read from [rs1],
  and [rs1] injects into [rs2].

  To that end, we are going to start from a fully-undefined location
  set [Locmap.init Vundef], and write the [args1] into it one by one.
  To prove that the result injects into [rs2], we will essentially
  rewrite the arguments read from [rs2] into [rs2] itself: the result
  will be less defined than [rs2], and by monotonicity we will know
  that [rs1] injects into it, and therefore into [rs2]. *)

(** The first step is to define a version of [Locmap.setpair] able to
  access stack locations. *)

Definition setlpair (p: rpair loc) (v: val) (rs: Locmap.t) :=
  match p with
    | One l =>
      Locmap.set l v rs
    | Twolong hi lo =>
      Locmap.set lo (Val.loword v) (Locmap.set hi (Val.hiword v) rs)
  end.

(** Thankfully, the "memory effects" of stack locations will at most
  yield an undefined value (but no integer conversions), so that we
  don't need to know the types of arguments. *)

Lemma val_load_result_chunk_of_type ty v:
  Val.lessdef (Val.load_result (chunk_of_type ty) v) v.
Proof.
  destruct ty, v; constructor.
Qed.

Lemma locmap_set_get_lessdef r v ls1 ls2:
  Val.lessdef v (ls2 r) ->
  (forall l, Val.lessdef (ls1 l) (ls2 l)) ->
  (forall l, Val.lessdef (Locmap.set r v ls1 l) (ls2 l)).
Proof.
  intros Hv Hls l.
  unfold Locmap.set.
  destruct Loc.eq; subst.
  - destruct l; eauto.
    eapply Val.lessdef_trans with v; eauto.
    eapply val_load_result_chunk_of_type.
  - destruct Loc.diff_dec; eauto.
Qed.

Global Instance locmap_set_lessdef:
  Monotonic
    (@Locmap.set)
    (- ==> Val.lessdef ++> (- ==> Val.lessdef) ++> - ==> Val.lessdef) | 10.
Proof.
  unfold Locmap.set. repeat rstep; auto using Val.load_result_lessdef.
Qed.

Global Instance locmap_set_inject f:
  Monotonic
    (@Locmap.set)
    (- ==> Val.inject f ++> (- ==> Val.inject f) ++> - ==> Val.inject f).
Proof.
  unfold Locmap.set. rauto.
Qed.

Global Instance locmap_setpair_inject f:
  Monotonic
    (@Locmap.setpair)
    (- ==> Val.inject f ++> (- ==> Val.inject f) ++> - ==> Val.inject f).
Proof.
  unfold Locmap.setpair. repeat rstep.
  destruct x; repeat rstep. (* XXX coqrel *)
Qed.

Global Instance setlpair_inject f:
  Monotonic
    (@setlpair)
    (- ==> Val.inject f ++> (- ==> Val.inject f) ++> - ==> Val.inject f).
Proof.
  unfold setlpair. repeat rstep.
  destruct x; repeat rstep. (* XXX coqrel *)
Qed.

Lemma locmap_setlpair_getpair_lessdef p ls1 ls2 v:
  Val.lessdef v (Locmap.getpair p ls2) ->
  (forall l, Val.lessdef (ls1 l) (ls2 l)) ->
  (forall l, Val.lessdef (setlpair p v ls1 l) (ls2 l)).
Proof.
  intros Hv Hls.
  unfold setlpair, Locmap.getpair.
  destruct p; simpl in *.
  - intros l.
    eapply Val.lessdef_trans with (Locmap.set r v ls2 l).
    + repeat rstep; eauto.
    + eapply locmap_set_get_lessdef; eauto.
  - intros l.
    eapply locmap_set_get_lessdef.
    * eapply Val.lessdef_trans, val_loword_longofwords.
      eauto using Val.loword_lessdef.
    * eapply locmap_set_get_lessdef; eauto.
      eapply Val.lessdef_trans, val_hiword_longofwords.
      eauto using Val.hiword_lessdef.
Qed.

Lemma locmap_setlpair_getpair_inject f v1 rs1 rs2 p:
  Val.inject f v1 (Locmap.getpair p rs2) ->
  (forall l, Val.inject f (rs1 l) (rs2 l)) ->
  (forall l, Val.inject f (setlpair p v1 rs1 l) (rs2 l)).
Proof.
  intros Hv Hrs l.
  eapply Mem.val_inject_lessdef_compose.
  - repeat rstep; eauto.
  - eapply locmap_setlpair_getpair_lessdef; eauto.
Qed.

(** Now, we can define a function for writing the complete list of
  arguments, and the associated property we need. *)

Fixpoint setlpairs (locs: list (rpair loc)) (args: list val) (rs: Locmap.t) :=
  match locs, args with
    | l::locs, v::args => setlpairs locs args (setlpair l v rs)
    | _, _ => rs
  end.

Lemma setlpairs_getpairs_inject f vs1 rs1 rs2 locs:
  list_rel (Val.inject f) vs1 (map (fun p => Locmap.getpair p rs2) locs) ->
  (forall l, Val.inject f (rs1 l) (rs2 l)) ->
  (forall l, Val.inject f (setlpairs locs vs1 rs1 l) (rs2 l)).
Proof.
  revert vs1 rs1.
  induction locs; intros vs1 rs1 Hvs Hrs; inv Hvs; simpl; eauto.
  eapply IHlocs; eauto.
  eapply locmap_setlpair_getpair_inject; eauto.
Qed.

(** The new intermediate register set can be obtained by starting from
  a fully [Vundef] state and writing arguments. *)

Definition rs_of_args (sg: signature) (args: list val) :=
  setlpairs (loc_arguments sg) args (Locmap.init Vundef).

Lemma rs_of_args_inject sg f args1 args2 rs2:
  list_rel (Val.inject f) args1 args2 ->
  args2 = map (fun p => Locmap.getpair p rs2) (loc_arguments sg) ->
  forall l, Val.inject f (rs_of_args sg args1 l) (rs2 l).
Proof.
  intros Hargs Hargs2. subst args2.
  unfold rs_of_args.
  eapply setlpairs_getpairs_inject; eauto.
Qed.

Global Instance getpair_inject f:
  Monotonic (@Locmap.getpair) (- ==> (- ==> Val.inject f) ++> Val.inject f).
Proof.
  unfold Locmap.getpair. rauto.
Qed.

Global Instance return_regs_inject f:
  Monotonic
    (@return_regs)
    ((- ==> Val.inject f) ++> (- ==> Val.inject f) ++> - ==> Val.inject f).
Proof.
  unfold return_regs. rauto.
Qed.

(* XXX a version is defined in Stackingproof, except for [ls1].
  We should make sure the direction in which agree_callee_save is used
  is consistent across CompCert, and also that the Stackingproof
  version of this lemma does not gratuitously depend on section
  variables, so that we can reuse it. *)
Lemma agree_callee_save_set_result:
  forall sg v ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save ls1 (Locmap.setpair (loc_result sg) v ls2).
Proof.
  intros; red; intros. rewrite Locmap.gpo. apply H; auto.
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; simpl; auto. congruence. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

Lemma loc_result_pair' sg rlo rhi:
  loc_result sg = Twolong rlo rhi ->
  sig_res sg = Some Tlong /\
  Loc.diff (R rhi) (R rlo) /\
  Archi.splitlong = true.
Proof.
  intros H. pose proof (loc_result_pair sg) as Hsg. rewrite H in Hsg.
  intuition auto. cbn. auto.
Qed.

Lemma locmap_getpair_setpair sg v ls:
  Val.has_type v (proj_sig_res sg) ->
  Locmap.getpair
    (map_rpair R (loc_result sg))
    (Locmap.setpair (loc_result sg) v ls) = v.
Proof.
  intros Hv.
  unfold setlpair, Locmap.getpair.
  destruct loc_result eqn:Hlr; simpl.
  - apply Locmap.gss.
  - edestruct loc_result_pair' as (Hres & Hdiff & Hsplit); eauto.
    rewrite Locmap.gss.
    rewrite Locmap.gso, Locmap.gss; eauto.
    eapply val_longofwords_eq_2; eauto.
    unfold proj_sig_res in Hv.
    rewrite Hres in Hv.
    assumption.
Qed.

Lemma locmap_setpair_getpair_lessdef p ls1 ls2 v:
  Val.lessdef v (Locmap.getpair (map_rpair R p) ls2) ->
  (forall l, Val.lessdef (ls1 l) (ls2 l)) ->
  (forall l, Val.lessdef (Locmap.setpair p v ls1 l) (ls2 l)).
Proof.
  intros Hv Hls.
  unfold Locmap.setpair, Locmap.getpair.
  destruct p; simpl in *.
  - intros l.
    eapply Val.lessdef_trans with (Locmap.set (R r) v ls2 l).
    + repeat rstep; eauto.
    + eapply locmap_set_get_lessdef; eauto.
  - intros l.
    eapply locmap_set_get_lessdef.
    * eapply Val.lessdef_trans, val_loword_longofwords.
      eauto using Val.loword_lessdef.
    * eapply locmap_set_get_lessdef; eauto.
      eapply Val.lessdef_trans, val_hiword_longofwords.
      eauto using Val.hiword_lessdef.
Qed.
