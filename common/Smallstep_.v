Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface_.
Require Import Integers.
Require Import Smallstep.
Require Import AST.

Set Implicit Arguments.

Record internal state: Type := {
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  globalenv: genvtype;
}.

Record external liA liB state: Type := {
  initial_state: query liB -> state -> Prop;
  at_external: state -> query liA -> Prop;
  after_external: state -> reply liA -> state -> Prop;
  final_state: state -> reply liB -> Prop;
}.

Record lts liA liB state: Type := {
  steps :> (ident -> Prop) -> internal state;
  events :> external liA liB state;
}.

(* Record lts liA liB state: Type := { *)
(*   genvtype: Type; *)
(*   step : genvtype -> state -> trace -> state -> Prop; *)
(*   footprint: ident -> Prop; *)
(*   initial_state: query liB -> state -> Prop; *)
(*   at_external: state -> query liA -> Prop; *)
(*   after_external: state -> reply liA -> state -> Prop; *)
(*   final_state: state -> reply liB -> Prop; *)
(*   globalenv: genvtype; *)
(* }. *)

Record semantics liA liB := {
  skel: AST.program unit unit;
  state: Type;
  activate :> Genv.symtbl -> lts liA liB state;
  footprint: ident -> Prop;
}.

Definition valid_query {li liA liB} (L: semantics liA liB) se (q: query li): Prop :=
  exists i, footprint L i /\ Genv.symbol_address se i Ptrofs.zero = entry q.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : smallstep_scope.

Section FSIM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
  Context {state1 state2: Type}.
  Context {qset: ident -> Prop}.

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
      forall s1 t s1', Step (L1 qset) s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
          (Plus (L2 qset) s2 t s2' \/ (Star (L2 qset) s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments fsim_properties : clear implicits.

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
  forall s1 t s1', Step (L1 qset) s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus (L2 qset) s2 t s2' \/ (Star (L2 qset) s2 t s2' /\ order s1' s1))
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
  forall s1 t s1', Step (L1 qset) s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus (L2 qset) s2 t s2' /\ match_states s1' s2')
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
  forall s1 t s1', Step (L1 qset) s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus (L2 qset) s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step (L1 qset) s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step (L2 qset) s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

End FORWARD_SIMU_DIAGRAMS.

End FSIM.

Arguments fsim_properties {_ _} _ {_ _} _ _ _ _ {_ _} _ L1 L2 index order match_states.

Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_match_states: _;

    fsim_skel:
      skel L1 = skel L2;
    fsim_footprint:
      forall i, footprint L1 i <-> footprint L2 i;
    fsim_lts se1 se2 wB qset:
      @match_senv liB1 liB2 ccB wB se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties ccA ccB se1 se2 wB qset (activate L1 se1) (activate L2 se2)
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
  - intros (i & Hi & Hx). exists i; split.
    + erewrite <- fsim_footprint; eauto.
    + erewrite <- match_senv_symbol_address; eauto.
  - intros (i & Hi & Hx). exists i; split.
    + erewrite fsim_footprint; eauto.
    + erewrite match_senv_symbol_address; eauto.
Qed.
