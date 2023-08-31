Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Require Import Callconv.

Set Implicit Arguments.

Section FSIM'.

Context {liA1 liA2} (ccA: callconv' liA1 liA2).
Context {liB1 liB2} (ccB: callconv' liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld' ccB).
Context {state1 state2: Type}.

(** The general form of a forward simulation. *)

Record fsim_properties' (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop) : Prop := {
    fsim_match_valid_query':
      forall q1 q2, match_query' ccB wB q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    fsim_match_initial_states':
      forall q1 q2 s1, match_query' ccB wB q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists s2, initial_state L2 q2 s2 /\ match_states i s1 s2;
    fsim_match_final_states':
      forall i s1 s2 r1, match_states i s1 s2 -> final_state L1 s1 r1 ->
      exists r2, final_state L2 s2 r2 /\ match_reply' ccB wB r1 r2;
    fsim_match_external':
      forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
      exists w q2, at_external L2 s2 q2 /\ match_query' ccA w q1 q2 /\ match_senv' ccA w se1 se2 /\
      forall r1 r2 s1', match_reply' ccA w r1 r2 -> after_external L1 s1 r1 s1' ->
      exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2';
    fsim_simulation_1:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments fsim_properties' : clear implicits.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation'_1:
  forall L1 L2 index order match_states, fsim_properties' L1 L2 index order match_states ->
  forall i s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  intros. exploit @fsim_simulation_1; eauto.
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

Hypothesis match_valid_query:
  forall q1 q2, match_query' ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis match_initial_states:
  forall q1 q2 s1, match_query' ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists s2, initial_state L2 q2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r1, match_states s1 s2 -> final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_reply' ccB wB r1 r2.

Hypothesis match_external:
  forall s1 s2 q1, match_states s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query' ccA wA q1 q2 /\ match_senv' ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply' ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states s1' s2'.

Let ms idx s1 s2 := idx = s1 /\ match_states s1 s2.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

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

Lemma forward_simulation_star_wf':
  fsim_properties' L1 L2 state1 order ms.
Proof.
  subst ms;
  constructor.
- auto.
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

Lemma forward_simulation_star':
  fsim_properties' L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star_wf'.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus':
  fsim_properties' L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star'.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step':
  fsim_properties' L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus'.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt':
  fsim_properties' L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star'.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: fsim_properties' L1 L2 index order match_states).

Lemma simulation_star':
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation_1; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.

Lemma simulation_plus':
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'_1; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'_1; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star'. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

Lemma simulation_forever_silent':
  well_founded order ->
  forall i s1 s2,
  Forever_silent L1 s1 -> match_states i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i s1 s2,
          Forever_silent L1 s1 -> match_states i s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation_1 S _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto.
Qed.

Lemma simulation_forever_reactive':
  forall i s1 s2 T,
  Forever_reactive L1 s1 T -> match_states i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star' as [i' [st2' [A B]]]; eauto.
  econstructor; eauto.
Qed.

End SIMULATION_SEQUENCES.

End FSIM'.

Arguments fsim_properties' {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record fsim_components' {liA1 liA2} (ccA: callconv' liA1 liA2) {liB1 liB2} ccB L1 L2 :=
  Forward_simulation' {
    fsim_index': Type;
    fsim_order': fsim_index' -> fsim_index' -> Prop;
    fsim_match_states': _;

    fsim_skel':
      Genv.skel_le (skel L2) (skel L1);
    fsim_lts' se1 se2 wB:
      @match_senv' liB1 liB2 ccB wB se1 se2 ->
      Genv.skel_symtbl_compatible (skel L1) (skel L2) se1 se2 ->
      fsim_properties' ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
        fsim_index' fsim_order' (fsim_match_states' se1 se2 wB);
    fsim_order_wf':
      well_founded fsim_order';
  }.

Arguments Forward_simulation' {_ _ ccA _ _ ccB L1 L2 fsim_index'}.

Definition forward_simulation' {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
  inhabited (@fsim_components' liA1 liA2 ccA liB1 liB2 ccB L1 L2).
(*
Section COMPOSE_FORWARD_SIMULATIONS.

Context {liA1 liA2 liA3} {ccA12: callconv' liA1 liA2} {ccA23: callconv' liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv' liB1 liB2} {ccB23: callconv' liB2 liB3}.
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (L3: semantics liA3 liB3).

Require Import Coq.Program.Equality.

Lemma compose_fsim_components:
  fsim_components' ccA12 ccB12 L1 L2 ->
  fsim_components' ccA23 ccB23 L2 L3 ->
  fsim_components' (cc_compose ccA12 ccA23) (cc_compose ccB12 ccB23) L1 L3.
Proof.
  intros [index order match_states path12 props order_wf].
  intros [index' order' match_states' path23 props' order_wf'].
  set (sk2 := skel L2).
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se2 '(w, w') (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se1 w (snd i) s1 s2 /\
             match_states' se1 se2 w' (fst i) s2 s3).
  apply Forward_simulation'
    with ff_order ff_match_states. etransitivity; eauto.
  2: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  intros se1 se2 [w w'] [Hse1 Hse2] [Hv1 [Hv3 Hcom]]. cbn in *.
  assert (COMPAT1: Genv.skel_symtbl_compatible (skel L1) (skel L2) se1 se1).
  {
    constructor. eauto. split.
    - clear - Hv1 path12.
      red in Hv1. red. intros.
      eapply Hv1. clear - path12 H.
      inv path12. eauto.
    - clear - Hv1. red in Hv1.
      split. intros.
      edestruct AST.prog_defmap_dom as [g A]. eauto.
      exploit Hv1; eauto.
      intros (b & g' & B & C & D). 
      intro. destruct H as [g [A B]]. congruence.
      destruct Hcom as [A B].
      split.
      intros. inv path23.
      exploit A; eauto.
  }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query by eauto.
  eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2. eexists. eexists. all: auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & x & y & HH & A & B).
  edestruct PATH_EQ as [X Y]; eauto. subst.
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as (s3 & x & y & HH & A & B).
  edestruct PATH_EQ as [X Y]; eauto. subst.
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  { constructor; eauto. }
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'. eexists. eexists. all : eauto.
- (* simulation *)
  intros. destruct H0 as (s3 & x & y & HH & A & B).
  edestruct PATH_EQ as [X Y]; eauto. subst.
  destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'. eexists. eexists. all: eauto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'. eexists. eexists. all: auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3. eexists. eexists. auto.
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
*)
