Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Import Values Maps Memory AST.

Set Implicit Arguments.

Lemma E0_split : forall x y, E0 = x ** y -> x = E0 /\ y = E0.
Proof.
  unfold E0, Eapp. intros. split.
  destruct x; auto. simpl in H. discriminate.
  destruct y; auto. exfalso. apply (app_cons_not_nil _ _ _ H).
Qed.

Lemma open_bsim_simulation' {index state1 state2 liA1 liB1 liA2 liB2}:
  forall
    {L1 : lts liA1 liB1 state1} {L2 : lts liA2 liB2 state2}
    {match_states: index -> state1 -> state2 -> Prop} {order},
  (forall s2 t s2', Step L2 s2 t s2' ->
   forall i s1, match_states i s1 s2 -> safe L1 s1 ->
   exists i', exists s1',
      (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
   /\ match_states i' s1' s2') ->
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 E0 s1'
  /\ match_states i' s1' s2'.
Proof.
  intros until i. revert i. remember E0 as t. induction H0; simpl; intros.
  exists i, s1. split; eauto. constructor.
  subst t.
  specialize (H _ _ _ H0 _ _ H3 H4) as (i'' & s & ST & MS).
  apply E0_split in H2 as []. subst.
  assert (Star L1 s0 E0 s). {
    destruct ST.
    inv H. apply E0_split in H6 as []. subst. eapply star_trans; eauto.
    econstructor. exact H2.
    econstructor. unfold E0, Eapp. rewrite app_nil_r. reflexivity.
    tauto. tauto.
  } clear ST.
  eapply star_safe in H4; eauto.
  specialize (IHstar ltac:(auto) _ _ MS H4) as (i' & s1' & ST & MS').
  exists i', s1'. split; auto. eapply star_trans; eauto.
Qed.

Lemma open_progress' {index state1 state2 liA1 liB1 liA2 liB2}:
  forall
    {L1 : lts liA1 liB1 state1} {L2 : lts liA2 liB2 state2}
    {match_states: index -> state1 -> state2 -> Prop} {order},
  (forall i s1 s2,
   match_states i s1 s2 -> safe L1 s1 ->
   (exists r, final_state L2 s2 r) \/
   (exists q, at_external L2 s2 q) \/
   (exists t, exists s2', Step L2 s2 t s2')) ->
  (forall s2 t s2', Step L2 s2 t s2' ->
   forall i s1, match_states i s1 s2 -> safe L1 s1 ->
   exists i', exists s1',
      (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
   /\ match_states i' s1' s2') ->
  forall i s1 s2,
  match_states i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros. unfold safe. intros. revert i s1 H1 H2.
  remember E0 as t.
  induction H3; simpl; intros. eauto. subst t.
  apply E0_split in H2 as []. subst.
  exploit H0; eauto. intros (i' & s1' & ST & MS).
  eapply IHstar. auto. exact MS.
  assert (Star L1 s0 E0 s1'). {
    destruct ST.
    inv H2. apply E0_split in H8 as []. subst. eapply star_trans; eauto.
    econstructor. exact H6.
    econstructor. assert (E0 = E0 ** E0) by auto. exact H2. auto.
    tauto.
  } clear ST.
  eapply star_safe; eauto.
Qed.

Module Closed.

(* Definitions. *)

Record semantics := ClosedSemantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> int -> Prop;
  globalenv: genvtype;
  symbolenv: Genv.symtbl
}.

Declare Scope closed_smallstep_scope.

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

Variable step: genv -> state -> trace -> state -> Prop.

Variable final_state: state -> int -> Prop.

Inductive eventually (ge: genv): nat -> state -> (state -> Prop) -> Prop :=
  | eventually_now: forall s (P: state -> Prop),
      P s ->
      eventually ge O s P
  | eventually_later: forall n s (P: state -> Prop),
      (forall r, ~ final_state s r) ->
      (forall t s', step ge s t s' -> t = E0 /\ eventually ge n s' P) ->
      eventually ge (S n) s P.

Lemma eventually_one: forall ge s (P: state -> Prop),
  (forall r, ~ final_state s r) ->
  (forall t s', step ge s t s' -> t = E0 /\ P s') ->
  eventually ge 1%nat s P.
Proof.
  intros. apply eventually_later; auto. intros.
  apply H0 in H1.
  intuition auto using eventually.
Qed.

Lemma eventually_trans: forall ge n1 s1 P1 n2 P2,
  eventually ge n1 s1 P1 -> 
  (forall s2, P1 s2 -> eventually ge n2 s2 P2) ->
  eventually ge (n1 + n2)%nat s1 P2.
Proof.
  intros. revert n1 s1 H. induction n1; intros s1 EV; inv EV; simpl.
- apply H0; assumption.
- apply eventually_later; auto. intros t s' ST. destruct (H2 t s' ST) as [U V]. auto.
Qed.

Corollary eventually_implies: forall ge n s (P1 P2: state -> Prop),
  eventually ge n s P1 ->
  (forall s, P1 s -> P2 s) ->
  eventually ge n s P2.
Proof.
  intros. replace n with (n + 0)%nat by lia. eapply eventually_trans; eauto using eventually_now.
Qed.

Lemma eventually_and_invariant: forall ge (Inv: state -> Prop) n s P,
  (forall s t s', step ge s t s' -> Inv s -> Inv s') ->
  eventually ge n s P -> Inv s ->
  eventually ge n s (fun s' => P s' /\ Inv s').
Proof.
  intros. revert n s H0 H1. induction n; intros s EV IV; inv EV.
- apply eventually_now. auto.
- apply eventually_later; auto. intros. edestruct H2; eauto. 
Qed.

End CLOSURES.
          
Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Eventually' L " := (eventually (step L) (final_state L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Open Scope closed_smallstep_scope.


Record fsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    fsim_order_wf: well_founded order;
    fsim_match_initial_states:
      forall s1, initial_state L1 s1 ->
      exists i, exists s2, initial_state L2 s2 /\ match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
    fsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: index -> state L1 -> state L2 -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall i s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  apply Forward_simulation with order (fun idx s1 s2 => idx = s1 /\ match_states s1 s2);
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
- auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
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

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
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

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  apply forward_simulation_plus.
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

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with measure.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.


(** ** Forward simulation with the "eventually" modality *)

(** A forward simulation diagram where the first semantics can take some extra steps
    before reaching a state that restores the simulation relation. *)

Section FORWARD_SIMU_EVENTUALLY.

Variable L1: semantics.
Variable L2: semantics.
Variable index: Type.
Variable order: index -> index -> Prop.
Variable match_states: index -> state L1 -> state L2 -> Prop.

Hypothesis order_wf: well_founded order.
Hypothesis initial_states:
  forall s1, initial_state L1 s1 ->
  exists i, exists s2, initial_state L2 s2 /\ match_states i s1 s2.
Hypothesis final_states:
  forall i s1 s2 r,
    match_states i s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists n i' s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
     /\ Eventually L1 n s1' (fun s1'' => match_states i' s1'' s2').

Hypothesis public_preserved:
  forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id.

Lemma forward_simulation_eventually: forward_simulation L1 L2.
Proof.
  apply @Forward_simulation with
    (index := (index * nat)%type)
    (order := lex_ord order Nat.lt)
    (match_states := fun i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => match_states (fst i) s1'' s2)).
  constructor.
- apply wf_lex_ord; auto using lt_wf.
- intros. exploit initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; auto using eventually_now.
- intros [i n] s1 s2 r EV FS; simpl in *. inv EV.
  + eapply final_states; eauto.
  + eelim H; eauto.
- intros s1 t s1' ST [i n] s2 EV; simpl in *. inv EV.
  + exploit simulation; eauto. intros (n & i' & s2' & A & B).
    exists (i', n), s2'; split; auto.
    destruct A as [P | [P Q]]; auto using lex_ord_left.
  + apply H0 in ST. destruct ST as (A & B). subst t.
    exists (i, n0), s2; split.
    right; split. apply star_refl. apply lex_ord_right; lia.
    exact B.
- apply public_preserved.
Qed.

End FORWARD_SIMU_EVENTUALLY.

(** Two simplified diagrams. *)

Section FORWARD_SIMU_EVENTUALLY_SIMPL.

Variable L1: semantics.
Variable L2: semantics.
Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis public_preserved:
  forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id.
Hypothesis initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.
Hypothesis final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r.

(** Simplified "plus" simulation diagram, when L2 always makes at least one transition. *)

Section FORWARD_SIMU_EVENTUALLY_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists n s2',
     Plus L2 s2 t s2'
  /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2').

Lemma forward_simulation_eventually_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_eventually with (order := lt) (match_states := fun i s1 s2 => match_states s1 s2).
- apply lt_wf.
- intros. exploit initial_states; eauto. intros (s2 & A & B). exists O, s2; auto.
- intros. eapply final_states; eauto.
- intros. exploit simulation; eauto. intros (n & s2' & A & B).
  exists n, O, s2'; auto.
- auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_PLUS.

(** Simplified "star" simulation diagram, with a decreasing, well-founded order on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR_WF.

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1)) /\ match_states s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2')).

Lemma forward_simulation_eventually_star_wf: forward_simulation L1 L2.
Proof.
  apply @Forward_simulation with
    (index := (nat * state L1)%type)
    (order := lex_ord Nat.lt order)
    (match_states := fun i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states s1'' s2)).
  constructor; intros.
- apply wf_lex_ord; auto using lt_wf.
- exploit initial_states; eauto. intros (s2 & A & B).
  exists (O, s1), s2; auto using eventually_now.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + eapply final_states; eauto.
  + eelim H; eauto.
- destruct i as [n s11]; destruct H0 as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit simulation; eauto. intros [(s2' & A & B) | (n & s2' & A & B)].
    * exists (O, s1'), s2'; split. 
      destruct A as [A | [A1 A2]]; auto using lex_ord_right.
      auto using eventually_now.
    * exists (n, s1'), s2'; auto.
  + apply H1 in H. destruct H. subst t.
    exists (n0, s1'), s2; split.
    right; split. apply star_refl. apply lex_ord_left; lia.
    auto.
- auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR_WF.

(** Simplified "star" simulation diagram, with a decreasing measure on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1' < measure s1))%nat
        /\ match_states s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2')).

Lemma forward_simulation_eventually_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_eventually_star_wf with (ltof _ measure).
- apply well_founded_ltof.
- exact simulation.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR.

End FORWARD_SIMU_EVENTUALLY_SIMPL.

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
  right; exists i'; intuition auto with sets.
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

Lemma simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L1 s1 -> match_states i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i s1 s2,
          Forever_silent L1 s1 -> match_states i s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto. eapply fsim_order_wf; eauto.
Qed.

Lemma simulation_forever_reactive:
  forall i s1 s2 T,
  Forever_reactive L1 s1 T -> match_states i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star as [i' [st2' [A B]]]; eauto.
  econstructor; eauto.
Qed.

End SIMULATION_SEQUENCES.

(** ** Composing two forward simulations *)

Lemma compose_forward_simulations:
  forall L1 L2 L3, forward_simulation L1 L2 -> forward_simulation L2 L3 -> forward_simulation L1 L3.
Proof.
  intros L1 L2 L3 S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].

  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states := fun (i: ff_index) (s1: state L1) (s3: state L3) =>
                             exists s2, match_states (snd i) s1 s2 /\ match_states' (fst i) s2 s3).
  apply Forward_simulation with ff_order ff_match_states; constructor.
- (* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans.
  eapply fsim_order_wf; eauto. eapply fsim_order_wf; eauto.
- (* initial states *)
  intros. exploit (fsim_match_initial_states props); eauto. intros [i [s2 [A B]]].
  exploit (fsim_match_initial_states props'); eauto. intros [i' [s3 [C D]]].
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. destruct H as [s3 [A B]].
  eapply (fsim_match_final_states props'); eauto.
  eapply (fsim_match_final_states props); eauto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' props); eauto. intros [[i1' [s3' [C D]]] | [i1' [C [D E]]]].
+ (* L2 makes one or several steps. *)
  exploit simulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P [Q R]]]].
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
- (* symbols *)
  intros. transitivity (Genv.public_symbol (symbolenv L2) id); eapply fsim_public_preserved; eauto.
Qed.

(** * Receptiveness and determinacy *)

Definition single_events (L: semantics) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

Section DETERMINACY.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (symbolenv L) t1 t2.
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
    destruct t1; simpl in L1; try extlia.
    destruct t0. inv MT. destruct t0; simpl in L2; try extlia.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.

(** Extra simulation diagrams for determinate languages. *)

Section FORWARD_SIMU_DETERM.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis L1det: determinate L1.

Variable index: Type.
Variable order: index -> index -> Prop.
Hypothesis wf_order: well_founded order.

Variable match_states: index -> state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists i s2, initial_state L2 s2 /\ match_states i s1 s2.

Hypothesis match_final_states:
  forall i s1 s2 r,
  match_states i s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists s1'' i' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
   /\ match_states i' s1'' s2'.

Hypothesis public_preserved:
  forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id.

Lemma star_match_eventually:
  forall s1 s1', Star L1 s1 E0 s1' ->
  forall i s2, match_states i s1' s2 ->
  exists n, Eventually L1 n s1 (fun s1'' => match_states i s1'' s2).
Proof.
  intros s10 s10' STAR0. pattern s10, s10'; eapply star_E0_ind; eauto.
  - intros s1 i s2 M. exists O; constructor; auto.
  - intros s1 s1' s1'' STEP IH i s2 M.
    destruct (IH i s2 M) as (n & MS).
    exists (S n); constructor.
    + intros; red; intros. eapply (sd_final_nostep L1det); eauto.
    + intros. exploit (sd_determ_3 L1det). eexact H. eexact STEP. intros [A B].
      subst t s'. auto.
Qed.

Lemma forward_simulation_determ: forward_simulation L1 L2.
Proof.
  apply forward_simulation_eventually with (order := order) (match_states := match_states); auto.
  intros. exploit simulation; eauto. intros (s1'' & i' & s2' & A & B & C).
  exploit star_match_eventually; eauto. intros (n & D).
  exists n, i', s2'; auto.
Qed.

End FORWARD_SIMU_DETERM.

(** A few useful special cases. *)

Section FORWARD_SIMU_DETERM_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis L1det: determinate L1.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis public_preserved:
  forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

Section SIMU_DETERM_STAR.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1'' < measure s1))%nat
   /\ match_states s1'' s2'.

Lemma forward_simulation_determ_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ with
    (match_states := fun i s1 s2 => i = s1 /\ match_states s1 s2)
    (order := ltof _ measure).
- assumption.
- apply well_founded_ltof.
- intros. exploit match_initial_states; eauto. intros (s2 & A & B). 
  exists s1, s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H0; subst i. 
  exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s1'', s2'. auto.
- assumption.
Qed.

End SIMU_DETERM_STAR.

Section SIMU_DETERM_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Plus L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ_star with (measure := fun _ => O).
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto.
Qed.

End SIMU_DETERM_PLUS.

Section SIMU_DETERM_ONE.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Step L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_one: forward_simulation L1 L2.
Proof.
  apply forward_simulation_determ_plus.
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto using plus_one.
Qed.

End SIMU_DETERM_ONE.

End FORWARD_SIMU_DETERM_DIAGRAMS.

Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id
  }.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Arguments Backward_simulation {L1 L2 index} order match_states props.


(* Closing open semantics. *)

Section CLOSE_SEMANTICS.

Variable liA liB : language_interface.
Variable query : query liB.
Variable reply : int -> reply liB -> Prop.
Variable s : Smallstep.semantics liA liB.
Variable se : Genv.symtbl.

Definition close_semantics :=
  let lts := Smallstep.activate s se in
  {|
    state := Smallstep.state s;
    genvtype := Smallstep.genvtype lts;
    step := Smallstep.step lts;
    initial_state := Smallstep.initial_state lts query;
    final_state := fun state retval => exists r, reply retval r /\ Smallstep.final_state lts state r;
    globalenv := Smallstep.globalenv lts;
    symbolenv := se;
  |}.

End CLOSE_SEMANTICS.

Section CLOSE_SOUND.

Variable liA1 liB1 : language_interface.
Variable query1 : query liB1.
Variable reply1 : int -> reply liB1 -> Prop.
Variable s1 : Smallstep.semantics liA1 liB1.
Variable se1 : Genv.symtbl.
Definition lts1 := (Smallstep.activate s1 se1).
Definition L1 := close_semantics query1 reply1 s1 se1.

Variable liA2 liB2 : language_interface.
Variable query2 : query liB2.
Variable reply2 : int -> reply liB2 -> Prop.
Variable s2 : Smallstep.semantics liA2 liB2.
Variable se2 : Genv.symtbl.
Definition lts2 := (Smallstep.activate s2 se2).
Definition L2 := close_semantics query2 reply2 s2 se2.

Variable ccA : callconv liA1 liA2.
Variable ccB : callconv liB1 liB2.

Hypothesis Hvalid : Genv.valid_for (skel s1) se1.

Variable wB : ccworld ccB.

Hypothesis Hmatch_query : match_query ccB wB query1 query2.
Hypothesis Hmatch_senv : match_senv ccB wB se1 se2.

Section FORWARD.

Hypothesis Hmatch_reply_forward : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply1 r r1 -> reply2 r r2.

Lemma close_sound_forward :
  Smallstep.forward_simulation ccA ccB s1 s2 -> forward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.forward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (fsim_lts se1 se2 wB Hmatch_senv Hvalid). inv fsim_lts.
  unfold L1, L2, close_semantics.
  do 2 econstructor; simpl; eauto.

  (* match final state *)
  intros i s1' s2' r MS (r1 & R1 & FINAL).
  exploit fsim_match_final_states0; eauto. intros (r2 & FINAL' & MATCH_REPLY).
  eexists. split; eauto.
  eapply match_senv_public_preserved; eauto.
Qed.

End FORWARD.

Section BACKWARD.

Lemma safe_sound_1:
  forall s, safe L1 s -> Smallstep.safe lts1 s.
Proof.
  unfold safe, Smallstep.safe, L1, lts1, close_semantics. simpl. intros.
  specialize (H _ H0) as [(r & r0 & REPLY & FS)|(t & s'' & STEP)]; eauto.
Qed.

Hypothesis closed2 : forall s q, Smallstep.safe lts2 s -> ~ at_external lts2 s q.
Hypothesis reply_sound2: forall s r, Smallstep.final_state lts2 s r -> exists i, reply2 i r.
Hypothesis Hmatch_reply_backward : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply2 r r2 -> reply1 r r1.

Lemma close_sound_backward:
  Smallstep.backward_simulation ccA ccB s1 s2 -> backward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.backward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (bsim_lts se1 se2 wB Hmatch_senv Hvalid).
  inv bsim_lts.
  unfold L1, L2, close_semantics.
  specialize (bsim_match_initial_states0 _ _ Hmatch_query).
  inv bsim_match_initial_states0.
  do 2 econstructor; simpl; simpl; eauto.

  intros. specialize (bsim_match_cont_match _ _ H H0) as (s1' & IS & []).
  exists x, s1'. eauto.

  intros. apply safe_sound_1 in H0. destruct H1 as (r0 & REPLY & FS).
  specialize (bsim_match_final_states0 _ _ _ _ H H0 FS) as (s1' & r1 & STAR & FS' & MS).
  exists s1'. split; eauto.

  intros. apply safe_sound_1 in H0.
  pose proof (progress := bsim_progress0).
  specialize (bsim_progress0 _ _ _ H H0) as [(r & FS)|[|]].
  left. destruct (reply_sound2 _ _ FS) as (ri & REPLY). eauto.
  destruct H1. exfalso. eapply closed2; eauto. eapply open_progress'; eauto.
  auto.

  intros. apply safe_sound_1 in H1.
  eapply bsim_simulation0; eauto.
  eapply  match_senv_public_preserved; eauto.
Qed.

End BACKWARD.

End CLOSE_SOUND.

End Closed.
