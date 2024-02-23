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

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Eventually' L " := (eventually (step L) (at_external L) (final_state L) (globalenv L)) (at level 1) : closed_smallstep_scope.
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
    (* fsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id *)
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: index -> state L1 -> state L2 -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.


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
    (* bsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id *)
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
Qed.

End BACKWARD.

End CLOSE_SOUND.

End Closed.
