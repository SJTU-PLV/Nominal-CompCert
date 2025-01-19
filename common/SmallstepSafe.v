Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.

Set Implicit Arguments.


(** * Forward simulation with the progress property and the preservation of UB *)

(* It means that the compilation satisfying this simulation cannot
utilize the UB to optimize the program *)

Section FSIM_WITH_2P.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

(** Here we combine the progress property and UB preservation property
into one definition for convenience. But they should be orthogonal
concepts and located in two definitions in principal. For example,
some compilation pass may compile UB to DB (defined behavior) and also
preserve certain UB (such as memory error state). *)

Record fsimp_properties (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop)
                       (err_state1: state1 -> Prop) (err_state2: state2 -> Prop): Prop := {
    fsimp_prop:
    fsim_properties ccA ccB se1 se2 wB L1 L2
      index order match_states;

    fsimp_initial_progress: forall q1 q2 s2,
      match_query ccB wB q1 q2 ->
      initial_state L2 q2 s2 ->
      exists s1, initial_state L1 q1 s1;

    (** FIXME: this property may be not correct (but it can be proved
    in RustIRgen?) *)
    fsimp_external_progress: forall i s1 s2 s2' wA r1 r2,
      match_states i s1 s2 ->
      match_reply ccA wA r1 r2 -> 
      after_external L2 s2 r2 s2' ->
      exists s1', after_external L1 s1 r1 s1';
    
    fsimp_progress: forall i s1 s2,
      match_states i s1 s2 -> safe L2 s2 ->
      (exists r, final_state L1 s1 r)
      \/ (exists q, at_external L1 s1 q)
      \/ (exists t, exists s1', Step L1 s1 t s1');
    
    fsimp_err_preservation: forall i s1 s2,
      match_states i s1 s2 ->
      err_state1 s1 ->
      (* The execution of L2 cannot emit event *)
      exists s2', Star L2 s2 E0 s2'
             /\ err_state2 s2';
  }.


End FSIM_WITH_2P.

Arguments fsimp_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states err_state1 err_state2.

(* The error states should be transparent *)
Record fsimp_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 err_state1 err_state2 :=
  Forward_simulation_progress_ubpreserve {
    fsimp_index: Type;
    fsimp_order: fsimp_index -> fsimp_index -> Prop;
    fsimp_match_states: _;
      
    fsimp_skel:
      skel L1 = skel L2;
    fsimp_lts se1 se2 wB:
      @match_senv liB1 liB2 ccB wB se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsimp_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
        fsimp_index fsimp_order (fsimp_match_states se1 se2 wB) (err_state1 se1) (err_state2 se2);
    fsimg_order_wf:
      well_founded fsimp_order;
  }.

Arguments Forward_simulation_progress_ubpreserve {_ _ ccA _ _ ccB L1 L2 err_state1 err_state2 fsimp_index}.

(* We can treat error_state as the patch of L1/L2 *)
Definition forward_simulation_progress_ubpreserve {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 err_state1 err_state2 :=
  inhabited (@fsimp_components liA1 liA2 ccA liB1 liB2 ccB L1 L2 err_state1 err_state2).


Section FSIM_IMPL.

Context {liA1 liB1} (L1: semantics liA1 liB1).
Context {liA2 liB2} (L2: semantics liA2 liB2).

(** Forward simualtion with progress property implies the normal
forward simulation *)

Lemma fsim_progress_ubpreserve_implies {ccA ccB} err_state1 err_state2 :
  forward_simulation_progress_ubpreserve ccA ccB L1 L2 err_state1 err_state2 ->
  forward_simulation ccA ccB L1 L2.
Proof.
  intros [FSIMG]. econstructor.
  inv FSIMG. eapply Forward_simulation with (fsim_match_states := fsimp_match_states0); eauto.
  intros.
  exploit fsimp_lts0; eauto.
  intros FSIMG1. inv FSIMG1. inv fsimp_prop0.
  econstructor; eauto.
Qed.

Lemma fsim_progress_ubpreserve_implies_progress {ccA ccB} err_state1 err_state2 :
  forward_simulation_progress_ubpreserve ccA ccB L1 L2 err_state1 err_state2 ->
  forward_simulation_progress ccA ccB L1 L2.
Proof.
  intros [FSIMG]. econstructor.
  inv FSIMG. eapply Forward_simulation_progress with (fsimg_match_states := fsimp_match_states0); eauto.
  intros.
  exploit fsimp_lts0; eauto.
  intros FSIMG1. inv FSIMG1. inv fsimp_prop0.
  econstructor; eauto.
  econstructor; eauto.
Qed.


End FSIM_IMPL.

(** Copy the tactic for normal forward simulation *)

Ltac fsimp_tac tac :=
  intros MATCH; constructor;
  eapply Forward_simulation_progress_ubpreserve with (fsimp_match_states := fun _ _ _ => _);
  [ try fsim_skel MATCH
  | intros se1 se2 w Hse Hse1; econstructor; try tac
  | try solve [auto using well_founded_ltof]].

Tactic Notation (at level 3) "fsimp" tactic3(tac) := fsimp_tac tac.


(** Backward simulation with the property of UB preservation  *)

Definition partial_safe {liA liB st} (L: lts liA liB st) (err_state: st -> Prop) (s: st) : Prop :=
  forall s',
  Star L s E0 s' ->
  ((exists r, final_state L s' r)
  \/ (exists q, at_external L s' q)
  \/ (exists t, exists s'', Step L s' t s''))
  \/ err_state s'.

Lemma star_partial_safe:
  forall {liA liB st} (L: lts liA liB st) err s s',
  Star L s E0 s' -> partial_safe L err s -> partial_safe L err s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

Section BSIM.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

(** The general form of a backward simulation. *)

Record bsimp_properties (L1 L2: lts _ _ _) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop)
                       err_state1 err_state2 : Prop := {
    bsimp_match_valid_query:
      forall q1 q2, match_query ccB wB q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    bsimp_match_initial_states:
      forall q1 q2, match_query ccB wB q1 q2 ->
      bsim_match_cont (rex match_states) (initial_state L1 q1) (initial_state L2 q2);
    bsimp_match_final_states:
      forall i s1 s2 r2,
      match_states i s1 s2 -> partial_safe L1 err_state1 s1 -> final_state L2 s2 r2 ->
      exists s1' r1, Star L1 s1 E0 s1' /\ final_state L1 s1' r1 /\ match_reply ccB wB r1 r2;
    bsimp_match_external:
      forall i s1 s2 q2, match_states i s1 s2 -> partial_safe L1 err_state1 s1 -> at_external L2 s2 q2 ->
      exists wA s1' q1, Star L1 s1 E0 s1' /\ at_external L1 s1' q1 /\
      match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
      forall r1 r2, match_reply ccA wA r1 r2 ->
      bsim_match_cont (rex match_states) (after_external L1 s1' r1) (after_external L2 s2 r2);
    bsimp_progress:
      forall i s1 s2,
      match_states i s1 s2 -> partial_safe L1 err_state1 s1 ->
      ((exists r, final_state L2 s2 r) \/
      (exists q, at_external L2 s2 q) \/
      (exists t, exists s2', Step L2 s2 t s2')) \/
      err_state2 s2;
    bsimp_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> partial_safe L1 err_state1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments bsimp_properties: clear implicits.

End BSIM.

Arguments bsimp_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states err_state1 err_state2.

Record bsimp_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 err_state1 err_state2 :=
  Backward_simulation_preserve_error {
    bsimp_index: Type;
    bsimp_order: bsimp_index -> bsimp_index -> Prop;
    bsimp_match_states: _;

    bsimp_skel:
      skel L1 = skel L2;
    bsimp_lts:
      forall se1 se2 wB,
        @match_senv liB1 liB2 ccB wB se1 se2 ->
        Genv.valid_for (skel L1) se1 ->
        bsimp_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
                        bsimp_index bsimp_order (bsimp_match_states se1 se2 wB) (err_state1 se1) (err_state2 se2);
    bsimp_order_wf:
      well_founded bsimp_order;
    }.

Arguments Backward_simulation_preserve_error {_ _ ccA _ _ ccB L1 L2 err_state1 err_state2 bsimp_index}.

Definition backward_simulation_preserve_error {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 err_state1 err_state2 :=
  inhabited (@bsimp_components liA1 liA2 ccA liB1 liB2 ccB L1 L2 err_state1 err_state2).

(** * Forward simulation to the error preserving backward simulation *)

(* Most of the proof are the same as the forward_to_backward in Smallstep.v *)

Record lts_sound_err {liA liB st} (L: lts liA liB st) (err: st -> Prop) : Prop :=
  Sound_error {
      sd_err_nostep: forall s,
        err s ->
        Nostep L s;

      sd_final_noerr: forall s r,
        final_state L s r ->
        err s ->
        False;

      sd_external_noerr: forall s q,
        at_external L s q ->
        err s ->
        False;        
    }.

Definition sound_err {liA liB} (L: semantics liA liB) err :=
  forall se,
  lts_sound_err (L se) (err se).

Section FORWARD_TO_BACKWARD.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2} (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2).
Context {index order match_states} (FS: fsim_properties ccA ccB se1 se2 wB L1 L2 index order match_states).
Hypothesis order_wf: well_founded order.
Hypothesis Hse: match_senv ccB wB se1 se2.
Hypothesis L1_receptive: lts_receptive L1 se1.
Hypothesis L2_determinate: lts_determinate L2 se2.

Context (err_state1: state1 -> Prop) (err_state2: state2 -> Prop).

Hypothesis L2_sound_err: lts_sound_err L2 err_state2.

Hypothesis err_preservation: forall i s1 s2,
    match_states i s1 s2 ->
    err_state1 s1 ->
    exists s2' : state2, Star L2 s2 E0 s2' /\ err_state2 s2'.

(* f2b_partial_transition is a useful predicate to exploit the
transition in source and target *)

Let f2b_transitions := @f2b_transitions _ _ ccA _ _ ccB se1 se2 wB _ _ L1 L2 index match_states.
Inductive f2b_partial_transitions: state1 -> state2 -> Prop :=
| f2b_trans_normal: forall s1 s2,
    f2b_transitions s1 s2 ->
    f2b_partial_transitions s1 s2
| f2b_trans_err: forall s1 s1' s2 s2' i,
    (* handle stuttering in L1 *)
    Star L1 s1 E0 s1' ->
    match_states i s1' s2 ->
    err_state1 s1' ->
    Star L2 s2 E0 s2' ->
    err_state2 s2' ->
    f2b_partial_transitions s1 s2.

Lemma f2b_partial_progress:
  forall i s1 s2, match_states i s1 s2 -> partial_safe L1 err_state1 s1 -> f2b_partial_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order); auto.
  intros i REC s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[[r FINAL] | [[q EXTERN] | [t [s1' STEP1]]]]| ERR]. apply star_refl.
  - (* final state reached *)
    edestruct @fsim_match_final_states as (r2 & Hr & Hfinal); eauto.
    eapply f2b_trans_normal. eapply f2b_trans_final; eauto.
    apply star_refl.
  - (* external call reached *)
    edestruct @fsim_match_external as (w & q2 & Hq & Hat & Hse' & Hafter); eauto.
    eapply f2b_trans_normal. eapply f2b_trans_ext; eauto.
    apply star_refl.
  - (* L1 can make one step *)
    exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
    assert (B: Plus L2 s2 t s2' \/ (s2' = s2 /\ t = E0 /\ order i' i)).
    intuition auto.
    destruct (star_inv H0); intuition auto.
    clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
    + eapply f2b_trans_normal. eapply f2b_trans_step; eauto. apply star_refl.
    + subst. exploit REC; eauto. eapply star_partial_safe; eauto. apply star_one; auto.
      intros TRANS. inv TRANS. inv H.
      * eapply f2b_trans_normal. eapply f2b_trans_final; eauto. eapply star_step; eauto.
      * eapply f2b_trans_normal. eapply f2b_trans_ext; eauto. eapply star_left; eauto.
      * eapply f2b_trans_normal. eapply f2b_trans_step; eauto. eapply star_left; eauto.
      (* error state  *)
      * eapply f2b_trans_err; eauto. eapply star_left; eauto.
  (* L1 is in the error state *)
  - exploit err_preservation; eauto. intros (s2' & STAR & ERR2).
    eapply f2b_trans_err; eauto. eapply star_refl. 
Qed.

(* simulation relation used in backward simulation *)

Let f2b_match_states := @f2b_match_states _ _ _ _ _ _ L1 L2 index match_states.

Inductive f2b_partial_match_states : f2b_index -> state1 -> state2 -> Prop :=
| f2b_pmatch_normal: forall i s1 s2
    (MATCH: f2b_match_states i s1 s2),
    f2b_partial_match_states i s1 s2
| f2b_pmatch_err: forall n s1 s2 s2b s2a i
    (Err1: err_state1 s1)
    (STAR: Star L2 s2b E0 s2)
    (STARN: starN (step L2) (globalenv L2) n s2 E0 s2a)
    (Err2: err_state2 s2a)
    (MATCH: match_states i s1 s2b),
    f2b_partial_match_states (F2BI_before n) s1 s2.

Lemma f2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i s1, f2b_partial_match_states i s1 s2 -> partial_safe L1 err_state1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ f2b_order i' i))
     /\ f2b_partial_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH. inv MATCH0.
- (* 1. At matching states *)
  exploit f2b_partial_progress; eauto. intros TRANS; inv TRANS. inv H0.
  + (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
    exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  + (* 1.1b  Same, with external states *)
    exploit (sd_at_external_nostep L2_determinate); eauto. contradiction.
  + (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
    inv H3.
    exploit @f2b_determinacy_inv. 1-2: eauto. eexact H0. eexact STEP2.
    intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
    * (* 1.2.1  L2 makes a silent transition *)
      destruct (silent_or_not_silent t2).
      (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
      subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
      exists (F2BI_after n); exists s1''; split.
      left. eapply plus_right; eauto.
      eapply f2b_pmatch_normal.
      eapply f2b_match_after'; eauto.
      (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
      subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
      exists (F2BI_before n); exists s1'; split.
      right; split. auto. constructor.
      eapply f2b_pmatch_normal.
      econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
    * (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
      exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
      congruence.
      subst t2. rewrite E0_right in H2.
      (* Use receptiveness to equate the traces *)
      exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
      exploit @fsim_simulation_not_E0. eauto. eexact STEP1. auto. eauto.
      intros [i''' [s2''' [P Q]]]. inv P.
      (* Exploit determinacy *)
      exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
      subst t0. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H3.
      intros. elim NOT2. inv H8. auto.
      subst t2. rewrite E0_right in *.
      assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
      (* Perform transition now and go to "after" state *)
      destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
      left. eapply plus_right; eauto.
      eapply f2b_pmatch_normal.
      eapply f2b_match_after'; eauto.
      
  (* L1 and L2 step to an error state *)
  + inv H3.
    (* L2 make 0 or several matching steps *)
    * (* impossible because error state cannot make step *)
      exfalso. eapply sd_err_nostep; eauto.
    * exploit @f2b_determinacy_inv. 1-2: eauto. eexact H5. eexact STEP2.
      intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
      -- subst.
         destruct (silent_or_not_silent t2); simpl in H7; try congruence. subst.
         (* L1 makes 0 transition and update the index to (before n) *)
         destruct (star_starN H6) as [n STEPS2].
         exists (F2BI_before n), s1'; split.
         right; split. auto. constructor.
         eapply f2b_pmatch_err; eauto. eapply star_one; eauto.
      -- exploit Eapp_E0_inv; eauto.
         intros (A1 & A2). subst. congruence.
         
- (* 2. Before *)
  inv H2. congruence.
  exploit @f2b_determinacy_inv. 1-2: eauto. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  + (* 2.1 L2 makes a silent transition: remain in "before" state *)
    subst. simpl in *. exists (F2BI_before n0); exists s1; split.
    right; split. apply star_refl. constructor. lia.
    eapply f2b_pmatch_normal.
    econstructor; eauto. eapply star_right; eauto.
  + (* 2.2 L2 make a non-silent transition *)
    exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
    congruence.
    subst. rewrite E0_right in *.
    (* Use receptiveness to equate the traces *)
    exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
    exploit @fsim_simulation_not_E0. eauto. eexact STEP1. auto. eauto.
    intros [i''' [s2''' [P Q]]].
    (* Exploit determinacy *)
    exploit @f2b_determinacy_star. 1-2: eauto.
    eauto. eexact STEP2. auto. apply plus_star; eauto.
    intro R. inv R. congruence.
    exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
    subst. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H2.
    intros. elim NOT2. inv H7; auto.
    subst. rewrite E0_right in *.
    assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
    (* Perform transition now and go to "after" state *)
    destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
    left. apply plus_one; auto.
    eapply f2b_pmatch_normal.
    eapply f2b_match_after'; eauto.

- (* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit @f2b_determinacy_inv. 1-2: eauto. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; lia.
  eapply f2b_pmatch_normal.
  eapply f2b_match_after'; eauto.
  congruence.
  
(* 4. Error states *)
- inv STARN.
  (* impossible: error state s2a cannot take a step *)
  exfalso. eapply sd_err_nostep; eauto.
  exploit @f2b_determinacy_inv. 1-2: eauto. eexact H. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  + (* 4.1 L2 makes a silent transition: remain in "before" state *)
    subst. simpl in *. exists (F2BI_before n0); exists s1; split.
    right; split. apply star_refl. constructor. lia.
    subst. eapply f2b_pmatch_err; eauto.
    eapply star_right; eauto.
  + exploit Eapp_E0_inv; eauto.
    intros (A1 & A2). subst. congruence.
    
Qed.

End FORWARD_TO_BACKWARD.

Lemma forward_to_backward_simulation_partial:
  forall {liA1 liA2} (ccA: callconv liA1 liA2),
  forall {liB1 liB2} (ccB: callconv liB1 liB2),
  forall L1 L2 err_state1 err_state2,
    forward_simulation_progress_ubpreserve ccA ccB L1 L2 err_state1 err_state2 ->
    receptive L1 ->
    determinate L2 ->
    sound_err L2 err_state2 ->
    backward_simulation_preserve_error ccA ccB L1 L2 err_state1 err_state2.
Proof.
  intros until err_state2. intros FS L1_receptive L2_determinate Err2.
  destruct FS as [[index order match_states Hskel FS order_wf]].
  set (ms se1 se2 w := f2b_partial_match_states (L1 se1) (L2 se2) (match_states := match_states se1 se2 w) (err_state1 se1) (err_state2 se2)).
  constructor.
  eapply Backward_simulation_preserve_error with f2b_order ms; auto using wf_f2b_order.
  intros se1 se2 wB Hse Hse1.
  specialize (FS se1 se2 wB Hse Hse1).
  specialize (L1_receptive se1). specialize (L2_determinate se2).
  specialize (Err2 se2).
  inv FS.
  split. 
- (* valid queries *)
  eapply fsim_match_valid_query; eauto.
- split.
  (* initial states exist *)
  intros. exploit (fsim_match_initial_states fsimp_prop0); eauto. intros [i [s2 [A B]]].
  exists s2; auto.
  (* initial states *)
  intros. exploit (fsim_match_initial_states fsimp_prop0); eauto. intros [i [s2' [A B]]].
  assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
  exists s1; split; auto. exists (F2BI_after O). econstructor; eauto.
  econstructor; eauto.
- (* final states *)
  intros. inv H. inv MATCH.
  + exploit @f2b_partial_progress; eauto. intros TRANS; inv TRANS. inv H2.
    * assert (r0 = r2) by eauto using sd_final_determ; subst. eauto using star_refl.
    * eelim sd_final_noext; eauto.
    * inv H5. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
    * inv H5.
      -- (* final no error *)
        exfalso. eapply sd_final_noerr; eauto.
      -- exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  + inv H4. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  + inv H. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  + inv STARN.
    * (* final no error *)
      exfalso. eapply sd_final_noerr; eauto.
    * exploit (sd_final_nostep L2_determinate); eauto. contradiction.
- (* external states *)
  intros. inv H. inv MATCH.
  + exploit @f2b_partial_progress; eauto.
    intros TRANS; inv TRANS. inv H2.
    * eelim (sd_final_noext L2_determinate); eauto.
    * assert (q0 = q2) by eauto using sd_at_external_determ; subst.
      exists wA, s1', q1. intuition auto. split.
      intros. edestruct H8 as (j & s2' & Hs2' & Hs'); eauto.
      intros. edestruct H8 as (j & s2' & Hs2' & Hs'); eauto.
      assert (s3 = s2') by eauto using sd_after_external_determ; subst.
      exists s0. intuition auto.
      exists (F2BI_after O). econstructor; eauto. econstructor; eauto.
    * inv H5. eelim (sd_at_external_nostep L2_determinate); eauto.
    * inv H5.
      -- (* external no error *)
        exfalso. eapply sd_external_noerr; eauto.
      -- eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H4. congruence. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv STARN.
    -- (* external no error *)
      exfalso. eapply sd_external_noerr; eauto.
    -- eelim (sd_at_external_nostep L2_determinate); eauto.
- (* progress *)
  intros. inv H. inv MATCH.
  + exploit @f2b_partial_progress; eauto. intros TRANS; inv TRANS; inv H1; eauto.
    * inv H4. left. eauto.
    * inv H4; eauto.
      left. eauto.
    * inv H4; eauto.
      left. eauto.
  + inv H3; eauto. congruence.
    left. eauto.
  + inv H. left. eauto.
  + inv STARN; eauto.
    left. eauto.
- (* simulation *)
  eapply f2b_simulation_step; eauto.
Qed.
