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
  Forward_simulation_ppub {
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

Arguments Forward_simulation_ppub {_ _ ccA _ _ ccB L1 L2 err_state1 err_state2 fsimp_index}.

(* We can treat error_state as the patch of L1/L2 *)
Definition forward_simulation_ppub {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 err_state1 err_state2 :=
  inhabited (@fsimp_components liA1 liA2 ccA liB1 liB2 ccB L1 L2 err_state1 err_state2).

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
