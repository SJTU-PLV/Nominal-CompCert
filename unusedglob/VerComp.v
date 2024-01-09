Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Memory.
Require Import Smallstep.
Require Import Inject InjectFootprint.
Require Import CKLRAlgebra.
Require Import Callconv ForwardSim.


(** * Test1: cc_compose_1 *)


Program Definition cc_compose_1 {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv' li2 li3) :=
  {|
    ccworld' := Genv.symtbl * ccworld cc12 * ccworld' cc23;
    match_senv' '(se2, w12, w23) se1 se3 :=
      match_senv cc12 w12 se1 se2 /\
      match_senv' cc23 w23 se2 se3;
    match_query' '(se2, w12, w23) q1 q3 :=
      exists q2,
        match_query cc12 w12 q1 q2 /\
        match_query' cc23 w23 q2 q3;
    match_reply' '(se2, w12, w23) r1 r3 :=
      exists r2,
        match_reply cc12 w12 r1 r2 /\
        match_reply' cc23 w23 r2 r3;
  |}.
Next Obligation.
  etransitivity.
  eapply match_senv_public_preserved'. eauto.
  eauto using match_senv_public_preserved.
Qed.

Infix "@1" := cc_compose_1 (at level 30, right associativity) : cc_scope.

Section CC_COMPOSE1.

Context {liA1 liA2 liA3} {ccA12: callconv liA1 liA2} {ccA23: callconv' liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv liB1 liB2} {ccB23: callconv' liB2 liB3}.
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (L3: semantics liA3 liB3).


Lemma compose_fsim_components_1:
  fsim_components ccA12 ccB12 L1 L2 ->
  fsim_components' ccA23 ccB23 L2 L3 ->
  fsim_components' (cc_compose_1 ccA12 ccA23) (cc_compose_1 ccB12 ccB23) L1 L3.
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
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { rewrite Hsk. congruence. }
  intros se1 se3 [[se2 w] w'] (Hse12 & Hse23) Hse1. cbn in *.
  destruct Hse1 as [Hvalid1 [Hvalid3 COMPAT13]].
  assert (Hvalid2: Genv.valid_for (skel L2) se2).
  { rewrite <- Hsk. eapply match_senv_valid_for; eauto. }
  assert (Hse2: Genv.skel_symtbl_compatible (skel L2) (skel L3) se2 se3).
  {
    constructor; eauto. split. eauto.
    destruct COMPAT13.
    split. intros. rewrite <- Hsk in H1. eauto.
    intro. apply H0. red.
    destruct H1 as [b2 [A B]]. rewrite Hsk.
    apply match_senv_match_stbls in Hse12. destruct Hse12 as [j1 Hse12].
    inversion Hse12.
    exploit mge_img; eauto. eapply Genv.genv_symb_range. eauto.
    intros [b1 INJ12].
    setoid_rewrite <- Genv.mge_symb in A; eauto.
  }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query'. 2: eapply props'; eauto.
  eapply fsim_match_valid_query; eauto. eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states' liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states' liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external' liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus' liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
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

Lemma compose_forward_simulations_1:
  forward_simulation ccA12 ccB12 L1 L2 ->
  forward_simulation' ccA23 ccB23 L2 L3 ->
  forward_simulation' (cc_compose_1 ccA12 ccA23) (cc_compose_1 ccB12 ccB23) L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components_1; auto.
Qed.

End CC_COMPOSE1.


Program Definition cc_compose_2 {li1 li2 li3} (cc12: callconv' li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld' := Genv.symtbl * ccworld' cc12 * ccworld cc23;
    match_senv' '(se2, w12, w23) se1 se3 :=
      match_senv' cc12 w12 se1 se2 /\
      match_senv cc23 w23 se2 se3;
    match_query' '(se2, w12, w23) q1 q3 :=
      exists q2,
        match_query' cc12 w12 q1 q2 /\
        match_query cc23 w23 q2 q3;
    match_reply' '(se2, w12, w23) r1 r3 :=
      exists r2,
        match_reply' cc12 w12 r1 r2 /\
        match_reply cc23 w23 r2 r3;
  |}.
Next Obligation.
  etransitivity.
  eapply match_senv_public_preserved; eauto.
  eauto using match_senv_public_preserved'.
Qed.

Infix "@1" := cc_compose_1 (at level 30, right associativity) : cc_scope.


Lemma match_stbls_find_none:
  forall j se1 se2 id,
    Genv.match_stbls j se1 se2 ->
    Genv.find_symbol se1 id = None <-> Genv.find_symbol se2 id = None.
Proof.
  intros. destruct (Genv.find_symbol se1 id) eqn: F1.
  - inv H. exploit mge_dom; eauto. eapply Genv.genv_symb_range. eauto.
    intros [b2 INJ]. setoid_rewrite mge_symb in F1; eauto.
    setoid_rewrite F1. split; congruence.
  - destruct (Genv.find_symbol se2 id) eqn: F2.
    exfalso. inv H.
    exploit mge_img; eauto. eapply Genv.genv_symb_range. eauto.
    intros [b1 INJ]. setoid_rewrite <- mge_symb in F2; eauto.
    unfold Genv.find_symbol in F1. congruence.
    split; eauto.
Qed.

Section CC_COMPOSE2.

Context {liA1 liA2 liA3} {ccA12: callconv' liA1 liA2} {ccA23: callconv liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv' liB1 liB2} {ccB23: callconv liB2 liB3}.
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (L3: semantics liA3 liB3).


Lemma compose_fsim_components_2:
  fsim_components' ccA12 ccB12 L1 L2 ->
  fsim_components ccA23 ccB23 L2 L3 ->
  fsim_components' (cc_compose_2 ccA12 ccA23) (cc_compose_2 ccB12 ccB23) L1 L3.
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
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { rewrite <- Hsk'. congruence. }
  intros se1 se3 [[se2 w] w'] (Hse12 & Hse23) Hse1. cbn in *.
  destruct Hse1 as [Hvalid1 [Hvalid3 COMPAT13]].
  apply match_senv_match_stbls in Hse23 as Hse23'. destruct Hse23' as [j2 Hse23'].
  assert (Hvalid2: Genv.valid_for (skel L2) se2).
  { rewrite  Hsk'.
    erewrite Genv.valid_for_match; eauto.
  }
  assert (Hse2: Genv.skel_symtbl_compatible (skel L1) (skel L2) se1 se2).
  {
    constructor; eauto. split. eauto.
    destruct COMPAT13.
    split. intros. rewrite Hsk'.
    apply H. eauto.
    rewrite <- match_stbls_find_none; eauto.
    intro. apply H0.
    red. red in H1.
    destruct H1 as [b1 [A B]].
    exists b1. split. eauto.
    rewrite <- match_stbls_find_none; eauto.
  }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query. 2: eapply props'; eauto.
  eapply fsim_match_valid_query'; eauto. eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states' liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states' liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external' liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation'_1 liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
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

Lemma compose_forward_simulations_2:
  forward_simulation' ccA12 ccB12 L1 L2 ->
  forward_simulation ccA23 ccB23 L2 L3 ->
  forward_simulation' (cc_compose_2 ccA12 ccA23) (cc_compose_2 ccB12 ccB23) L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components_2; auto.
Qed.

End CC_COMPOSE2.





(** * Definition of new callconv refinement *)
(* From common/CallconvAlgebra.v *)


Definition ccref' {li1 li2} (cc cc': callconv' li1 li2) :=
  forall w se1 se2 q1 q2,
    match_senv' cc w se1 se2 ->
    match_query' cc w q1 q2 ->
    exists w',
      match_senv' cc' w' se1 se2 /\
      match_query' cc' w' q1 q2 /\
      forall r1 r2,
        match_reply' cc' w' r1 r2 ->
        match_reply' cc w r1 r2.

Definition cceqv' {li1 li2} (cc cc': callconv' li1 li2) :=
  ccref' cc cc' /\ ccref' cc' cc.

Global Instance ccref_preo' li1 li2:
  PreOrder (@ccref' li1 li2).
Proof.
  split.
  - intros cc w q1 q2 Hq.
    eauto.
  - intros cc cc' cc'' H' H'' w se1 se2 q1 q2 Hse Hq.
    edestruct H' as (w' & Hse' & Hq' & Hr'); eauto.
    edestruct H'' as (w'' & Hse'' & Hq'' & Hr''); eauto 10.
Qed.

Global Instance cceqv_equiv' li1 li2:
  Equivalence (@cceqv' li1 li2).
Proof.
  split.
  - intros cc.
    split; reflexivity.
  - intros cc1 cc2. unfold cceqv'.
    tauto.
  - intros cc1 cc2 cc3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance ccref_po' li1 li2:
  PartialOrder (@cceqv' li1 li2) (@ccref' li1 li2).
Proof.
  firstorder.
Qed.

(** ** Relation to forward simulations *)

Global Instance open_fsim_ccref':
  Monotonic
    (@forward_simulation')
    (forallr - @ liA1, forallr - @ liA2, ccref' ++>
     forallr - @ liB1, forallr - @ liB2, ccref' -->
     subrel).
Proof.
  intros liA1 liA2 ccA ccA' HA liB1 liB2 ccB ccB' HB sem1 sem2 [FS].
  destruct FS as [index order match_states SKEL PROP WF].
  constructor.
  set (ms se1 se2 w' idx s1 s2 :=
         exists w : ccworld' ccB,
           match_states se1 se2 w idx s1 s2 /\
           match_senv' ccB w se1 se2 /\
           forall r1 r2, match_reply' ccB w r1 r2 -> match_reply' ccB' w' r1 r2).
  eapply Forward_simulation' with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query'; eauto.
  - intros q1 q2 s1 Hq' Hs1.
    destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    edestruct @fsim_match_initial_states' as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. exists wB; auto.
  - intros i s1 s2 r1 (wB & Hs & Hse & Hr') Hr1.
    edestruct @fsim_match_final_states' as (r2 & Hr2 & Hr); eauto.
  - intros i s1 s2 qA1 (wB & Hs & Hse & Hr') HqA1.
    edestruct @fsim_match_external' as (wA & qA2 & HqA2 & HqA & HseA & ?); eauto.
    edestruct HA as (wA' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB; eauto.
  - intros s1 t s1' Hs1' i s2 (wB & Hs & Hse & Hr').
    edestruct @fsim_simulation'_1; eauto.
    destruct H as (i' & s2' & Hs2' & Hs').
    exists i', s2'. split; auto. exists wB; eauto.
    destruct H as (i' & C & D & E).
    exists i', s2. split; auto. right. split.
    subst. eapply star_refl. eauto. exists wB; eauto.
Qed.
(*
Global Instance open_bsim_ccref':
  Monotonic
    (@backward_simulation')
    (forallr - @ liA1, forallr - @ liA2, ccref' ++>
     forallr - @ liB1, forallr - @ liB2, ccref' -->
     subrel).
Proof.
  intros liA1 liA2 ccA ccA' HA liB1 liB2 ccB ccB' HB sem1 sem2 [FS].
  destruct FS as [index order match_states SKEL PROP WF].
  constructor.
  set (ms se1 se2 w' idx s1 s2 :=
         exists w : ccworld ccB,
           match_states se1 se2 w idx s1 s2 /\
           match_senv ccB w se1 se2 /\
           forall r1 r2, match_reply ccB w r1 r2 -> match_reply ccB' w' r1 r2).
  eapply Backward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply bsim_match_valid_query; eauto.
  - intros q1 q2 Hq'.
    destruct (HB wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
    split; auto.
    intros. edestruct MATCH as (s1' & Hs1' & i & Hs); eauto. 
    exists s1'. split; auto. exists i, wB; auto.
  - intros i s1 s2 r1 (wB & Hs & Hse & Hr') SAFE Hr1.
    edestruct @bsim_match_final_states as (s2' & r2 & Hs2' & Hr2 & Hr); eauto 10.
  - intros i s1 s2 qA1 (wB & Hs & Hse & Hr') SAFE HqA1.
    edestruct @bsim_match_external as (wA & s1' & qA2 & Hs1' & HqA2 & HqA & HseA & ?); eauto.
    edestruct HA as (wA' & HseA' & HqA' & Hr); eauto.
    exists wA', s1', qA2. intuition auto.
    edestruct H as [EXIST MATCH]; eauto. split; auto.
    intros. edestruct MATCH as (s1'' & Hs1'' & j & Hs''); eauto.
    exists s1''. split; auto.
    exists j. red. eauto 10.
  - intros i s1 s2 (wB & Hs & Hse & Hr') SAFE.
    eapply bsim_progress; eauto.
  - intros s2 t s2' Hs2' i s1 (wB & Hs & Hse & Hr') SAFE.
    edestruct @bsim_simulation as (i' & s1' & Hs1' & Hs'); eauto.
    exists i', s1'. split; auto. exists wB; eauto.
Qed.
*)



(** Pre: from cklr/CKLRAlgebra.v *)

Definition subcklr' (Q R: cklr') :=
  forall wq se1 se2 m1 m2,
    match_stbls Q wq se1 se2 ->
    match_mem Q wq m1 m2 ->
    exists wr,
      match_stbls R wr se1 se2 /\
      match_mem R wr m1 m2 /\
      inject_incr (mi Q wq) (mi R wr) /\
      forall wr' m1' m2',
        match_mem R wr' m1' m2' ->
        wr ~> wr' ->
        exists wq',
          match_mem Q wq' m1' m2' /\
          wq ~> wq' /\
          inject_incr (mi R wr') (mi Q wq').

Definition eqcklr' R1 R2 :=
  subcklr' R1 R2 /\ subcklr' R2 R1.

Global Instance subcklr_preo':
  PreOrder subcklr'.
Proof.
  split.
  - intros R w q1 q2 Hq.
    exists w; intuition eauto.
  - intros R1 R2 R3 H12 H23 w1 sea seb ma mb Hse1 Hm1.
    destruct (H12 w1 sea seb ma mb Hse1 Hm1) as (w2 & Hse2 & Hm2 & Hincr12 & H21); clear H12.
    destruct (H23 w2 sea seb ma mb Hse2 Hm2) as (w3 & Hse3 & Hm3 & Hincr23 & H32); clear H23.
    exists w3. repeat apply conj; eauto using inject_incr_trans.
    intros w3' ma' mb' Hm3' Hw3'.
    destruct (H32 w3' ma' mb' Hm3' Hw3') as (w2' & Hm2' & Hw2' & Hincr32).
    destruct (H21 w2' ma' mb' Hm2' Hw2') as (w1' & Hm1' & Hw1' & Hincr21).
    exists w1'; intuition eauto using inject_incr_trans.
Qed.

Global Instance eqcklr_equiv':
  Equivalence eqcklr'.
Proof.
  split.
  - intros R.
    split; reflexivity.
  - intros R1 R2. unfold eqcklr'.
    tauto.
  - intros R1 R2 R3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance subcklr_po':
  PartialOrder eqcklr' subcklr'.
Proof.
  unfold eqcklr'. red. generalize subcklr'.
  firstorder.
Qed.


(** * Composition *)

(** ** Definition *)

(** ** Preliminaries *)

Lemma option_le_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (option_le (rel_compose R1 R2))
    (rel_compose (option_le R1) (option_le R2)).
Proof.
  split.
  - intros _ _ [x z (y & Hxy & Hyz) | z];
    eexists; split; constructor; eauto.
  - intros x z (y & Hxy & Hyz).
    destruct Hxy; [inversion Hyz; clear Hyz; subst | ];
    constructor; eexists; split; eauto.
Qed.

Lemma list_rel_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (list_rel (rel_compose R1 R2))
    (rel_compose (list_rel R1) (list_rel R2)).
Proof.
  split.
  - induction 1.
    + exists nil; split; constructor.
    + destruct H as (z & ? & ?).
      destruct IHlist_rel as (z0 & ? & ?).
      exists (z::z0); split; constructor; eauto.
  - intros la lc (lb & H1 & H2).
    revert lc H2.
    induction H1; intros lc H2; inv H2.
    + constructor.
    + constructor; eauto.
Qed.

Global Instance compose_meminj_incr:
  Monotonic compose_meminj (inject_incr ++> inject_incr ++> inject_incr).
Proof.
  intros f1 f2 Hf g1 g2 Hg b xb xdelta.
  unfold compose_meminj.
  destruct (f1 b) as [[b' delta] | ] eqn:Hb'; try discriminate.
  erewrite Hf by eauto.
  destruct (g1 b') as [[b'' delta'] | ] eqn:Hb''; try discriminate.
  erewrite Hg by eauto.
  tauto.
Qed.

Lemma val_inject_compose f g:
  eqrel
    (Val.inject (compose_meminj f g))
    (rel_compose (Val.inject f) (Val.inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try (eexists; split; constructor).
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    exists (Vptr bi (Ptrofs.add ofs1 (Ptrofs.repr di))).
    split; econstructor; eauto.
    rewrite add_repr, Ptrofs.add_assoc.
    reflexivity.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; econstructor.
    unfold compose_meminj.
    + rewrite H, H3.
      reflexivity.
    + rewrite add_repr, Ptrofs.add_assoc.
      reflexivity.
Qed.

Lemma memval_inject_compose f g:
  eqrel
    (memval_inject (compose_meminj f g))
    (rel_compose (memval_inject f) (memval_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try solve [eexists; split; constructor].
    apply val_inject_compose in H.
    destruct H as (vi & Hv1i & Hvi2).
    eexists; split; constructor; eauto.
  - intros v1 v3 Hv.
    destruct Hv as (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; constructor.
    apply val_inject_compose.
    eexists; split; eauto.
Qed.

Lemma ptr_inject_compose f g:
  eqrel
    (ptr_inject (compose_meminj f g))
    (rel_compose (ptr_inject f) (ptr_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv.
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    rewrite Z.add_assoc.
    exists (bi, ofs1 + di); split; econstructor; eauto.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23.
    rewrite <- Z.add_assoc.
    constructor.
    unfold compose_meminj.
    rewrite H, H3.
    reflexivity.
Qed.

Lemma ptrbits_inject_compose f g:
  eqrel
    (ptrbits_inject (compose_meminj f g))
    (rel_compose (ptrbits_inject f) (ptrbits_inject g)).
Proof.
  split.
  - destruct 1.
    unfold compose_meminj in H.
    destruct (f b1) as [[bI delta1I] | ] eqn:H1I; [ | discriminate].
    exists (bI, Ptrofs.add ofs1 (Ptrofs.repr delta1I)); split; eauto.
    destruct (g bI) as [[xb2 deltaI2] | ] eqn:HI2; [ | discriminate].
    inv H.
    rewrite add_repr.
    rewrite <- Ptrofs.add_assoc.
    constructor; eauto.
  - intros p1 p3 (p2 & H12 & H23).
    destruct H12 as [b1 ofs1 b2 delta12].
    inv H23.
    rewrite Ptrofs.add_assoc.
    rewrite <- add_repr.
    constructor.
    unfold compose_meminj. rewrite H, H3.
    reflexivity.
Qed.

Lemma rptr_inject_compose f g:
  subrel
    (rptr_inject (compose_meminj f g))
    (rel_compose (rptr_inject f) (rptr_inject g)).
Proof.
  unfold rptr_inject.
  intros p1 p3 Hp.
  rewrite ptr_inject_compose in Hp.
  rewrite ptrbits_inject_compose in Hp.
  destruct Hp as [(p2 & H12 & H23) | [q1 q3 (q2 & H12 & H23)]].
  - exists p2; split; rauto.
  - exists (ptrbits_unsigned q2); split; rauto.
Qed.

Lemma ptrrange_inject_compose f g:
  eqrel
    (ptrrange_inject (compose_meminj f g))
    (rel_compose (ptrrange_inject f) (ptrrange_inject g)).
Proof.
  split.
  - destruct 1.
    apply ptr_inject_compose in H.
    destruct H as ([bi ofsi] & H1 & H2).
    exists (bi, ofsi, ofsi + sz).
    split; constructor; eauto.
  - intros r1 r3 (r2 & H12 & H23).
    destruct H12; inv H23.
    assert (sz0 = sz) by lia; subst.
    constructor.
    apply ptr_inject_compose.
    eexists; split; eauto.
Qed.

Lemma block_inject_compose f g:
  eqrel
    (block_inject (compose_meminj f g))
    (rel_compose (block_inject f) (block_inject g)).
Proof.
  split.
  - intros b1 b3 [d13 H13].
    unfold compose_meminj in H13.
    destruct (f b1) as [[b2 d12] | ] eqn:H12; [ | discriminate].
    destruct (g b2) as [[xb3 d23] | ] eqn:H23; [ | discriminate].
    inv H13.
    exists b2; eexists; eauto.
  - intros b1 b3 (b2 & [d2 H12] & [d3 H23]).
    exists (d2 + d3).
    unfold compose_meminj.
    rewrite H12, H23.
    reflexivity.
Qed.

Lemma block_inject_sameofs_compose f g:
  subrel
    (rel_compose (block_inject_sameofs f) (block_inject_sameofs g))
    (block_inject_sameofs (compose_meminj f g)).
Proof.
  intros b1 b3 (b2 & H12 & H23).
  red in H12, H23 |- *.
  unfold compose_meminj. rewrite H12, H23.
  reflexivity.
Qed.

Lemma flat_inj_idemp thr:
  compose_meminj (Mem.flat_inj thr) (Mem.flat_inj thr) = Mem.flat_inj thr.
Proof.
  apply Axioms.functional_extensionality; intros b.
  unfold compose_meminj, Mem.flat_inj.
  destruct Mem.sup_dec eqn:Hb; eauto.
  rewrite Hb.
  reflexivity.
Qed.

Program Definition cklr_compose' (R1 R2: cklr'): cklr' :=
  {|
    world := world R1 * world R2;
    wacc := wacc R1 * wacc R2;
    mi w := compose_meminj (mi R1 (fst w)) (mi R2 (snd w));
    match_stbls w := rel_compose (match_stbls R1 (fst w)) (match_stbls R2 (snd w));
    match_mem w := rel_compose (match_mem R1 (fst w)) (match_mem R2 (snd w));
  |}.

Next Obligation.
  rauto.
Qed.

(** mi_acc_separated *)
Next Obligation.
  rename w1 into w2'.
  rename w0 into w1'.
  rename w into w1.
  intros b1 b2 delta Hw Hw'.

  destruct H as (m & Hm1 & Hm2).
  destruct H0 as [HR1 HR2].
  cbn in *.

  specialize (mi_acc_separated R1 _ _ _ _ Hm1 HR1) as sep1.
  specialize (mi_acc_separated R2 _ _ _ _ Hm2 HR2) as sep2.
  unfold inject_separated in sep1, sep2.
  unfold compose_meminj in Hw, Hw'.
  destruct (mi R1 w1' b1) as [[b11' delta11'] |] eqn:HR1w1'; [|discriminate].
  destruct (mi R2 w2' b11') as [[b22' delta22'] |] eqn:HR2w2'; [|discriminate].
  injection Hw'. clear Hw'. intros; subst delta b22'.
  destruct (mi R1 w1 b1) as [[b11 delta11] |] eqn:HR1w1.
  - destruct (mi R2 w2 b11) as [[b22 delta22] |] eqn:HR2w2.
    discriminate.
    assert (HR1w1'_alt: mi R1 w1' b1 = Some (b11, delta11)).
    { eapply mi_acc; eauto. }
    rewrite HR1w1' in HR1w1'_alt. inv HR1w1'_alt.
    destruct (sep2 _ _ _ HR2w2 HR2w2') as [Hnvb11 Hnvb2].
    split; [|assumption].
    contradict Hnvb11.
    eapply (cklr_valid_block _ _ _ _ Hm1); eauto.
    eexists. eauto.
  - destruct (sep1 _ _ _ HR1w1 HR1w1') as [Hnvb1 Hnvb11'].
    split. auto.
    destruct (mi R2 w2 b11') as [[b22 delta22] |] eqn:HR2w2.
    + contradict Hnvb11'.
      assert (HR2w2'_alt: mi R2 w2' b11' = Some (b22, delta22)).
      { eapply mi_acc; eauto. }
      rewrite HR2w2' in HR2w2'_alt. inv HR2w2'_alt.
      eapply cklr_valid_block; eauto.
      eexists. eauto.
    + eapply sep2; eauto.
Qed.

Next Obligation.
  intros [w12 w23] [w12' w23'] [H12 H23]. cbn.
  eapply rel_compose_subrel; rauto.
Qed.

Next Obligation.
  cbn. intros se1 se3 (se2 & Hse12 & Hse23).
  apply match_stbls_proj in Hse12.
  apply match_stbls_proj in Hse23.
  eapply Genv.match_stbls'_compose; eauto.
Qed.

Next Obligation.
  destruct H as (sei & Hse1i & Hsei2), H0 as (mi & Hm1i & Hmi2). cbn in *.
  eapply (match_stbls_support R2); eauto.
  eapply (match_stbls_support R1); eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) lo hi.
  edestruct (cklr_alloc R1 w12 m1 m2 Hm12 lo hi)
    as (w12' & Hw12' & Hm12' & Hb12).
  edestruct (cklr_alloc R2 w23 m2 m3 Hm23 lo hi)
    as (w23' & Hw23' & Hm23' & Hb23).
  exists (w12', w23'); split; [rauto | ].
  rstep. simpl. split.
  - eexists; split; rauto.
  - red. apply block_inject_sameofs_compose.
    eexists; split; eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [[b1 lo1] hi1] [[b3 lo3] hi3] H.
  apply ptrrange_inject_compose in H.
  destruct H as ([[b2 lo2] hi2] & Hr12 & Hr23).
  simpl in *. red.
  destruct (Mem.free m1 _ _ _) as [m1'|] eqn:H1; [|constructor].
  generalize (cklr_free). intro R.
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23').
  split; [rauto | ].
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  red. simpl in *. unfold klr_pullw.
  rewrite val_inject_compose.
  apply option_le_compose.
  generalize (cklr_load). intro R.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  simpl in *. red. unfold klr_pullw in *.
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  apply val_inject_compose in Hv. destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.store chunk m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  generalize (cklr_store). intro R.
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr sz.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  unfold k1, klr_pullw. simpl in *.
  eapply option_le_subrel. (* XXX coqrel *)
  {
    apply list_subrel.
    apply memval_inject_compose.
  }
  rewrite list_rel_compose.
  apply option_le_compose.
  generalize (cklr_loadbytes). intro R.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  unfold k1, klr_pullw in *. simpl in *.
  apply rptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  rewrite memval_inject_compose in Hv. apply list_rel_compose in Hv.
  destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.storebytes m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm [b1 o1] [b3 o3] Hptr pk pe.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  etransitivity. instantiate (1:= Mem.perm m2 b2 o2 pk pe).
  generalize (cklr_perm R1). intro. rauto.
  generalize (cklr_perm R2). intro. rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm b1 b3 Hb.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply block_inject_compose in Hb. destruct Hb as (b2 & Hb12 & Hb23).
  etransitivity; rauto.
Qed.

Next Obligation. (* no overlap *)
  intros a1 a2 da b1 b2 db oa ob Hab1 Ha Hb Hoa Hob. simpl in *.
  destruct H as (mx & Hm1x & Hmx2).
  unfold compose_meminj in *.
  destruct (mi R1 w a1) as [[ax da1x] | ] eqn:Ha1x; [ | discriminate].
  destruct (mi R2 w0 ax) as [[ay dax2] | ] eqn:Hax2; [ | discriminate].
  inv Ha.
  destruct (mi R1 w b1) as [[bx db1x] | ] eqn:Hb1x; [ | discriminate].
  destruct (mi R2 w0 bx) as [[bz dbz2] | ] eqn:Hbx2; [ | discriminate].
  inv Hb.
  assert (Mem.perm mx ax (oa + da1x) Max Nonempty).
  { revert Hoa. generalize (cklr_perm R1). intro. repeat rstep. constructor. eauto. }
  assert (Mem.perm mx bx (ob + db1x) Max Nonempty).
  { revert Hob. generalize (cklr_perm R1). intro. repeat rstep. constructor; eauto. }
  edestruct (cklr_no_overlap R1 w m1 mx); eauto.
  - edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
    rewrite !Z.add_assoc.
    eauto.
  - destruct (eq_block ax bx); eauto.
    + right. assert (dax2 = dbz2) by congruence. extlia.
    + edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
      rewrite !Z.add_assoc.
      eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H1. simpl in H1.
  destruct (mi R1 w b1) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H1.
  simpl in *.
  assert (d1I >= 0 /\ 0 <= ofs1 + d1I <= Ptrofs.max_unsigned) as [? ?].
  { eapply (cklr_representable R1); eauto. }
  assert (dI2 >= 0 /\ 0 <= (ofs1 + d1I) + dI2 <= Ptrofs.max_unsigned).
  { eapply (cklr_representable R2); eauto.
    revert H0. generalize (cklr_perm R1). intro.
    repeat rstep.
    - constructor; eauto.
    - replace (ofs1 + d1I -1) with (ofs1 - 1 + d1I) by extlia.
      constructor; eauto. }
  extlia.
Qed.

Next Obligation. (* aligned_area_inject *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H5. simpl in H5.
  destruct (mi R1 w b) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H5.
  simpl in *.
  rewrite Z.add_assoc.
  eapply (cklr_aligned_area_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b (x - d1I) Cur Nonempty). { eapply H3. extlia. }
    revert H. generalize (cklr_perm R1). intro. repeat rstep.
    replace x with (x - d1I + d1I) at 2 by extlia.
    constructor; eauto.
  - eapply (cklr_aligned_area_inject R1); eauto.
Qed.

Next Obligation. (* disjoint_or_equal_inject *)
  simpl in *.
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in *.
  destruct (mi R1 w b1) as [[b1I d1] | ] eqn:Hb1I; [ | discriminate].
  destruct (mi R2 w0 b1I) as [[xb1' d1'] | ] eqn:Hb1'; [ | discriminate].
  inv H0.
  destruct (mi R1 w b2) as [[b2I d2] | ] eqn:Hb2I; [ | discriminate].
  destruct (mi R2 w0 b2I) as [[xb2' d2'] | ] eqn:Hb2'; [ | discriminate].
  inv H1.
  rewrite !Z.add_assoc.
  eapply (cklr_disjoint_or_equal_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b1 (x - d1) Max Nonempty). { eapply H2. extlia. }
    revert H. generalize (cklr_perm R1). intro. repeat rstep.  
    replace x with (x - d1 + d1) at 2 by extlia.
    constructor; eauto.
  - intros x Hx.
    assert (Mem.perm m b2 (x - d2) Max Nonempty). { eapply H3. extlia. }
    revert H. generalize (cklr_perm R1). intro. repeat rstep.
    replace x with (x - d2 + d2) at 2 by extlia.
    constructor; eauto.
  - eapply (cklr_disjoint_or_equal_inject R1); eauto.
Qed.

Next Obligation. (* perm inv *)
  simpl in *.
  destruct H as (mi & Hm1i & Hmi2).
  apply ptr_inject_compose in H0 as ([bi ofsi] & Hp1i & Hpi2).
  edestruct (cklr_perm_inv R2); eauto.
  - eapply (cklr_perm_inv R1); eauto.
  - right. intros Hm1. apply H. revert Hm1. generalize (cklr_perm R1). intro. rauto.
Qed.


Next Obligation. (* sup include *)
  destruct H as (mI & Hm1I & Hm2I).
  destruct H0 as ([w' w0'] & Hw' & mI' & Hm1I' & Hm2I').
  cbn [fst snd] in *. unfold Ple in *.
  inv Hw'; cbn in *.
  etransitivity; eapply cklr_sup_include; eauto; eexists; split; eauto.
Qed.

Declare Scope cklr_scope.
Bind Scope cklr_scope with cklr.
Delimit Scope cklr_scope with cklr.
Infix "#" := cklr_compose' (at level 30, right associativity) : cklr_scope.

(** ** Properties *)

(** Monotonicity *)

Global Instance cklr_compose_subcklr:
  Proper (subcklr ++> subcklr ++> subcklr) (@cklr_compose).
Proof.
  intros R12 R12' H12 R23 R23' H23.
  intros [w12 w23] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23). simpl in *.
  specialize (H12 w12 se1 se2 m1 m2 Hse12 Hm12) as (w12' & Hse12' & Hm12' & Hincr12 & H12).
  specialize (H23 w23 se2 se3 m2 m3 Hse23 Hm23) as (w23' & Hse23' & Hm23' & Hincr23 & H23).
  exists (w12', w23'); simpl.
  repeat apply conj; try rauto.
  - eexists; split; eauto.
  - eexists; split; eauto.
  - intros [v12' v23'] m1' m3' (m2' & Hm'12 & Hm'23) [Hwv12 Hwv23].
    specialize (H12 v12' m1' m2' Hm'12 Hwv12) as (v12 & Hm'12' & Hwv12' & Hi12').
    specialize (H23 v23' m2' m3' Hm'23 Hwv23) as (v23 & Hm'23' & Hwv23' & Hi23').
    simpl in *.
    exists (v12, v23).
    split; [ | split].
    + eexists; split; eauto.
    + rauto.
    + rauto.
Qed.

(*
(** Associativity *)

Require Import Axioms.
Lemma cklr_compose_assoc R1 R2 R3:
  subcklr ((R1 @ R2) @ R3) (R1 @ (R2 @ R3)).
Proof.
  intros [[w1 w2] w3] sea sed ma md (seb & (sec & Hse1 & Hse2) & Hse3) (mb & (mc & Hm1 & Hm2) & Hm3).
  simpl in *.
  exists (w1, (w2, w3)).
  repeat apply conj.
  - repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - rewrite compose_meminj_assoc. apply inject_incr_refl.
  - intros (w1' & w2' & w3') ma' md' (mb' & Hm1' & (mc' & Hm2' & Hm3')).
    intros (Hw1 & Hw2 & Hw3).
    simpl in *.
    exists ((w1', w2'), w3').
    split; [ | split].
    + repeat (econstructor; eauto).
    + rauto.
    + rewrite compose_meminj_assoc. apply inject_incr_refl.
Qed.
*)

(** * Properties of [cc_c] *)

Global Instance cc_c_ref':
  Monotonic (@cc_c') (subcklr' ++> ccref').
Proof.
  intros Q R HQR. red in HQR |- *.
  intros w se1 se2 q1 q2 Hse Hq.
  destruct Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm].
  specialize (HQR w se1 se2 m1 m2 Hse Hm) as (wr & HseR & HmR & Hincr & HQR').
  exists wr. simpl in *. repeat apply conj; auto.
  - constructor; eauto.
  - intros r1 r2 (wr' & Hw' & Hr). destruct Hr as [v1 v2 m1' m2' Hvres Hm'].
    specialize (HQR' wr' m1' m2' Hm' Hw') as (w' & HmQ' & HwQ' & Hincr').
    eexists. split; eauto. constructor; eauto.
Qed.

Lemma match_c_query_compose R12 R23 w12 w23:
  eqrel
    (cc_c_query' (cklr_compose' R12 R23) (w12, w23))
    (rel_compose (cc_c_query' R12 w12) (cc_c_query' R23 w23)).
Proof.
  split.
  - intros _ _ [vf1 vf3 sg vargs1 vargs3 m1 m3 Hvf Hvargs Hm].
    simpl in *.
    apply val_inject_compose in Hvf. destruct Hvf as (vf2 & Hvf12 & Hv23).
    apply val_inject_list_compose in Hvargs. destruct Hvargs as (vargs2 & ? & ?).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (cq vf2 sg vargs2 m2); split; constructor; simpl; eauto.
    destruct Hvf12; congruence.
  - intros q1 q3 (q2 & Hq12 & Hq23).
    destruct Hq23 as [vf1 vf2 sg vargs2 vargs3 m2 m3 Hvf Hvargs23 Hm23 Hvf1].
    inv Hq12.
    constructor; simpl.
    + apply val_inject_compose. ercompose; eauto.
    + apply val_inject_list_compose. ercompose; eauto.
    + ercompose; eauto.
    + auto.
Qed.
(*
Lemma cc_c_compose R12 R23:
  cceqv' (cc_c' (R12 R23)) (cklr_compose' (cc_c' R12) (cc_c' R23)).
Proof.
  split.
  - intros [w12 w23] se1 se3 q1 q3 (se2 & Hse12 & Hse23) Hq.
    apply match_c_query_compose in Hq as (q2 & Hq12 & Hq23).
    exists (se2, w12, w23).
    repeat apply conj; cbn; eauto.
    intros r1 r3 (r2 & (w12' & Hw21' & Hr12) & (w23' & Hw23' & Hr23)).
    exists (w12', w23'). split. constructor; cbn; auto.
    destruct Hr12; inv Hr23.
    constructor; cbn; eauto.
    apply val_inject_compose; eauto.
  - intros [[se2 w12] w23] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    cbn in *. exists (w12, w23). repeat apply conj; eauto.
    + apply match_c_query_compose; eauto.
    + intros r1 r3 ([w12' w23'] & Hw' & Hr).
      destruct Hr. cbn in *.
      apply val_inject_compose in H.
      destruct Hw' as [? ?], H as (vi & ? & ?), H0 as (mi & ? & ?).
      exists (cr vi mi).
      split; eexists; constructor; eauto; constructor; eauto.
Qed.
 *)

(** * easy part : compose injp' ⋅ injp ≡ injp' *)

(* Maybe we can trans cklr into cklr'. Or we can have a more clean solution later *)
(*
Definition callconv_gen (R : cklr) : cklr' :=
  {|
    world := CKLR.world R;
    wacc := CKLR.wacc R;
    mi w := (CKLR.mi R) w;
    match_stbls w := (CKLR.match_stbls R) w;
    match_mem w := (CKLR.match_mem R) w;
  |}.
*)

Section SYMTBL_CONSTR.

Variable se1 se3 : Genv.symtbl.
Variable f : meminj.

Hypothesis MSE: Genv.match_stbls' f se1 se3.
  
Fixpoint remove_sup (se : Genv.symtbl) (s : sup) :=
  match s with
  | nil => se
  | hd :: tl => remove_sup (Genv.remove_global se hd) tl
  end.

Definition unmap_se1 := filter (fun b => if f b then false else true) (Genv.genv_sup se1).

Definition se2 := remove_sup se1 unmap_se1.

Lemma se2_public : Genv.public_symbol se1 = Genv.public_symbol se2.
Admitted.

Lemma se2_sup : forall b, sup_In b (Genv.genv_sup se2) <-> sup_In b (Genv.genv_sup se1) /\ f b <> None.
Admitted.

Lemma se2_symb : forall b1 b2 d, f b1 = Some (b2, d) ->
                            forall id, Genv.find_symbol se1 id = Some b1 <-> Genv.find_symbol se2 id = Some b1.
Admitted.

Lemma se2_info : forall b1 b2 d, f b1 = Some (b2, d) ->
                            Genv.find_info se1 b1 = Genv.find_info se2 b1.
Admitted.

Theorem SUP : Mem.sup_include (Genv.genv_sup se2) (Genv.genv_sup se1).
Proof.
  red. intros. apply se2_sup in H. apply H.
Qed.

Theorem Hse1 : Genv.match_stbls' (meminj_dom f) se1 se2.
Proof.
  constructor.
  - intros. rewrite se2_public. reflexivity.
  - intros. unfold meminj_dom in H0. destruct (f b1); simpl in H0; try congruence.
  - intros. apply se2_sup in H. destruct H. exists b2. unfold meminj_dom.
    destruct (f b2) eqn:H1. reflexivity. congruence.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    eapply se2_symb; eauto.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    eapply se2_info; eauto.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    split; intros. eapply se2_sup; eauto. split; eauto. congruence.
    apply se2_sup in H. apply H.
Qed. (* ok *)

Theorem Hse2 : Genv.match_stbls f se2 se3.
Proof.
  constructor.
  - intros. inversion MSE. etransitivity. eauto. rewrite se2_public. reflexivity.
  - intros. apply se2_sup in H. destruct H. destruct (f b1) as [[b2 d]|] eqn:Hinj; try congruence.
    inv MSE. exploit mge_dom'; eauto. intro. subst. eauto.
  - intros. inv MSE. eapply mge_img'; eauto.
  - intros. inversion MSE. setoid_rewrite <- se2_symb; eauto.
    eapply mge_symb'; eauto.
  - intros. inversion MSE. setoid_rewrite <- se2_info; eauto.
    eapply mge_info'; eauto.
  - intros. inversion MSE. split; intros. eapply mge_separated'; eauto.
    eapply se2_sup; eauto. eapply se2_sup. split; eauto.
    eapply mge_separated'; eauto. congruence.
Qed.

End SYMTBL_CONSTR.


Theorem injp'_injp_ref1:
  ccref'  (cc_c' injp') (cc_compose_2 (cc_c' injp') (cc_c injp)).
Proof.
  red. intros w se1 se3 q1 q2 Hse Hq.
  inv Hse. inv Hq. cbn in H2, H3. inv H4. rename m0 into m1. rename m3 into m2.
  set (se2 := se2 se1 f).
  exists (se2, (injpw (meminj_dom f) (Genv.genv_sup se1) (Genv.genv_sup se2) m1 m1 (mem_inject_dom f m1 m2 Hm)),
      (injpw f (Genv.genv_sup se2) (Genv.genv_sup se3) m1 m2 Hm)).
  repeat apply conj.
  - split; constructor; eauto.
    eapply Hse1; eauto.
    eapply Mem.sup_include_trans. eapply SUP; eauto. eauto.
    eapply Hse2; eauto.
    eapply Mem.sup_include_trans. eapply SUP; eauto. eauto.
  - exists (cq vf1 sg vargs1 m1). split.
    econstructor; cbn; eauto.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    constructor; cbn; eauto.
  - intros r1 r3 [r2 [Hr1 Hr2]].
    destruct Hr1 as [w12' [Hw12 Hr1]]. destruct Hr2 as [w23' [Hw23 Hr2]].
    destruct w12' as [f12' ? ? m1' m2' Hm12']. destruct w23' as [f23' ? ? m2'' m3' Hm23'].
    inv Hw12. inv Hw23. cbn in *.
    inv Hr1. inv Hr2. cbn in *. inv H6. inv H11.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'1 into m3'.
    eexists (injpw (compose_meminj f12' f23') (Genv.genv_sup se1) (Genv.genv_sup se3) m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H6. split. red. unfold meminj_dom. rewrite H6. reflexivity. eauto.
      * red. intros. unfold compose_meminj.
        erewrite H21. erewrite H29; eauto.
        2: unfold meminj_dom; rewrite H6; reflexivity.
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H22; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H30; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
Qed.

Lemma compose_meminj_midvalue: forall j1 j2 v1 v3,
    Val.inject (compose_meminj j1 j2) v1 v3 ->
    exists v2, Val.inject j1 v1 v2 /\ Val.inject j2 v2 v3.
Proof.
  intros. inv H.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  unfold compose_meminj in H0.
  destruct (j1 b1) as [[b2' d1]|] eqn:M1; try congruence.
  destruct (j2 b2') as [[b3' d2]|] eqn:M2; inv H0.
  eexists. split. econstructor; eauto.
  econstructor; eauto. rewrite add_repr.
  rewrite Ptrofs.add_assoc. auto.
  exists Vundef. split; constructor.
Qed.

Theorem injp'_injp_ref2:
  ccref' (cc_compose_2 (cc_c' injp') (cc_c injp)) (cc_c' injp') .
Proof.
  red.
  intros w se1 se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2 w12] w23].
  destruct MSTBL13 as [MSTBL12 MSTBL23].
  destruct MMEM13 as [q2 [MMEM12 MMEM23]].
  inv MMEM12. inv H1. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H9. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H8, H6, MSTBL23, MSTBL12, H, H0.
  assert (gs0 = gs2).
  inv MSTBL12. inv MSTBL23. eauto. subst gs0.                
  exists ((injpw (compose_meminj j12 j23) gs1 gs3
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl. repeat apply conj.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls'_stbls_compose; eauto.
  - constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
     eapply CKLRAlgebra.val_inject_list_compose.
     econstructor; eauto.
  - intros r1 r3 [w13' [INCR13' Hr13]].
    inv Hr13. inv H3. cbn in H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2' into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? ? ?  RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst. cbn in *.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' j23' gs2 m2'_sup INJ12 SUPINCL2).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    admit.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    admit.
    rename gs0 into gs1. rename gs4 into gs3.
    set (w1' := injpw j12' gs1 gs2 m1' m2' INJ12').
    set (w2' := injpw j23' gs2 gs3 m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (fun b z => loc_out_of_reach j12 m1 b z /\ ~ sup_In b gs2) m2 m2').
    eapply UNCHANGE21; eauto.
    admit.
    exists (cr vres2 m2'). split.
    + exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      admit.
      eapply MAXPERM2; eauto.
      admit.
      eapply Mem.unchanged_on_implies; eauto.
      intros. destruct H3. split; eauto. red. unfold compose_meminj.
      rewrite H3. reflexivity.
      constructor; eauto. constructor; eauto.
    +
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto. admit.
      eapply MAXPERM2; eauto. admit.
      eapply UNCHANGE22; eauto. admit. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Admitted.

Theorem injp'_injp_c_equiv:
  cceqv' (cc_c' injp') (cc_compose_2 (cc_c' injp') (cc_c injp)).
Proof. split. apply injp'_injp_ref1. apply injp'_injp_ref2. Qed.

(** * hard part : compose injp ⋅ injp' ≡ injp' *)

Definition source_inj (se: Genv.symtbl) (f : meminj) :=
  fun b => if Mem.sup_dec b (Genv.genv_sup se) then
        Some (b,0) else meminj_dom f b.

Lemma source_inj_meminj_dom_incr : forall se f,
    inject_incr (meminj_dom f) (source_inj se f).
Proof.
  intros. intro. intros.
  unfold source_inj.
  unfold meminj_dom in *.
  destruct (f b); try discriminate. inv H.
  destruct Mem.sup_dec; eauto.
Qed.

Global Instance source_inj_incr se:
  Monotonic (@source_inj se) (inject_incr ++> inject_incr).
Proof.
  intros f g Hfg b b' delta Hb.
  unfold source_inj in *.
  destruct (Mem.sup_dec). eauto.
  eapply meminj_dom_incr; eauto.
Qed.

Lemma source_inj_compose se f:
  compose_meminj (source_inj se f) f = f.
Proof.
  apply Axioms.functional_extensionality; intros b.
  unfold compose_meminj, source_inj, meminj_dom.
  destruct (Mem.sup_dec).
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  rewrite Hfb.
  replace (0 + ofs) with ofs by extlia.
  reflexivity.
Qed.

Lemma block_inject_dom se f b1 b2:
  block_inject f b1 b2 ->
  block_inject (source_inj se f) b1 b1.
Proof.
  unfold source_inj,meminj_dom.
  intros (delta & Hb).
  exists 0.
  rewrite Hb; eauto.
  destruct Mem.sup_dec; eauto.
Qed.

Lemma val_inject_dom se f v1 v2:
  Val.inject f v1 v2 ->
  Val.inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  - unfold source_inj, meminj_dom.
    rewrite H. destruct Mem.sup_dec; eauto.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Lemma memval_inject_dom se f v1 v2:
  memval_inject f v1 v2 ->
  memval_inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  eapply val_inject_dom; eauto.
Qed.

Lemma val_inject_list_dom se f vs1 vs2:
  Val.inject_list f vs1 vs2 ->
  Val.inject_list (source_inj se f) vs1 vs1.
Proof.
  induction 1; constructor; eauto using val_inject_dom.
Qed.

Lemma global_blocks_pointer:
  forall se m b ofs q n b' ofs',
    Maps.ZMap.get ofs (NMap.get b (Mem.mem_contents m)) = (Fragment (Vptr b' ofs') q n) ->
    sup_In b (Genv.genv_sup se) ->
    sup_In b' (Genv.genv_sup se).
Proof.
Admitted.

Lemma mem_mem_inj_dom se f m1 m2:
  Mem.mem_inj f m1 m2 ->
  Mem.mem_inj (source_inj se f) m1 m1.
Proof.
  intros H.
  split.
  - unfold source_inj, meminj_dom. intros b1 b2 delta ofs k p Hb1 Hp.
    destruct Mem.sup_dec; destruct (f b1); inv Hb1;
    replace (ofs + 0) with ofs by extlia; auto.
  - unfold source_inj, meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (Mem.sup_dec); destruct (f b1) as [[b1' delta'] | ]; inv Hb1;
    eauto using Z.divide_0_r.
  - unfold source_inj, meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (Mem.sup_dec) ; destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
    replace (ofs + 0) with ofs by extlia.
    {
      set (mv:= (Maps.ZMap.get ofs (NMap.get b2 (Mem.mem_contents m1)))).
      destruct mv eqn:Hmem; constructor.
      destruct v eqn:Hv; econstructor.
      rewrite pred_dec_true. reflexivity.
      eapply global_blocks_pointer; eauto.
      rewrite Ptrofs.add_zero. reflexivity.
    }
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
Qed.

Lemma mem_source_inj se f m1 m2:
  Mem.sup_include (Genv.genv_sup se) (Mem.support m1) ->
  Mem.inject f m1 m2 ->
  Mem.inject (source_inj se f) m1 m1.
Proof.
  intros H.
  split.
  - eapply mem_mem_inj_dom.
    eapply Mem.mi_inj; eauto.
  - unfold source_inj, meminj_dom. intros.
    erewrite Mem.mi_freeblocks; eauto.
    rewrite pred_dec_false; eauto.
    intro. apply H1. apply H. eauto.
  - unfold source_inj, meminj_dom; intros.
    destruct Mem.sup_dec; eauto. inv H1. apply H; eauto.
    destruct (f b) as [[b'' delta'] | ] eqn:Hb; inv H1.
    eapply Mem.valid_block_inject_1; eauto.
  - red. unfold source_inj, meminj_dom. intros.
    destruct Mem.sup_dec; inv H2; eauto.
    destruct Mem.sup_dec; inv H3; eauto.
    destruct (f b2); inv H6; eauto.
    destruct Mem.sup_dec; inv H3; eauto.
    destruct (f b1); inv H7; eauto.                              
    destruct (f b1); inv H7.
    destruct (f b2); inv H6.
    eauto.
  - unfold source_inj, meminj_dom. intros.
    destruct (Mem.sup_dec); eauto. inv H1.
    split; try extlia. rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
    destruct (f b); inv H1.
    split; try extlia.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  - unfold source_inj, meminj_dom. intros.
    destruct Mem.sup_dec; inv H1.
    rewrite Z.add_0_r in H2; eauto.
    destruct (f b1); inv H4.
    rewrite Z.add_0_r in H2; eauto.
Qed.

Lemma match_stbls'_dom f se1 se2:
  Genv.match_stbls' f se1 se2 ->
  Genv.match_stbls' (source_inj se1 f) se1 se1.
Proof.
  intros Hse. unfold source_inj, meminj_dom. split; eauto; intros.
  - rewrite pred_dec_true in H0; eauto. inv H0. reflexivity.
  - eexists. rewrite pred_dec_true; eauto.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
Qed.

Lemma loc_unmapped_dom f b ofs:
  loc_unmapped (meminj_dom f) b ofs <->
  loc_unmapped f b ofs.
Proof.
  unfold meminj_dom, loc_unmapped.
  destruct (f b) as [[b' delta] | ].
  - split; discriminate.
  - reflexivity.
Qed.

Definition source_world f m1 m2 (Hm: Mem.inject f m1 m2) (se:Genv.symtbl) (Hse: Mem.sup_include (Genv.genv_sup se) (Mem.support m1)) :=
     injpw (source_inj se f) (Genv.genv_sup se) (Genv.genv_sup se) m1 m1 (mem_source_inj se f m1 m2 Hse Hm).

Lemma match_stbls_dom' f se1 se2:
  Genv.match_stbls' f se1 se2 ->
  Genv.match_stbls (source_inj se1 f) se1 se1.
Proof.
  intros Hse. unfold source_inj. unfold meminj_dom. split; eauto; intros.
  - destruct Mem.sup_dec; try congruence. eauto.
  - inv Hse. exists b2. destruct Mem.sup_dec; try congruence.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
Qed.
(*
Section INJECT_CONSTR.

Variable se1 se2 : Genv.symtbl.
Variable f : meminj.

Hypothesis MSE: Genv.match_stbls' f se1 se2.
*)

    
  


Theorem injp_injp'_ref1:
  ccref'  (cc_c' injp') (cc_compose_1 (cc_c injp) (cc_c' injp')).
Proof.
  red. intros w se1 se3 q1 q2 Hse Hq.
  inv Hse. inv Hq. cbn in H2, H3. inv H4. rename m0 into m1. rename m3 into m2.
  exists (se1, (injpw (source_inj se1 f) (Genv.genv_sup se1) (Genv.genv_sup se1) m1 m1 (mem_source_inj se1 f m1 m2 H0 Hm)),
      (injpw f (Genv.genv_sup se1) (Genv.genv_sup se3) m1 m2 Hm)).
  repeat apply conj.
  - split. constructor; eauto. eapply match_stbls_dom'; eauto.
    constructor; eauto.
  - exists (cq vf1 sg vargs1 m1). split.
    constructor; cbn; eauto.
    eapply val_inject_dom; eauto. eapply val_inject_list_dom; eauto.
    constructor; cbn; eauto.
  - intros r1 r3 [r2 [Hr1 Hr2]].
    destruct Hr1 as [w12' [Hw12 Hr1]]. destruct Hr2 as [w23' [Hw23 Hr2]].
    destruct w12' as [f12' ? ? m1' m2' Hm12']. destruct w23' as [f23' ? ? m2'' m3' Hm23'].
    inv Hw12. inv Hw23. cbn in *.
    inv Hr1. inv Hr2. cbn in *. inv H6. inv H11.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'1 into m3'.
    eexists (injpw (compose_meminj f12' f23') (Genv.genv_sup se1) (Genv.genv_sup se3) m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H6. split. red. unfold source_inj.
        rewrite pred_dec_false. unfold meminj_dom. rewrite H6. reflexivity. eauto. eauto.
      * red. intros. unfold compose_meminj.
        erewrite H21. erewrite H29; eauto.
        2: { unfold source_inj, meminj_dom. destruct Mem.sup_dec. reflexivity.
             rewrite H6. reflexivity. }
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H22; eauto. unfold source_inj, meminj_dom.
        rewrite pred_dec_false.
        rewrite Hb. auto.
        {
          intro.
          erewrite H21 in Hb1.
          2: { unfold source_inj.  rewrite pred_dec_true. eauto.  eauto. }
          inv Hb1.
          exploit H30; eauto. intros [A B].
          apply A. eapply H0; eauto.
        }
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H30; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
Qed.

Theorem injp_injp'_ref2:
  ccref' (cc_compose_1 (cc_c injp) (cc_c' injp')) (cc_c' injp') .
Proof.
  red.
  intros w se1 se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2 w12] w23].
  destruct MSTBL13 as [MSTBL12 MSTBL23].
  destruct MMEM13 as [q2 [MMEM12 MMEM23]].
  inv MMEM12. inv H1. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H9. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H8, H6, MSTBL23, MSTBL12, H, H0.
  assert (gs0 = gs2).
  inv MSTBL12. inv MSTBL23. eauto. subst gs0.                
  exists ((injpw (compose_meminj j12 j23) gs1 gs3
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl. repeat apply conj.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_stbls'_compose; eauto.
  - constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
     eapply CKLRAlgebra.val_inject_list_compose.
     econstructor; eauto.
  - intros r1 r3 [w13' [INCR13' Hr13]].
    inv Hr13. inv H3. cbn in H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2' into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? ? ?  RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst. cbn in *.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' j23' gs2 m2'_sup INJ12 SUPINCL2).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    admit.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    admit.
    rename gs0 into gs1. rename gs4 into gs3.
    set (w1' := injpw j12' gs1 gs2 m1' m2' INJ12').
    set (w2' := injpw j23' gs2 gs3 m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (fun b z => loc_out_of_reach j12 m1 b z /\ ~ sup_In b gs2) m2 m2').
    eapply UNCHANGE21; eauto.
    admit.
    exists (cr vres2 m2'). split.
    + exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      admit.
      eapply MAXPERM2; eauto.
      admit.
      eapply Mem.unchanged_on_implies; eauto.
      intros. destruct H3. split; eauto. red. unfold compose_meminj.
      rewrite H3. reflexivity.
      constructor; eauto. constructor; eauto.
    +
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto. admit.
      eapply MAXPERM2; eauto. admit.
      eapply UNCHANGE22; eauto. admit. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Admitted.

Theorem refinement_injp_injp'_c:
  cceqv' (cc_c' injp') (cc_compose_1 (cc_c injp) (cc_c' injp')).
Proof. split. eapply injp_injp'_ref1. apply injp_injp'_ref2. Qed.




