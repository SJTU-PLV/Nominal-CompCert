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

Require Import CallconvNew.

Require Import RelClasses.


(* Set Asymmetric Patterns. *)
(* Set Implicit Arguments. *)
 Generalizable All Variables. 

Import GS.


Section COMP_FSIM.

  Context `(cc1: callconv lis lin) `(cc2: callconv lin lif)
          (Ls: semantics lis lis) (Ln: semantics lin lin) (Lf: semantics lif lif).
  Context (H1: fsim_components cc1 Ls Ln)
          (H2: fsim_components cc2 Ln Lf).

  Inductive compose_fsim_match_states se1 se3:
    ccworld (cc_compose cc1 cc2) ->
    gworld (cc_compose cc1 cc2) ->
    (fsim_index H2 * fsim_index H1) ->
    state Ls -> state Lf -> Prop :=
  | compose_match_states_intro se2 s1 s2 s3 i1 i2 wb1 wb2 wp1 wp2
    (HS1: fsim_match_states H1 se1 se2 wb1 wp1 i1 s1 s2)
    (HS2: fsim_match_states H2 se2 se3 wb2 wp2 i2 s2 s3):
    compose_fsim_match_states se1 se3 (se2, (wb1, wb2)) (wp1,wp2) (i2, i1) s1 s3.

  (** Is this necessary or useful? *)
  (*Inductive compose_fsim_inv:
    gworld (cc_compose cc1 cc2) -> gworld (cc_compose cc1 cc2) -> Prop :=
  | compose_fsim_inv_intro wa1 wa2 wb1 wb2
      (INV1: fsim_invariant H1 wa1 wb1)
      (INV2: fsim_invariant H2 wa2 wb2):
    compose_fsim_inv (wa1, wa2) (wb1, wb2).*)

  Lemma st_fsim_vcomp':
    fsim_components (cc_compose cc1 cc2) Ls Lf.
  Proof.
    set (ff_order := lex_ord (Relation_Operators.clos_trans
                                _ (fsim_order H2)) (fsim_order H1)).
    apply GS.Forward_simulation with ff_order compose_fsim_match_states.
    - rewrite (fsim_skel H1); apply (fsim_skel H2).
    - intros se1 se3 [se2 [wb1 wb2]] [Hse01 Hse02] Hse1.
      pose proof (@fsim_lts _ _ _ _ _ H1 se1 se2 wb1 Hse01 Hse1) as X1.
      assert (Hse2: Genv.valid_for (skel Ln) se2).
      { rewrite <- (fsim_skel H1). eapply match_senv_valid_for; eauto. }
      pose proof (@fsim_lts _ _ _ _ _ H2 se2 se3 wb2 Hse02 Hse2) as X2.
      clear Hse1 Hse2. constructor.
      + intros q1 q3 (q2 & Hq1 & Hq2).
        etransitivity; eauto using fsim_match_valid_query.
      + intros q1 q3 s1 (q2 & Hq12 & Hq23) Hi Hse.
        destruct Hse as (Hse1 & Hse2). cbn in *.
        edestruct (@fsim_match_initial_states lis) as (i & s2 & A & B); eauto.
        edestruct (@fsim_match_initial_states lin) as (i' & s3 & C & D); eauto.
        eexists (i', i), s3. split; eauto.
        econstructor; eauto.
      + intros (wb1' & wb2') (i2, i1) s1 s3 r1 Hs H.
        inv Hs.
        edestruct (@fsim_match_final_states lis) as (r2 & Hr2 & A); eauto.
        edestruct (@fsim_match_final_states lin) as (r3 & Hr3 & B); eauto.
        destruct A as (R1 & I1).
        destruct B as (R2 & I2).
        exists r3. repeat split; eauto.
        econstructor; eauto.
      + intros (wb1' & wb2') (i2, i1) s1 s3 q1 Hs H.
        inv Hs.
        edestruct (@fsim_match_external lis)
          as (wa2 & q2 & Hq2 & ACC2 & Hq12 & HSE12 & Hk12); eauto.
        edestruct (@fsim_match_external lin)
          as (wa3 & q3 & Hq3 & ACC3 & Hq23 & HSE23 & Hk23); eauto.
        exists (se2, (wa2,wa3)), q3. repeat split; eauto. 
        * econstructor; eauto.
        * intros r1 r3 s1' (wpi & wpj) Hw (r2 & Hr12 & Hr23) HH. inv Hw. cbn in *.
          edestruct Hk12 as (i2' & s2' & Hs2' & wpi' & Hpiw & Hm); eauto.
          edestruct Hk23 as (i1' & s3' & Hs3' & wpk' & Hpjw & Hn); eauto.
          eexists (_, _), _. repeat split; eauto.
          eexists (_, _).
          repeat split; eauto.
          econstructor; eauto.
      + intros s1 t s1' Hstep (wpi & wpj) (i2, i1) s3 Hs.
        inv Hs.
        edestruct (@fsim_simulation' lis) as (i1' & wpi' & Hpi & Hx); eauto.
        destruct Hx as [[s2' [A B]] | [A [B C]]].
        * (* L2 makes one or several steps. *)
          edestruct (@simulation_plus lin) as (wpj' & i2' & Hw & Hx); eauto.
          destruct Hx as [[s3' [P Q]] | [P [Q R]]].
          -- (* L3 makes one or several steps *)
            exists (i2', i1'); exists s3'; split.
            left; eauto.
            eexists (_, _). repeat split; eauto.
            econstructor; eauto.
          -- (* L3 makes no step *)
            exists (i2', i1'); exists s3; split.
            right; split. subst t; apply star_refl. red. left. auto.
            eexists (_, _). repeat split; eauto.
            econstructor; eauto.
        * (* L2 makes no step *)
          exists (i2, i1'); exists s3; split.
          right; split. subst t; apply star_refl. red. right. auto.
          eexists (_, _). repeat split; eauto.
          cbn; reflexivity.
          econstructor; eauto.
    - unfold ff_order.
      apply wf_lex_ord. apply Transitive_Closure.wf_clos_trans.
      eapply (fsim_order_wf H2). eapply (fsim_order_wf H1).
  Qed.

End COMP_FSIM.

Lemma st_fsim_vcomp
  `(cc1: callconv lis lin) `(cc2: callconv lin lif)
  (Ls: semantics lis lis) (Ln: semantics lin lin) (Lf: semantics lif lif):
  forward_simulation cc1 Ls Ln ->
  forward_simulation cc2 Ln Lf ->
  forward_simulation (cc_compose cc1 cc2) Ls Lf.
Proof.
  intros [X] [Y]. constructor. eapply st_fsim_vcomp'; eauto.
Qed.


(** ** Identity *)
Program Instance world_unit : World unit :=
  {|
    w_state := unit;
    w_lens := lens_id;
    w_acci := fun _ _ => True;
    w_acce := fun _ _ => True;
  |}.

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.

Solve All Obligations with
  cbn; intros; subst; auto.

Notation "1" := cc_id : gs_cc_scope.


(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

(*Section CCTRANS.

  Context {li1 li2} (cc1 cc2: callconv li1 li2)
    Context (se1)
*)

Definition ccref_outgoing {li1 li2} (cc cc': callconv li1 li2)
  (trans1 : gworld cc -> gworld cc')
  (trans2 : gworld cc -> gworld cc' -> gworld cc' -> gworld cc):=
  forall w se1 se2 q1 q2,
    match_senv cc w se1 se2 ->
    match_query cc w q1 q2 ->
    exists w',
      match_senv cc' w' se1 se2 /\
      match_query cc' w' q1 q2 /\
      get w' = trans1 (get w) /\
      forall r1 r2 (wp': gworld cc'),
        get w' o-> wp' ->
        match_reply cc' (set w' wp') r1 r2 ->
        let wp := trans2 (get w) (get w') wp' in
        get w o-> wp /\
        match_reply cc (set w wp) r1 r2.

Definition ccref_incoming {li1 li2} (cc cc': callconv li1 li2)
  (trans1 : gworld cc -> gworld cc')
  (trans2 : gworld cc' -> gworld cc):=
  forall w se1 se2 q1 q2,
    match_senv cc w se1 se2 ->
    match_query cc w q1 q2 ->
    exists w',
      match_senv cc' w' se1 se2 /\
      match_query cc' w' q1 q2 /\
      get w' = trans1 (get w) /\
      forall r1 r2 (wp': gworld cc'),
        get w' o-> wp' ->
        match_reply cc' (set w' wp') r1 r2 ->
        let wp := trans2 wp' in
        get w o-> wp /\
        match_reply cc (set w wp) r1 r2.

  Record cctrans {li1 li2} (cc1 cc2: callconv li1 li2) :=
    Callconv_Trans{
        trans_12 : gworld cc1 -> gworld cc2; (* compose m1<->m2<->m3 into m1<->m3*)
        trans_21_acc : gworld cc1 -> gworld cc2 -> gworld cc2 -> gworld cc1;
        (*the injp_construction operation which keeps accessibility*)
        trans_21 : gworld cc2 -> gworld cc1; (* split m1<-> m3 into m1<->m1<->m3*)
        trans_initial : forall (gw: gworld cc2), trans_12 (trans_21 gw) = gw;
        (*split the outer-side world and compose it back *)
        trans_acc_eq : forall gw1 gw2 gw2', trans_12 (trans_21_acc gw1 gw2 gw2') = gw2';
        trans_acci : forall (gw1 gw1' : gworld cc1), gw1 *-> gw1' -> (trans_12 gw1) *-> (trans_12 gw1');
        (*the accessibility of internal world (containing mid-level information) can derive
         the accessibility of composed world*)
        bigstep_12 : ccref_outgoing cc1 cc2 trans_12 trans_21_acc; (*the hard part*)
        bigstep_21 : ccref_incoming cc2 cc1 trans_21 trans_12; (*the easy part*)
      }.


  Lemma open_fsim_cctrans {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct X as [trans12 trans21_acc trans21 trans_acc_eq trans_initial trans_acci Big12 Big21].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
  set (ms se1 se2 w' (wp': gworld cc2) idx s1 s2 :=
         exists w wp,
           wp' = trans12 wp /\
           get w = trans21 (get w') /\
           match_states se1 se2 w wp idx s1 s2 /\
             match_senv cc1 w se1 se2 /\
             forall r1 r2 wpf, (get w) o-> wpf -> match_reply cc1 (set w wpf) r1 r2 ->
                          let wpf' := trans12 wpf in
                          (get w') o-> wpf' /\ match_reply cc2 (set w' wpf') r1 r2).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (Big21 wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query; eauto.
  - intros q1 q2 s1 Hq' Hs1 Ho.
    destruct (Big21 wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hr); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. red. exists wB,(get wB). repeat apply conj; eauto.
    rewrite Htrans. eauto.
  - intros gw i s1 s2 r1 (wB & gw' & Htransw & HtranswB & Hs & Hse & Hr') Hr1.
    edestruct @fsim_match_final_states as (r2 & Hr2 & ACC & Hr); eauto.
    exploit Hr'; eauto. intros. exists r2. simpl in H. destruct H.
    split. auto. split. rewrite Htransw. auto. rewrite Htransw. auto.
  - (*the most tricky part*) 
    intros gw2 i s1 s2 qA1 (wB & gw1 & Htransw & HtranswB &  Hs & Hse & Hr') HqA1.
    edestruct @fsim_match_external as (wA & qA2 & Hacc1 & HqA2 & HqA & HseA & ?); eauto.
    edestruct Big12 as (wA' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    rewrite Htransw. setoid_rewrite H0.
    apply trans_acci. auto. exploit H1; eauto.
    intros [A B].
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. destruct Hs' as [gw1'' [C D]].
    rename gw'' into gw2'.
    exists (trans12 gw1''). split.
    assert (trans12 ( trans21_acc (get wA) (get wA') gw2') = gw2'). eauto.
    rewrite <- H5. eauto.
    exists wB, gw1''. intuition auto.
  - intros s1 t s1' Hs1' gw2 i s2 (wB & gw1 & Htransw & HtranswB & Hs & Hse & Hr').
    edestruct @fsim_simulation as (i' & s2' & Hs2' & gw1' & Hac1 & Hs'); eauto.
    exists i', s2'. split; auto.
    exists (trans12 gw1'). (*here what we do is just [ignore] the middle part in gw1'*)
    split. rewrite Htransw. eauto.
    econstructor; eauto. exists gw1'. repeat apply conj; eauto.
Qed.

Inductive
(** TODOs*)
(** 1.Definition of c_injp as a callconv *)
(** 2.Achieve [cctrans (injp@injp) (injp)] *)
(** 3.Introduce callconv with empty world (ext, inj, CLLMMA) *)
(** 4.Try the composition of these trivial callconv using cctrans *)
(** 4.1 The self-simulation mechniasm? *)  
(** 4.Modify the proofs of each pass *)
(** 5.Compose the compiler *)



