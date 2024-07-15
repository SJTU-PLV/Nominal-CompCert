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

Require Import CallconvBig.

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
        edestruct (@fsim_match_final_states lis) as (r2 & wb1'' & Hr2 & ACCO1 & ACCI1 & A); eauto.
        edestruct (@fsim_match_final_states lin) as (r3 & wb2'' & Hr3 & ACCO2 & ACCI2 & B); eauto.
        exists r3. exists (wb1'', wb2''). repeat split; eauto.
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
          edestruct Hk12 as (i2' & s2' & Hs2' & Hm); eauto.
          edestruct Hk23 as (i1' & s3' & Hs3' & Hn); eauto.
          eexists (_, _), _. repeat split; eauto.
          econstructor; eauto.
      + intros s1 t s1' Hstep (wpi & wpj) (i2, i1) s3 Hs.
        inv Hs.
        edestruct (@fsim_simulation' lis) as (i1' & Hx); eauto.
        destruct Hx as [[s2' [A B]] | [A [B C]]].
        * (* L2 makes one or several steps. *)
          edestruct (@simulation_plus lin) as (i2'& Hx); eauto.
          destruct Hx as [[s3' [P Q]] | [P [Q R]]].
          -- (* L3 makes one or several steps *)
            exists (i2', i1'); exists s3'; split.
            left; eauto.
            econstructor; eauto.
          -- (* L3 makes no step *)
            exists (i2', i1'); exists s3; split.
            right; split. subst t; apply star_refl. red. left. auto.
            econstructor; eauto.
        * (* L2 makes no step *)
          exists (i2, i1'); exists s3; split.
          right; split. subst t; apply star_refl. red. right. auto.
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
(** cc1: internal, i.e. injp ⋅ injp
    cc2: external, i.e. injp  *)

(*
Definition acci_future_query {li1 li2} {cc1 cc2: callconv li li2}
  (wp1 : gworld cc1) (wp2 : gworld cc2) :=
  forall wp1' w1 q1 q2, wp1 *-> wp1' /\ match_query cc1 w1 q1 q2 /\
 *)


Inductive same_mem {li1 li2: language_interface} {cc1 cc2: callconv li1 li2} : gworld cc1 -> gworld cc2 -> Prop :=
|match_query_mem : forall w1 w2 q1 q2 wp1 wp2,
    match_query cc1 w1 q1 q2 -> match_query cc2 w2 q1 q2 ->
    get w1 = wp1 -> get w2 = wp2 ->
    same_mem wp1 wp2
|match_reply_mem : forall w1 w2 r1 r2 wp1 wp2,
    match_reply cc1 w1 r1 r2 -> match_reply cc2 w2 r1 r2 ->
    get w1 = wp1 -> get w2 = wp2 ->
    same_mem wp1 wp2.

Definition ACCI_12 {li1 li2} {cc1 cc2: callconv li1 li2} (wp1 : gworld cc1) (wp2 : gworld cc2) :=
  forall wp1' wp2', wp1 *-> wp1' -> same_mem wp1' wp2' -> wp2 *-> wp2'.

Definition ccref_outgoing {li1 li2} (cc1 cc2: callconv li1 li2) :=
  forall w1 se1 se2 q1 q2,
    match_senv cc1 w1 se1 se2 ->
    match_query cc1 w1 q1 q2 ->
    exists w2,
      match_senv cc2 w2 se1 se2 /\
      match_query cc2 w2 q1 q2 /\  
      forall r1 r2 (wp2: gworld cc2),
        get w2 o-> wp2 ->
        match_reply cc2 (set w2 wp2) r1 r2 ->
        exists (wp1 : gworld cc1),
        get w1 o-> wp1 /\
         match_reply cc1 (set w1 wp1) r1 r2 /\
        ACCI_12 wp1 wp2 .

(** I -> F *)
Definition ccref_incoming {li1 li2} (cc1 cc2: callconv li1 li2) :=
  forall w2 se1 se2 q1 q2,
    match_senv cc2 w2 se1 se2 ->
    match_query cc2 w2 q1 q2 ->
    exists w1,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      ACCI_12 (get w1) (get w2) /\
      (forall r1 r2 (wp1: gworld cc1),
        get w1 o-> wp1 -> (get w1 *-> wp1) ->
        match_reply cc1 (set w1 wp1) r1 r2 ->
        exists (wp2 : gworld cc2),
        get w2 o-> wp2 /\ (get w2 *-> wp2) /\
        match_reply cc2 (set w2 wp2) r1 r2).

(*The case I -> X *)
(* 
Definition ccref_incoming_acci1 {li1 li2} (cc1 cc2: callconv li1 li2) :=
  forall w2 se1 se2 q1 q2,
    match_senv cc2 w2 se1 se2 ->
    match_query cc2 w2 q1 q2 ->
    exists w1,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      (* get w' = trans1 (get w) /\ *)
      forall q1' q2' (wp1: gworld cc1),
        get w1 *-> wp1 ->
        match_query cc1 (set w1 wp1) q1' q2' ->
        exists wp2,
        get w2 *-> wp2 /\
          match_query cc2 (set w2 wp2) q1' q2'.
*)
(*The case Y -> X *)
(* 
Definition ccref_incoming_acci1 {li1 li2} (cc1 cc2: callconv li1 li2) :=
  forall w2 se1 se2 r1 r2,
    match_senv cc2 w2 se1 se2 ->
    match_reply cc2 w2 r1 r2 ->
    exists w1,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      (* get w' = trans1 (get w) /\ *)
      forall q1' q2' (wp1: gworld cc1),
        get w1 *-> wp1 ->
        match_query cc1 (set w1 wp1) q1' q2' ->
        exists wp2,
        get w2 *-> wp2 /\
          match_query cc2 (set w2 wp2) q1' q2'.
*)
  Record cctrans {li1 li2} (cc1 cc2: callconv li1 li2) :=
    Callconv_Trans{
        big_step_incoming : ccref_incoming cc1 cc2;
        big_step_outgoing : ccref_outgoing cc1 cc2;
      }.

  
  Lemma open_fsim_cctrans {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct H0 as [INCOM OUTGO].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
  
  set (ms se1 se2 (w2 : ccworld cc2) (wp2: gworld cc2) idx s1 s2 :=
         exists w1 wp1,
           match_states se1 se2 w1 wp1 idx s1 s2 /\
             match_senv cc1 w1 se1 se2 /\
             ACCI_12 wp1 wp2 /\
             (forall r1 r2 wp1', (get w1) o-> wp1' -> wp1 *-> wp1' -> match_reply cc1 (set w1 wp1') r1 r2 ->
                            exists wp2', (get w2) o-> wp2' /\ wp2 *-> wp2' /\ match_reply cc2 (set w2 wp2') r1 r2)).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query; eauto.
  - intros q1 q2 s1 Hq' Hs1 Ho.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & HACCI & Hr); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. red. exists wB,(get wB). repeat apply conj; eauto.
    (** INCOM is not strong enough *)
  - intros gw i s1 s2 r1 (wB & gw' & Hs & Hse & HACCI & Hr') Hr1.
    edestruct @fsim_match_final_states as (r2 & gw1 & Hr2 & ACCO1 & ACCI1 & Hr); eauto.
    exploit Hr'; eauto. intros (gw2 &  ACCO2 & ACCI2 & Hr2'). exists r2.
    exists gw2. intuition auto.
  (** The match_state is strong enough for [final_state]*)
    (** Can this be weaken? *)
  - (*the most tricky part*)
    intros gw2 i s1 s2 qA1 (wB & gw1 & Hs & Hse & HACCI& Hr') HqA1.
    edestruct @fsim_match_external as (wA & qA2 & Hacc1 & HqA2 & HqA & HseA & ?); eauto.
    edestruct OUTGO as (wA' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    eapply HACCI. eauto.  econstructor; eauto. 
    (** from gw1 *-> get wA to gw2 *-> get wA'*)
    (** This should be provided by match_states or INCOM? and OUTGOING(AFTER) *)
    exploit Hr; eauto. intros (wp1 & ACCO1 & MR1 & HACCI').
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto.
    exists wB, wp1. intuition auto.
    (** This part of match_states need to be provided by after_external or OUTGO*)
    admit.
  - intros s1 t s1' Hs1' gw2 i s2 (wB & gw1 & Hs & Hse & Hr').
   edestruct @fsim_simulation as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto.
    econstructor; eauto.
Qed.


(** TODOs*)
(** 1.Definition of c_injp as a callconv *)
(** 2.Achieve [cctrans (injp@injp) (injp)] *)
(** 3.Introduce callconv with empty world (ext, inj, CLLMMA) *)
(** 4.Try the composition of these trivial callconv using cctrans *)
(** 4.1 The self-simulation mechniasm? *)  
(** 4.Modify the proofs of each pass *)
(** 5.Compose the compiler *)

  
Require Import InjectFootprint.

Program Instance injp_world_id : World injp_world :=
    {
      w_state := injp_world;
      w_lens := lens_id;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.

Program Definition c_injp : callconv li_c li_c :=
  {|
    ccworld := injp_world;
    ccworld_world := injp_world_id;
    match_senv w := CKLR.match_stbls injp w;
    match_query := cc_c_query injp;
    match_reply := cc_c_reply injp;    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Compute (gworld (cc_compose c_injp c_injp)).
Program Definition trans12 : injp_world * injp_world -> injp_world.
Proof.
  intros. inv X. destruct X0,X1.
  econstructor.
  eapply Mem.inject_compose.
Abort. (** SOOOO BAD: It can not be defined.. I Need match_query to get m1<->m2<->m3*)

Lemma cctrans_injp_comp : cctrans (cc_compose c_injp c_injp) (c_injp).
Proof.
  econstructor.
Admitted.

Theorem injp_pass_compose: forall (L1 L2 L3: semantics li_c li_c),
    forward_simulation c_injp L1 L2 ->
    forward_simulation c_injp L2 L3 ->
    forward_simulation c_injp L1 L3.
Proof.
  intros.
  assert (forward_simulation (cc_compose c_injp c_injp) L1 L3).
  eapply st_fsim_vcomp; eauto.
  eapply open_fsim_cctrans; eauto.
  apply cctrans_injp_comp.
Qed.



