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

Require Import CallconvBig InjpAccoComp.

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
(*
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
*)

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

(** cc1: internal, i.e. injp ⋅ injp
    cc2: external, i.e. injp  *)

(*
Inductive wf_mem {li1 li2 : language_interface} {cc : callconv li1 li2} : gworld cc -> Prop :=
|wf_q : forall w wp q1 q2, match_query cc w q1 q2 -> get w = wp -> wf_mem wp
|wf_r : forall w wp r1 r2, match_reply cc w r1 r2 -> get w = wp -> wf_mem wp.
                                                                   
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
 *)

(** We are trying to define the ccref_outgoing with respect to the "living wp1, however,
    to show from [wp1 *-> (get w1)] we can construct w2 and show [wp2 *-> (get w2)], we still
    have to show that wp1 and wp2 are recording the same injected memories. Such relation has to be **defined**
    in some way "*)


Definition ccref_outgoing {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop) :=
  forall wp1 wp2 w1 se1 se2 q1 q2,
    match_senv cc1 w1 se1 se2 ->
    match_query cc1 w1 q1 q2 ->
    wp1 *-> (get w1) ->
    match12 wp1 wp2 ->
    exists w2,
      wp2 *-> (get w2) /\
      match_senv cc2 w2 se1 se2 /\
      match_query cc2 w2 q1 q2 /\
      forall r1 r2 (wp2': gworld cc2),
        get w2 o-> wp2' ->
        match_reply cc2 (set w2 wp2') r1 r2 ->
        exists (wp1' : gworld cc1),
        get w1 o-> wp1' /\
        match_reply cc1 (set w1 wp1') r1 r2 /\
        match12 wp1' wp2'.            

Definition ccref_incoming {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop):=
  forall w2 se1 se2 q1 q2,
    match_senv cc2 w2 se1 se2 ->
    match_query cc2 w2 q1 q2 ->
    exists (w1: ccworld cc1) ,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      match12 (get w1) (get w2) /\
        (forall r1 r2 wp1 wp2 wp1',
        match12 wp1 wp2 ->    
        get w1 o-> wp1' -> wp1 *-> wp1' ->
        match_reply cc1 (set w1 wp1') r1 r2 ->
        exists (wp2' : gworld cc2),
        (* match12 wp1' wp2' ->*)
        get w2 o-> wp2' /\ wp2 *-> wp2' /\
        match_reply cc2 (set w2 wp2') r1 r2).

(* Lemma same_mem_trans_OK {li1 li2} (cc1 cc2: callconv li1 li2) :=
  forall wp1 wp2,
    wf_mem wp1 -> trans12 wp1 = wp2 ->
 *)

Record cctrans {li1 li2} (cc1 cc2: callconv li1 li2) :=
  Callconv_Trans{
        match12 : gworld cc1 -> gworld cc2 -> Prop;
        big_step_incoming : ccref_incoming cc1 cc2 match12;
        big_step_outgoing : ccref_outgoing cc1 cc2 match12;
      }.

  
  Lemma open_fsim_cctrans {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct X as [match12 INCOM OUTGO].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
    set (ms se1 se2 (w2 : ccworld cc2) (wp2: gworld cc2) idx s1 s2 :=
         exists w1 (wp1 : gworld cc1),
           match_states se1 se2 w1 wp1 idx s1 s2 /\
             match_senv cc1 w1 se1 se2 /\
             match12 (get w1) (get w2) /\
             match12 wp1 wp2 /\
             (forall r1 r2 wp1 wp2 wp1', match12 wp1 wp2 -> (get w1) o-> wp1' -> wp1 *-> wp1' -> match_reply cc1 (set w1 wp1') r1 r2 ->
            exists (wp2' : gworld cc2), (get w2) o-> wp2' /\ wp2 *-> wp2' /\ match_reply cc2 (set w2 wp2') r1 r2)).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query; eauto.
  - intros q1 q2 s1 Hq' Hs1 Ho.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hf); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. red. exists wB,(get wB). repeat apply conj; eauto.
  - intros gw i s1 s2 r1 (wB & gw' & Hs & Hse & HmB & Hm & Hf) Hr1.
    edestruct @fsim_match_final_states as (r2 & gw1 & Hr2 & ACCO1 & ACCI1 & Hr); eauto.
    exploit Hf; eauto. intros (gw2 &  ACCO2 & Hr2'). exists r2.
    exists gw2. intuition auto.
  - (*the most tricky part*)
    intros gw2 i s1 s2 qA1 (wB & gw1 & Hs & Hse & HmB & Hm & Hf) HqA1.
    edestruct @fsim_match_external as (wA & qA2 & Hacc1 & HqA2 & HqA & HseA & ?); eauto.
    edestruct OUTGO as (wA' & Hm' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    exploit Hr; eauto. intros (wp1' & ACCO1 & MR1 & Hm'').
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB. exists wp1'.
    intuition auto.
  - intros s1 t s1' Hs1' gw2 i s2 (wB & gw1 & Hs & Hse & Hr').
   edestruct @fsim_simulation as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto.
    econstructor; eauto.
Qed.


Require Import Inject InjectFootprint.

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

Inductive match_injp_comp_world : (injp_world * injp_world) -> injp_world -> Prop :=
|world_comp_intro:
  forall m1 m2 m3 j12 j23 j13 Hm12 Hm23 Hm13,
    j13 = compose_meminj j12 j23 ->
    match_injp_comp_world (injpw j12 m1 m2 Hm12, injpw j23 m2 m3 Hm23) (injpw j13 m1 m3 Hm13).

Inductive injp_trivial_comp_world : (injp_world * injp_world) -> injp_world -> Prop :=
|trivial_comp_intro : forall j m1 m3 Hm12 Hm23 Hm13,
    injp_trivial_comp_world (injpw (meminj_dom j) m1 m1 Hm12, injpw j m1 m3 Hm23)
      (injpw j m1 m3 Hm13).


          
Lemma injp_comp_acce : forall w11 w12 w11' w12' w1 w2,
    injp_trivial_comp_world (w11, w12)  w1 ->
    match_injp_comp_world (w11', w12')  w2 ->
    injp_acce w11 w11' -> injp_acce w12 w12' ->
    injp_acce w1 w2.
Proof.
  intros. inv H. inv H0.
  inv H1. inv H2. rename m0 into m1'. rename m2 into m2'. rename m4 into m3'.
  econstructor; eauto.
  - destruct H11. split. auto. eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split; auto. red. unfold meminj_dom.
    rewrite H. reflexivity.
  - assert (j = compose_meminj (meminj_dom j) j).
    rewrite meminj_dom_compose. reflexivity.
    rewrite H. rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
    destruct (j12 b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j23 bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    exploit H14; eauto. unfold meminj_dom. rewrite Hb. reflexivity.
    intros [X Y].
    destruct (j bi) as [[? ?] | ] eqn:Hfbi.
    {
      eapply Mem.valid_block_inject_1 in Hfbi; eauto.
    }
    edestruct H22; eauto. erewrite <- inject_tid; eauto.
    inv Hm0. inv mi_thread. erewrite <- Hjs; eauto.
  - red. intros. unfold compose_meminj in H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H0.
    destruct (j23 bi) as [[b2' d']|] eqn: Hj2; inv H2.
    exploit H15; eauto. unfold meminj_dom. rewrite H. reflexivity.
    intros [A B]. split; auto.
    intro. apply B. red. erewrite inject_block_tid; eauto.
Qed.


Lemma inject_preserve_tid : forall j m1 m2 b1 b2 d,
    j b1 = Some (b2, d) ->
    Mem.inject j m1 m2 ->
    fst b1 = fst b2 /\ Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2).
Proof.
  intros. inv H0. inv mi_thread. inv Hms. split; eauto.
Qed.

Lemma inject_other_thread : forall j m1 m2 b1 b2 d,
    j b1 = Some (b2, d) ->
    Mem.inject j m1 m2 ->
    fst b1 <> Mem.tid (Mem.support m1) <->
    fst b2 <> Mem.tid (Mem.support m2).
Proof.
  intros. edestruct inject_preserve_tid; eauto.
  split;
  congruence.
Qed.
(*
Inductive external_mid_hidden: injp_world -> injp_world -> Prop :=
|external_mid_hidden_intro :
  forall j12 j23 m1 m2 m3 Hm12 Hm23
    (** This case says that for any related external blocks [j13 b1 = Some b3],
        we have constructed b2 in m2 s.t. j12 b1 = Some b2.*)
    (Hconstr1: forall b1 b2 d, fst b2 <> Mem.tid (Mem.support m2) ->
                 j12 b1 = Some (b2, d) -> j23 b2 <> None)
    (** This cases says that for any external stack block [with permission] in m2
        and *mapped to m3* in m2, it comes from a corresponding position im m1*)
    (Hconstr2: forall b2 ofs2 b3 d2, fst b2 <> Mem.tid (Mem.support m2) ->
                Mem.perm m2 b2 ofs2 Max Nonempty -> j23 b2 = Some (b3, d2) ->
                exists b1 ofs1, Mem.perm m1 b1 ofs1 Max Nonempty /\ j12 b1 = Some (b2, ofs2 - ofs1)),
    external_mid_hidden (injpw j12 m1 m2 Hm12) (injpw j23 m2 m3 Hm23).
 *)

(** From the incoming world [w1], where the internal memory is hidden, we will construct a 
    mid-level memory [m2] to get [w11] and [w12]. This construction is either [I: Initial state]
    or [Y: After external].   

    For I, [m2] is exactlt [m1]. For Y, [m2] is constructed by the "injp construction" algorithm.
    These constructions are defined by us, therefore we can ensure that for any "thread-external block"
    (i.e. allocated by other threads) [b2] in [m2], it must be *public* in both [w11] and [w12].
    Otherwise it should not be created. 
    
    Therefore, we can prove the following lemma, which states that the internal accessbility of
    [w11, w12] to [w11',w12'] can indicate the same accessbility of [w2] which hides the mid-level
    memory
 *)

Lemma inject_val_tid : forall j m1 m2 b1 b2 d,
    Mem.inject j m1 m2 ->
    j b1 = Some (b2, d) ->
    fst b1 = fst b2.
Proof.
  intros. inv H. inv mi_thread. erewrite Hjs; eauto.
Qed.

Lemma injp_comp_acci : forall w11 w12 w11' w12' w1 w2,
    match_injp_comp_world (w11, w12)  w1 ->
    external_mid_hidden w11 w12 ->
    match_injp_comp_world (w11', w12')  w2 ->
    injp_acci w11 w11' -> injp_acci w12 w12' ->
    injp_acci w1 w2.
Proof.
  intros. inv H. inv H1. inv H0.
  rename j0 into j12'. rename j1 into j23'. rename m0 into m1'. rename m4 into m2'.
  rename m5 into m3'.
  inv H2. inv H3.
  constructor; eauto.
  - destruct H11 as [S11 H11]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. red in X. unfold compose_meminj in X.
    destruct (j12 b) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j23 b2) as [[b3 d2]|] eqn:Hj23; try congruence.
    eapply Hconstr1 in Hj12; eauto. congruence.
    erewrite <- inject_other_thread; eauto.
  - destruct H21 as [S21 H21]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. intros. red in X. intro.
    exploit Hconstr2; eauto. erewrite inject_other_thread; eauto.
    intros (b1 & ofs1 & Hp1 & Hj12).
    exploit X. unfold compose_meminj. rewrite Hj12, H. reflexivity.
    replace (ofs - (ofs - delta - ofs1 + delta)) with ofs1 by lia. auto.
    auto.
  - rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
        destruct (j12' b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
        destruct (j23' bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
        inv Hb'.
        destruct (j12 b1) as [[? ?] | ] eqn:Hb1.
        + apply H13 in Hb1 as Heq. rewrite Hb1' in Heq. inv Heq.
          destruct (j23 b) as [[? ?] |] eqn: Hb2.
          unfold compose_meminj in Hb. rewrite Hb1, Hb2 in Hb. congruence.
          exfalso. exploit H23; eauto.
          erewrite <- inject_tid; eauto.
          erewrite <- inject_val_tid. 3: eauto. auto. eauto.
          intros [X Y].
          eapply Mem.valid_block_inject_2 in Hb1; eauto.
        + exploit H14; eauto. intros [X Y].
          destruct (j23 bi) as [[? ?] |] eqn: Hb2.
          exfalso. eapply Mem.valid_block_inject_1 in Hb2; eauto.
          exploit H23; eauto. erewrite <- inject_tid; eauto.
          erewrite <- inject_val_tid. 3: eauto. auto. eauto.
          intros [X1 Y1]. intuition auto.
  - red. intros. unfold compose_meminj in H, H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H.
    + 
      destruct (j23 bi) as [[b2' d']|] eqn: Hj2; inv H2.
      apply H13 in Hj1 as Hj1'. rewrite Hj1' in H0.
      destruct (j23' bi) as [[b2'' d'']|] eqn: Hj2'; inv H0.
      exploit H24; eauto. intros [A B]. split; auto.
      intro. apply A. red. erewrite <- inject_block_tid. 3: eauto. eauto. eauto.
    + destruct (j12' b1) as [[bi d]|] eqn: Hj1'; inv H0.
      destruct (j23' bi) as [[b2' d'']|] eqn: Hj2'; inv H1.
      exploit H15; eauto. intros [A B]. split; auto.
      intro. apply B. red. erewrite inject_block_tid; eauto.
  - red. intros. unfold compose_meminj in H. rename b2 into b3.
    destruct (j12 b1) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j23 b2) as [[b3' d2]|] eqn:Hj23; try congruence. inv H.
    red in H16. specialize (H16 _ _ _ _ Hj12 H0 H1 H2) as Hp2'.
    eapply Mem.perm_inject in H1 as Hp2. 3: eauto. 2: eauto.
    red in H25. inv Hm12. inv mi_thread. inv Hms. rewrite H3 in H0.
    red in Hjs. erewrite Hjs in H0; eauto.
    specialize (H25 _ _ _ _ Hj23 H0 Hp2 Hp2') as Hp3.
    rewrite Z.add_assoc. auto.
Qed.

Definition match_12_cctrans : injp_world * injp_world -> injp_world -> Prop :=
  fun w2 w =>
    match_injp_comp_world w2 w /\ external_mid_hidden (fst w2) (snd w2).

(** Problem : Although the "thread-external" blocks in [m2] is perfectly public from construction.
    It may be changed during the internal execution.

    [b1]                                         [xx] <- freed
     w1                                           w1'
    [b2] -----------------ACCI--------------->   [b2]
     w2                                           w2'
    [b3]                                         [b3]
   
    After internal execution, the [Hconstr2] may be destoryed. Why?
    
    When the block [b] is deliverd to external, and back to internal again.
    It is possible for the internal executions to change the values of [b3] because 
    it is now public in second [w2'] but private in the composed world. 

    Which breaks the ACCI: 
    For values, there is a case such that the value in [b2] is Vundef but [b3] = Vint 1.
    Then L2 does sth like [b++;], therefore Vundef -> Vundef. Vint 1 -> Vint 2. 
    It is possbie according to the definition of ACCI.
    
    But the point here is: "How can L2 opearates on [b2]?" It is a private external block.
    Since L2 cannot even see [b2], the values of its corresponding block in [b3] should
    not change either. 
    In other words, The simulation L1 <= L2 indicates that [b2] is not changed via ACCI.
    But such unchanged property cannot be transfer to [b3] vid L2 <= L3.

    Now the solution is we add [free_preserved] in ACCI, which requires that [b2] is freed
    if its inverse image [b1] is freed. 
    Therefore we can ensure that an [out_of_reach] position in m2 is not only "unchanged",
    but also *inaccessible*. 
    Therefore we do not have to worry the change of values in [b3] because it is also 
    [out_of_reach] now in [w2'].

    *)
Lemma external_mid_hidden_acci: forall j12 j23 m1 m2 m3 Hm12 Hm23 j12' j23' m1' m2' m3' Hm12' Hm23',
    let w1 := injpw j12 m1 m2 Hm12 in
    let w2 := injpw j23 m2 m3 Hm23 in
    let w1' := injpw j12' m1' m2' Hm12' in
    let w2' := injpw j23' m2' m3' Hm23' in
    external_mid_hidden w1 w2 ->
    injp_acci w1 w1' -> injp_acci w2 w2' ->
    external_mid_hidden w1' w2'.
Proof.
  intros. inv H. inv H0. inv H1.
  econstructor; eauto.
  - intros. red in Hnb0. destruct (j12 b1) as [[b2' d']|] eqn:Hj12.
    + apply H13 in Hj12 as Heq. rewrite H0 in Heq. inv Heq.
      destruct (j23 b2') as [[b3 d'']|] eqn:Hj23.
      * apply H22 in Hj23. congruence.
      * exploit Hconstr1; eauto. inv H12. destruct unchanged_on_thread_i. congruence.
    + exploit H14; eauto. erewrite inject_val_tid. 3: eauto. 2: eauto.
      erewrite inject_tid. 2: eauto. inversion H12. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb0; eauto. eapply Mem.valid_block_inject_2; eauto.
      intro. apply H. destruct H20 as [[_ Z] _]. congruence.
  - intros. red in Hnb3. destruct (j23 b2) as [[b3' d']|] eqn:Hj23.
    + apply H22 in Hj23 as Heq. rewrite H1 in Heq. inv Heq.
      destruct (Mem.loc_in_reach_find m1 j12 b2 ofs2) as [[b1 ofs1]|] eqn:FIND12.
      * eapply Mem.loc_in_reach_find_valid in FIND12; eauto. destruct FIND12 as [Hj12 Hpm1].
        exists b1, ofs1. split. edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_]. congruence.
        replace (ofs1 + (ofs2 - ofs1)) with ofs2 by lia.
        auto. auto.
      * eapply Mem.loc_in_reach_find_none in FIND12; eauto. destruct H12 as [[X Y]Z].
        exploit Hconstr2; eauto. congruence. inv Z.
        eapply unchanged_on_perm; eauto. red. split; auto. congruence. eapply Mem.valid_block_inject_1; eauto.
        intros (b1 & ofs1 & Hpm1 & Hj12). exists b1, ofs1. split.
        edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_]. congruence.
        replace (ofs1 + (ofs2 - ofs1)) with ofs2 by lia. auto. auto.
    + exploit H23; eauto. inversion H12. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb3; eauto. eapply Mem.valid_block_inject_2; eauto.
      erewrite inject_other_thread in H. 3: eauto. 2: eauto. intro.
      apply H.
      destruct H21 as [[_ Z]_]. congruence.
Qed.

(*
(** But the introduce of [mid_hidden] is to show the absence of such *weird* injection of positions, why it cannot work? *)
Lemma injp_acce_outgoing_constr: forall j12 j23 m1 m2 m3 Hm13 j13' m1' m3' (Hm12: Mem.inject j12 m1 m2) (Hm23 :Mem.inject j23 m2 m3) Hm13',
    let w1 := injpw j12 m1 m2 Hm12 in
    let w2 := injpw j23 m2 m3 Hm23 in
    injp_acce  (injpw (compose_meminj j12 j23) m1 m3 Hm13) (injpw j13' m1' m3' Hm13') -> external_mid_hidden w1 w2 ->
    exists j12' j23' m2' Hm12' Hm23',
      let w1' := injpw j12' m1' m2' Hm12' in
      let w2' := injpw j23' m2' m3' Hm23' in
      j13' = compose_meminj j12' j23' /\
      injp_acce w1 w1' /\ injp_acce w2 w2' /\ external_mid_hidden w1' w2'.
Proof.
  (*need to be proved in another file*)
Admitted.
*)
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
  econstructor; eauto. rewrite Valuesrel.add_repr.
  rewrite Ptrofs.add_assoc. auto.
  exists Vundef. split; constructor.
Qed.

Lemma cctrans_injp_comp : cctrans (cc_compose c_injp c_injp) (c_injp).
Proof.
  econstructor. instantiate (1:= match_12_cctrans).
  - (*incoming construction*)
    red. intros. inv H0. inv H3. simpl in H2, H1.
    inv H.
    exists (se1, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm),
              injpw f m1 m2 Hm)).
    repeat apply conj; eauto.
    + simpl. split. constructor; eauto. eapply match_stbls_dom; eauto. constructor; simpl; eauto.
    + exists (cq vf1 sg vargs1 m1). split.
      econstructor; simpl; eauto. eapply val_inject_dom; eauto.
      eapply val_inject_list_dom; eauto.
      econstructor; eauto. simpl. econstructor; eauto.
    + econstructor. rewrite meminj_dom_compose. reflexivity.
    + econstructor; eauto. intros. unfold meminj_dom in H0.
      destruct (f b1) as [[? ?]|] eqn: Hf; inv H0. congruence.
      intros. exists b2, ofs2. split. auto. unfold meminj_dom. rewrite H3.
      replace (ofs2 - ofs2) with 0 by lia. reflexivity.
    + intros r1 r3 wp1 wp2 wp1' Hmatch [Hae1 Hae2] HACCI Hr. simpl in Hae1, Hae2.
      destruct wp1' as [wp11' wp12']. simpl. simpl in *.
      destruct wp1 as [wp11 wp12]. simpl in *. destruct HACCI as [HAci1 HAci2].
      simpl in *. destruct wp11' as [j12 m1' m2' Hm1']. destruct wp12' as [j23 m2'_ m3' Hm2'].
      destruct Hr as [r2 [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in *. inv H0. inv H11. rename m1'0 into m1'.
      rename m2'0 into m2'. rename m2'1 into m3'.
      exists (injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm1' Hm2')).
      repeat apply conj; eauto.
      -- eapply injp_comp_acce. 3: apply Hae1. 3:apply Hae2.
         econstructor; eauto.
         econstructor; eauto.
      -- inv Hmatch. eapply injp_comp_acci; eauto. econstructor; eauto.
      -- econstructor; simpl; eauto. eapply val_inject_compose; eauto.
  - (* outgoing construction *)
    red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [x [w11 w12]].
    inv HACI. simpl in H1,H2. 
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    assert (m2'_ = m2').
    { destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2. simpl in *. inv H5. inv H14.
      reflexivity. }
    subst m2'_.
    exists (injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23') ).
    repeat apply conj; eauto.
    + simpl. inv H; simpl in *.
      eapply injp_comp_acci; eauto.
      econstructor; eauto.
      econstructor; eauto.
    + inv Hs. inv H3. inv H4. econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2.
      inv H5. inv H14. simpl in *.
      econstructor; simpl; eauto. eapply val_inject_compose; eauto.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    + (** The accessbility construction : use acco*)
      intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. inv MR. simpl in H3,H4.
      destruct wp2' as [j13'' m1'' m3'' Hm13'].
      simpl in H3, H4.
      assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j23' m2' m3' Hm23')).
      destruct wp1. destruct w, w0.      inv H0.
      exploit external_mid_hidden_acci; eauto. econstructor; eauto.
      exploit injp_acce_outgoing_constr; eauto.
      intros (j12'' & j23'' & m2'' & Hm12'' & Hm23'' & COMPOSE & ACCE1 & ACCE2 & HIDDEN).
      exists ((injpw j12'' m1'' m2'' Hm12''),(injpw j23'' m2'' m3'' Hm23'')).
      repeat apply conj; eauto.
      -- inv H4.
         rename vres2 into vres3. exploit compose_meminj_midvalue; eauto.
         intros [vres2 [RES1 RES2]]. 
         exists (cr vres2 m2''). repeat econstructor; eauto.
      -- econstructor; eauto.
Qed.
                                                                                                               
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

(**  TODOs*)

(** 3.Introduce callconv with empty world (ext, inj, CLLMMA) *)
(** 4.Try the composition of these trivial callconv using cctrans *)

(** Question: Can we compose the simulation of [id] and [ext] passes with new [injp] passes 
    without modifing the proofs?

    Yes for [id]
 *)


Local Instance world_unit {T: Type} : World T :=
  {
    w_state := unit;
    w_lens := lens_unit;
    w_acci := fun _ _ => True;
    w_acce := fun _ _ => True;
  }.

Program Definition cc_id {li : language_interface} : callconv li li :=
  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.

Lemma cctrans_id_1 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc_id cc) cc.
Proof.
  econstructor. instantiate (1:= fun w1 w => eq (snd w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se1,(tt,w2))). econstructor; eauto. reflexivity.
    + econstructor; eauto. split. reflexivity. auto.
    + reflexivity.
    + intros. destruct wp1 as [xx wp2']. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [xy wp2'']. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [tt w2]].
    simpl in H. destruct H as [Heq H]. subst se'.
    simpl in H0. destruct H0 as [q1' [Heq H0]]. subst q1'.
    destruct wp1 as [tt' wp2'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (tt, wp2'). intuition auto.
    split; auto. exists r1. split. econstructor; eauto. auto.
Qed.

Lemma cctrans_id_2 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc cc_id) cc.
Proof.
  econstructor. instantiate (1:= fun w1 w => eq (fst w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se2,(w2,tt))). econstructor; eauto. reflexivity.
    + exists q2. split; auto. econstructor; eauto.
    + reflexivity.
    + intros. destruct wp1 as [wp2' xx]. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [wp2'' xy]. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [w2 tt]].
    simpl in H. destruct H as [H Heq]. subst se'.
    simpl in H0. destruct H0 as [q2' [H0 Heq]]. subst q2'.
    destruct wp1 as [wp2' tt'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (wp2',tt). intuition auto. split; simpl. auto. reflexivity.
    exists r2. split. auto. econstructor; eauto.
Qed.

Lemma oldfsim_newfsim_ccid : forall {li : language_interface} (L1 L2: semantics li li),
    Smallstep.forward_simulation LanguageInterface.cc_id LanguageInterface.cc_id L1 L2 ->
    forward_simulation cc_id L1 L2.
Proof.
  intros. red in H. inv H. constructor.
  inv X. econstructor; eauto.
  intros. exploit fsim_lts0; eauto.
  intros FPros.
  instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  fsim_match_states0 se1 se2 wB idx s1 s2).
  simpl.
  inv FPros. econstructor; eauto.
  - intros. exploit fsim_match_final_states0; eauto.
    intros [r2 [A B]]. exists r2. exists tt. intuition auto. reflexivity. reflexivity.
  - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto.
Qed.


(** Q : Can we (Should we) define the new [injp] as [cklr] instead of several different
        callconvs for different interfaces ?
      
    1. Compare the [c_injp] defined above v.s. [cc_c injp]. 
       Can we define another version of cc_c based on another [cklr] equipped with acci and acce?
    2. Try []

  *)

Lemma compose_id_new_injp_1 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    Smallstep.forward_simulation 1 1 L1 L2 ->
    forward_simulation cc L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros. eapply open_fsim_cctrans.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
  eapply cctrans_id_1.
Qed.

Lemma compose_id_new_injp_2 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    forward_simulation cc L1 L2 ->
    Smallstep.forward_simulation 1 1 L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros. eapply open_fsim_cctrans.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
  eapply cctrans_id_2.
Qed.

(*
c_injp
  cc_c
    Extends.ext
    inj
 *)

Require Import Extends.
Program Definition c_ext : callconv li_c li_c :=
  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := cc_c_query ext w;
    match_reply w := cc_c_reply ext w;
  |}.

Lemma cctrans_ext_comp : cctrans (cc_compose c_ext c_ext) c_ext.
Proof.
  econstructor. instantiate (1:= fun _ _ => True).
  - red. intros. inv H.  inv H0. simpl in H, H1, H2.
    exists (se2, (tt,tt)). intuition auto. econstructor; eauto. reflexivity. reflexivity.
    exists (cq vf1 sg vargs1 m1). split.
    econstructor; eauto. reflexivity. simpl.
    generalize dependent vargs1.
    induction 1. constructor. constructor; eauto. reflexivity.
    simpl. eapply Mem.extends_refl.
    econstructor; eauto.
    exists tt. intuition auto. destruct wp1'. simpl in H6. 
    destruct H6 as [r1' [A B]]. inv A. inv B. simpl in *.
    econstructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    eapply Mem.extends_extends_compose; eauto.
  - red. intros. destruct w1 as [se' [w11 w12]]. inv H. inv H3. inv H4. inv H2.
    inv H0. inv H. inv H0. inv H2. simpl in H9, H11, H12, H , H3, H4.
    exists tt. intuition auto. reflexivity. constructor.
    constructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    eapply CallConv.val_inject_lessdef_list_compose. eauto.
    eapply (ext_lessdef_list tt). eauto.
    eapply Mem.extends_extends_compose; eauto.
    exists (tt,tt). split. reflexivity. split. exists r1. inv H2. simpl in *.
    split. econstructor; simpl; eauto. eapply val_inject_id.
    eapply Val.lessdef_refl.
    eapply Mem.extends_refl.
    econstructor; eauto. auto.
Qed.


Lemma oldfsim_newfsim_ext_c : forall  (L1 L2: semantics li_c li_c),
    Smallstep.forward_simulation (cc_c ext) (cc_c ext) L1 L2 ->
    forward_simulation c_ext L1 L2.
Proof.
  intros. red in H. inv H. constructor.
  inv X. econstructor; eauto.
  intros. exploit fsim_lts0; eauto.
  intros FPros.
  instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  fsim_match_states0 se1 se2 wB idx s1 s2).
  simpl.
  inv FPros. econstructor; eauto.
  - intros. exploit fsim_match_final_states0; eauto.
    intros [r2 [A B]]. exists r2. exists tt. intuition auto. reflexivity. reflexivity.
    destruct B as [x [X Y]]. simpl. destruct x. destruct w. auto.
  - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto. econstructor. split; eauto.
Qed.


(** Idea: first try to compose all C level passes? Clight -> LTL *)

(** Idea: Since we have totally the same incoming and outgoing lemmas. The [inj] is useless? *)
(* inj *)

Local Instance world_inj : World inj_world :=
  {
    w_state := inj_world;
    w_lens := lens_id;
    w_acci := inj_incr;
    w_acce := inj_incr;
  }.

Program Definition c_inj : callconv li_c li_c :=
  {|
    ccworld := inj_world;
    ccworld_world := world_inj;
    match_senv w := inj_stbls w;
    match_query w := cc_c_query inj w;
    match_reply w := cc_c_reply inj w;
  |}.



(** 4.1 The self-simulation mechniasm? *)  
(** 4.Modify the proofs of each pass *)
(** 5.Compose the compiler *)

  

