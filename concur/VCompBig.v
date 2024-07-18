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
(*
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


(** TODOs*)
(** 1.Definition of c_injp as a callconv *)
(** 2.Achieve [cctrans (injp@injp) (injp)] *)
(** 3.Introduce callconv with empty world (ext, inj, CLLMMA) *)
(** 4.Try the composition of these trivial callconv using cctrans *)
(** 4.1 The self-simulation mechniasm? *)  
(** 4.Modify the proofs of each pass *)
(** 5.Compose the compiler *)

  
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
    intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
    destruct (j12 b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j23 bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    exploit H14; eauto. unfold meminj_dom. rewrite Hb. reflexivity.
    intros [X Y].
    destruct (j bi) as [[? ?] | ] eqn:Hfbi.
    {
      eapply Mem.valid_block_inject_1 in Hfbi; eauto.
    }
    edestruct H21; eauto.
Qed.

(** failed *)
(* Lemma memval_inj_eq_trans: forall mv1 mv2 mv2' f,
    memval_inject f mv1 mv2 ->
    memval_inject f mv1 mv2' ->
    mv2 = mv2'.
Proof.
  intros. destruct mv1; inv H; inv H0; eauto.
  admit.
  destruct v; inv H5; inv H4; eauto.
  admit.
  rewrite H1 in H2. inv H2. reflexivity.
Admitted.
 *)

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

Lemma injp_comp_acci : forall w11 w12 w11' w12' w1 w2,
    match_injp_comp_world (w11, w12)  w1 ->
    match_injp_comp_world (w11', w12')  w2 ->
    injp_acci w11 w11' -> injp_acci w12 w12' ->
    injp_acci w1 w2.
Proof.
  intros. inv H. inv H0.
  rename j0 into j12'. rename j1 into j23'. rename m0 into m1'. rename m4 into m2'.
  rename m5 into m3'.
  inv H1. inv H2.
  constructor; eauto.
  - destruct H11 as [S11 H11]. split. auto.
    (** a little bit different from old composition, it was (meminj_dom j) compose j.
        Now here it is arbitrary j1 compose j2 *)
    constructor.
    + destruct H11. auto.
    + intros b ofs k p [X Y] Hv.
      red in X. destruct (j12 b) as [[b2 d]|] eqn: Hj12.
      -- destruct (j23 b2) as [[b3 d2]|] eqn:Hj23.
         exfalso. unfold compose_meminj in X.
         rewrite Hj12, Hj23 in X. congruence.
         destruct H19 as [S19 H19].
         split; intro Hpm1.
         **
           eapply Mem.perm_inject in Hpm1 as Hpm2; eauto.
           erewrite Mem.unchanged_on_perm in Hpm2; eauto.
           eapply Mem.perm_inject_inv in Hpm2 as H; eauto.
           destruct H. auto. exploit H15; eauto with mem.
           intro. inv H0. red. split. auto. rewrite <- inject_other_thread; eauto.
           eapply Mem.valid_block_inject_2; eauto.
         ** eapply Mem.perm_inject in Hpm1 as Hpm2. 3: eauto.
            2: eauto.
            erewrite <- Mem.unchanged_on_perm in Hpm2; eauto.
            eapply Mem.perm_inject_inv in Hpm2 as H; eauto.
            destruct H. auto. red in H9. exfalso.
            exploit H9. 2: eauto with mem. eauto with mem.
            intro. apply H. eauto with mem.
            red. split; auto. rewrite <- inject_other_thread; eauto. 
            eapply Mem.valid_block_inject_2; eauto.
      -- inv H11. eapply unchanged_on_perm; eauto. split; auto.
    + intros b ofs [X Y] Hv.
      red in X. destruct (j12 b) as [[b2 d]|] eqn: Hj12.
      -- unfold compose_meminj in X. rewrite Hj12 in X.
         admit. (* Problem : we have to prevent the contents in m1 and m1'
                  from being like [Vint 1 ---> Vundef], simular to the free_preservation*)
      -- inv H11. eapply unchanged_on_contents; eauto. split; auto.
  - destruct H20 as [S20 H20]. split. auto.
    constructor. inv H20. auto.
    + (*perm*)
      intros b3 ofs3 k p [X Y] Hv3. red in X.
      destruct (Mem.loc_in_reach_find m2 j23 b3 ofs3) as [[b2 ofs2]|] eqn:FIND23.
      -- edestruct Mem.loc_in_reach_find_valid as [Hj23 Hpm2]; eauto.
         destruct (Mem.loc_in_reach_find m1 j12 b2 ofs2) as [[b1 ofs1] |] eqn:FIND12.
         exfalso. edestruct (Mem.loc_in_reach_find_valid) as [Hj12 Hpm1]; eauto.
         eapply X. unfold compose_meminj. rewrite Hj12, Hj23.
         reflexivity. replace (ofs3 - (ofs2 - ofs1 + (ofs3 - ofs2))) with ofs1 by lia. auto.
         eapply Mem.loc_in_reach_find_none in FIND12; eauto.
         destruct H12 as [S12 H12]. inv H12.
         exploit unchanged_on_perm. red. split. apply FIND12.
         rewrite inject_other_thread; eauto.
         eauto with mem.
         instantiate (1:= p).
         instantiate (1:= k).
         intro Hpm2eq. replace (ofs3) with (ofs2 + (ofs3 - ofs2)) by lia.
         split; intro.
         ++ eapply Mem.perm_inject_inv in H; eauto. destruct H; auto.
            eapply Mem.perm_inject. 2: eauto. eauto. apply Hpm2eq. auto.
            congruence.
         ++ eapply Mem.perm_inject_inv in H as H'; eauto. destruct H'; auto.
            eapply Mem.perm_inject; eauto. apply Hpm2eq. auto.
            exploit H23; eauto with mem. intro. inv H1.
      -- eapply Mem.loc_in_reach_find_none in FIND23; eauto.
         eapply H20; eauto. split. auto. auto.
    + (*content*)
      intros b3 ofs3 [X Y] Hpm3. red in X.
      destruct (Mem.loc_in_reach_find m2 j23 b3 ofs3) as [[b2 ofs2]|] eqn:FIND23.
      -- edestruct Mem.loc_in_reach_find_valid as [Hj23 Hpm2]; eauto.
         destruct (Mem.loc_in_reach_find m1 j12 b2 ofs2) as [[b1 ofs1] |] eqn:FIND12.
         exfalso. edestruct (Mem.loc_in_reach_find_valid) as [Hj12 Hpm1]; eauto.
         eapply X. unfold compose_meminj. rewrite Hj12, Hj23.
         reflexivity. replace (ofs3 - (ofs2 - ofs1 + (ofs3 - ofs2))) with ofs1 by lia. auto.
         eapply Mem.loc_in_reach_find_none in FIND12; eauto.
         assert (Mem.perm m2 b2 ofs2 Cur Readable).
         { replace ofs3 with (ofs2 + (ofs3 - ofs2)) in Hpm3 by lia.
           eapply Mem.perm_inject_inv in Hpm3; eauto.
           destruct Hpm3; eauto. congruence. }
         destruct H12 as [S12 H12]. inv H12.
         exploit unchanged_on_contents. red. split. apply FIND12.
         rewrite inject_other_thread; eauto. eauto.
         intro Hcon2eq.
         assert (Hpm2' : Mem.perm m2' b2 ofs2 Cur Readable).
         apply unchanged_on_perm; eauto. split. auto.
         rewrite inject_other_thread; eauto.
         eauto with mem.
         inv Hm23. inv mi_inj. exploit mi_memval; eauto.
         intro VINJ1.
         inv Hm'3. inv mi_inj. exploit mi_memval0; eauto.
         intro VINJ2.
         admit. (** Theproblem? *)
      -- eapply Mem.loc_in_reach_find_none in FIND23; eauto.
         eapply H20; eauto. split. auto. auto.
  - rauto.
  - red.
    intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (j12' b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
        destruct (j23' bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
        inv Hb'.
        destruct (j12 b1) as [[? ?] | ] eqn:Hb1.
        + apply H13 in Hb1 as Heq. rewrite Hb1' in Heq. inv Heq.
          destruct (j23 b) as [[? ?] |] eqn: Hb2.
          unfold compose_meminj in Hb. rewrite Hb1, Hb2 in Hb. congruence.
          exfalso. exploit H22; eauto. intros [X Y].
          eapply Mem.valid_block_inject_2 in Hb1; eauto.
        + exploit H14; eauto. intros [X Y].
          destruct (j23 bi) as [[? ?] |] eqn: Hb2.
          exfalso. eapply Mem.valid_block_inject_1 in Hb2; eauto.
          exploit H22; eauto. intros [X1 Y1]. intuition auto.
  - red. intros. unfold compose_meminj in H.
    destruct (j12 b1) as [[bi ?] |] eqn:Hj1; try congruence.
    destruct (j23 bi) as [[? ?] |] eqn: Hj2; try congruence.
    inv H.
    red in H15.
    specialize (H15 _ _ _ _ Hj1 H0 H1) as Hpm2'.
    eapply Mem.perm_inject in H0 as Hpm2. 3: eauto. 2: eauto.
    red in H23.
    specialize (H23 _ _ _ _ Hj2 Hpm2 Hpm2') as Hpm3'.
    replace (ofs1 + (z + z0)) with (ofs1 + z + z0) by lia.
    auto.
Admitted.

Lemma cctrans_injp_comp : cctrans (cc_compose c_injp c_injp) (c_injp).
Proof.
  econstructor. instantiate (1:= match_injp_comp_world).
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
      -- eapply injp_comp_acci; eauto. econstructor; eauto.
      -- econstructor; simpl; eauto. eapply val_inject_compose; eauto.
  - (* outgoing construction *)
    red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [x [w11 w12]].
    inv HACI. simpl in H,H0. 
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    assert (m2'_ = m2').
    { destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2. simpl in *. inv H3. inv H12. reflexivity. }
    subst m2'_.
    exists (injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23') ).
    repeat apply conj; eauto.
    + simpl.
      eapply injp_comp_acci. 3: apply H. 3: apply H0.
      econstructor; eauto.
      econstructor; eauto.
    + inv Hs. inv H1. inv H2. econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2.
      inv H3. inv H12. simpl in *.
      econstructor; simpl; eauto. eapply val_inject_compose; eauto.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    + (** The accessbility construction : use acco*)
      admit. (** Does this construction also contains new problems????? *)
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
