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

Require Import CallconvBig InjpAccoComp CallConvAlgebra.

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
          exploit H23; eauto.
  - red. intros. unfold compose_meminj in H, H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H.
    + 
      destruct (j23 bi) as [[b2' d']|] eqn: Hj2; inv H2.
      apply H13 in Hj1 as Hj1'. rewrite Hj1' in H0.
      destruct (j23' bi) as [[b2'' d'']|] eqn: Hj2'; inv H0.
      exploit H24; eauto. intros A. erewrite inject_tid; eauto.
      erewrite inject_block_tid. 3: eauto. eauto. eauto.
    + destruct (j12' b1) as [[bi d]|] eqn: Hj1'; inv H0.
      destruct (j23' bi) as [[b2' d'']|] eqn: Hj2'; inv H1.
      exploit H15; eauto. 
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
  constructor. econstructor. instantiate (1:= match_12_cctrans).
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
