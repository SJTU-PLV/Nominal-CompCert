Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra VCompBig CallConvLibs.

Unset Program Cases.

(** This file contains the composition lemmas for compose the correctness of each passes into a
    big_step simulation for concurrent component *)


(** ** Part1 : The C-level composition *)


(** The C-level passes:

    SimplLocals : injp
    Cshmgen: id
    Cminorgen: injp
    Selection : wt_c @ ext
    RTLgen : ext
    Tailcall : ext
    Inlining : injp
    Renumber : id
    Constprop : option (ro @ injp)
    CSE      : option (ro @ injp)
    Deadcode  : option (ro @ injp)
    Unusedglob : injp 
    

    ?
    Alloc : wt_c @ ext @ CL
    Tunneling : cc_locset ext
    Linearize : id
    Cleanuplabels : id 
    Debugvar : id
    Stacking : wt_loc @ cc_stacking_injp
    Asmgen : cc_mach ext @ MA
 *)

(**  step1 : injp @ injp @ wt_c @ ext @ ext @ ext @ injp @ id ==========> wt_c @ injp *)

(**  1. injp @ wt_c @ ext @ injp 
     2. wt_c @ injp @ ext @ injp
     3. wt_c @ injp
 *)

(** lemmas about [wt_c] *)

Infix "@" := GS.cc_compose (at level 30, right associativity).



Inductive match_wt_1 : (injp_world * (unit * injp_world)) -> (unit * (injp_world * injp_world)) -> Prop :=
|match_wt_1_intro w1 w2 tt:
  match_wt_1 (w1, (tt, w2)) (tt, (w1, w2)).

Lemma move_wt_injp : cctrans (c_injp @ wt_c @ c_injp) (wt_c @ c_injp @ c_injp).
Proof.
  constructor.
  econstructor. instantiate (1:= match_wt_1).
  - red. intros. rename se2 into se3. rename q2 into q3.
    simpl in w2. destruct w2 as [se1'1 [ [se1'2 sig] [se2 [w1 w2]]]].
    destruct H as [Hsei [Hse1 Hse2]]. inv Hsei. inv H. rename se1'1 into se1.
    destruct H0 as [q1' [Hqi [q2 [Hq1 Hq2]]]]. inv Hqi. rename q1' into q1.
    exists (se2, (w1,(se2,((se2,sig) ,w2)))). intuition auto.
    + constructor. auto. constructor. constructor. constructor. auto.
    + inv Hq1. inv Hq2. inv H. simpl in *.
      edestruct CallConv.has_type_inject_list as (vl2 & Hvl2 & Hvl & Hvl'); eauto.
      exists (cq vf2 sg vl2 m2). split. constructor; eauto.
      exists (cq vf2 sg vl2 m2). split. constructor; eauto.
      constructor; eauto.
      eapply CallConv.val_lessdef_inject_list_compose; eauto.
    + constructor.
    + destruct wp1' as [w1' [ss w2']]. destruct ss.
      destruct H1 as [ACCE1 [_ ACCE2]]. simpl in ACCE1, ACCE2.
      inv H0. rename w0 into wp1. rename w3 into wp2.
      destruct H2 as [ACCI1 [_ ACCI2]]. simpl in ACCI1, ACCI2.
      exists (tt, (w1', w2')). intuition auto.
      repeat constructor; eauto.
      repeat constructor; eauto. rename r2 into r3.
      destruct H3 as [r2' [Hr1 [r2 [Hri Hr2]]]]. inv Hri.
      repeat econstructor; eauto.
      simpl. simpl in H0.
      inv Hr1.
      eapply val_has_type_inject; eauto.
  - red. intros.  rename se2 into se3. rename q2 into q3.
    simpl in wp1. rename wp2 into xxx.
    destruct wp1 as [wp1 [ss wp2]]. destruct ss. inv H2. simpl in w1.
    destruct w1 as [se2' [w1 [se2 [[se2'' sig] w2]]]].
    destruct H1 as [ACCI1 [X ACCI2]]. simpl in ACCI1, ACCI2. inv X.
    destruct H as [Hse1 [Hsei Hse2]]. inv Hsei. inv H.
    destruct H0 as [q2 [Hq1 [q2' [Hqi Hq2]]]]. inv Hqi. rename q2' into q2.
    exists (se1,((se1,sig),(se2,(w1,w2)) )). intuition auto.
    + repeat constructor; auto.
    + repeat constructor; auto.
    + exists q1. constructor.
      inv Hq1. inv H. constructor. simpl in *. split; auto.
      eapply val_has_type_list_inject; eauto.
      exists q2. constructor; auto.
    + destruct wp2' as [ss [wp1' wp2']]. destruct ss.
      destruct H0 as [x [E1 E2]]. simpl in x,E1,E2. rename r2 into r3.
      destruct H1 as [r1' [Hri [r2 [Hr1 Hr2]]]]. inv Hri.
      exists (wp1', (tt, wp2')). intuition auto.
      repeat constructor; auto.
      inv Hr1. simpl in *.
      exists (cr (Val.ensure_type vres2 (proj_sig_res sig)) m2').
      split. constructor; eauto.
      eapply CallConv.has_type_inject; eauto.
      exists (cr (Val.ensure_type vres2 (proj_sig_res sig)) m2').
      constructor. constructor. apply Val.ensure_has_type.
      inv Hr2. econstructor; eauto.
      eapply Val.inject_ensure_type_l; eauto.
      constructor.
Qed.

Inductive match_assoc_1 {A B C : Type}: (A * (B * C)) -> (A * B * C) -> Prop :=
|match_assoc_1_intro a b c: match_assoc_1 (a,(b,c)) (a,b,c).

Lemma cc_compose_assoc_1 {A B C D}:
  forall (cc1 : GS.callconv A B) (cc2 : GS.callconv B C) (cc3 : GS.callconv C D),
    cctrans (cc1 @ cc2 @ cc3) ((cc1 @ cc2) @ cc3).
Proof.
  constructor.
  econstructor. instantiate (1:= match_assoc_1).
  - red.
    intros [sec [[seb [w1 w2]] w3]] sea sed qa qd.
    intros ((Hseab & Hsebc) & Hsecd) (qc & (qb & Hqab & Hqbc) & Hqcd).
    exists (seb, (w1, (sec, (w2, w3)))). intuition auto.
    repeat constructor; auto.
    repeat econstructor; eauto. simpl.
    constructor. 
    destruct wp1' as [w1' [w2' w3']].
    rename wp2 into wp2'.
    destruct wp1 as [wp1 [wp2 wp3]]. inv H.
    destruct H0 as [E1 [E2 E3]]. destruct H1 as [I1 [I2 I3]]. simpl in E1,E2,E3,I1,I2,I3.
    exists ((w1',w2'),w3'). intuition auto.
    repeat constructor; auto.
    repeat constructor; auto.
    destruct H2 as [rb [Hr1 [rc [Hr2 Hr3]]]].
    repeat econstructor; eauto.
  - red.
    intros [w1 [w2 w3]] [[wp1 wp2] wp3] [seb [w1' [sec [w2' w3']]]]
    sea sed qa qd.
    intros (Hseab & Hsebc & Hsecd) (qb & Hqab & qc & Hqbc & Hqcd) [I1 [I2 I3]] Hm.
    simpl in I1, I2, I3. inv Hm.
    exists (sec,(seb,(w1', w2'),w3')). intuition auto.
    repeat constructor; auto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    simpl in H. destruct wp2' as [[w1'' w2''] w3''].
    destruct H as [[E1 E2]E3]. simpl in E1, E2, E3.
    exists (w1'', (w2'', w3'')). intuition auto.
    repeat constructor; auto.
    destruct H0 as [rc [[rb [Hr1 Hr2]] Hr3]].
    repeat econstructor; eauto.
    constructor.
Qed.

Lemma move_wt_ext : cctrans (c_injp @ wt_c @ c_ext) (wt_c @ c_injp @ c_ext).
Admitted. (*should be the same as above*)

Inductive match_assoc_2 {A B C : Type}: (A * B * C) -> (A * (B * C)) -> Prop :=
|match_assoc_2_intro a b c: match_assoc_2 (a,b,c) (a,(b,c)).

Lemma cc_compose_assoc_2 {A B C D}:
  forall (cc1 : GS.callconv A B) (cc2 : GS.callconv B C) (cc3 : GS.callconv C D),
    cctrans ((cc1 @ cc2) @ cc3) (cc1 @ cc2 @ cc3).
Proof.
  constructor.
  econstructor. instantiate (1:= match_assoc_2).
  - red.
    intros [seb [w1 [sec [w2 w3]]]]
      sea sed qa qd.
    intros (Hseab & Hsebc & Hsecd) (qb & Hqab & qc & Hqbc & Hqcd).
    exists (sec,((seb,(w1,w2)),w3)).
    intuition auto.
    repeat constructor; auto.
    repeat econstructor; eauto.
    constructor.
    destruct wp1' as [[w1' w2'] w3'].
    rename wp2 into xx.
    destruct wp1 as [[wp1 wp2] wp3]. inv H.
    destruct H0 as [[E1 E2] E3]. destruct H1 as [[I1 I2] I3].
    simpl in E1, E2, E3, I1, I2, I3. destruct H2 as [rc [[rb [Hr1 Hr2]] Hr3]].
    exists (w1', (w2', w3')). intuition auto.
    repeat constructor; auto.
    repeat constructor; auto.
    repeat econstructor; eauto.
  - red.
    intros [[w1 w2] w3] [wp1 [wp2 wp3]] [sec [[seb [w1' w2']] w3']] sea sed qa qd.
    intros ((Hseab & Hsebc) & Hsecd) (qb & (Hqab & qc & Hqbc) & Hqcd) [[I1 I2] I3] Hm.
    simpl in I1, I2, I3. inv Hm.
    exists (seb, (w1', (sec, (w2', w3')))). intuition auto.
    repeat constructor; auto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    simpl in H. destruct wp2' as [w1'' [w2'' w3'']].
    destruct H as [E1 [E2 E3]]. simpl in E1, E2, E3.
    exists ((w1'', w2''), w3''). intuition auto.
    repeat constructor; auto.
    destruct H0 as [rb [Hr1 [rc [Hr2 Hr3]]]].
    repeat econstructor; eauto.
    constructor.
Qed.

Require Import InjpAccoComp.

Inductive match_injp_ext_comp_world : injp_world -> injp_world -> injp_world -> Prop :=
|world_comp_intro:
  forall m1 m2 m3 m4 j12 j34 j14 Hm12 Hm34 Hm14,
    j14 = compose_meminj j12 j34 ->
    Mem.extends m2 m3 ->
    match_injp_ext_comp_world (injpw j12 m1 m2 Hm12) (injpw j34 m3 m4 Hm34) (injpw j14 m1 m4 Hm14).

Definition injp_ext_cctrans : injp_world * (unit * injp_world) -> injp_world -> Prop :=
  fun wjxj w =>
    let w1 := fst wjxj in let w2 := snd (snd wjxj) in
    match_injp_ext_comp_world w1 w2 w /\ external_mid_hidden w1 w2.

Lemma injp_ext_comp_acce : forall w11 w12 w11' w12' w1 w2,
    injp_trivial_comp_world (w11, w12)  w1 ->
    match_injp_ext_comp_world w11' w12'  w2 ->
    injp_acce w11 w11' -> injp_acce w12 w12' ->
    injp_acce w1 w2.
Proof.
  intros. inv H. inv H0. rename Hm34 into Hm34'.
  rename Hm23 into Hm34. rename m4 into m3'. rename m5 into m4'.
  rename m3 into m4. rename m0 into m1'. rename m2 into m2'.
  inv H1. inv H2.
  econstructor; eauto.
  - destruct H12. split. auto. eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split; auto. red. unfold meminj_dom.
    rewrite H. reflexivity.
  - assert (j = compose_meminj (meminj_dom j) j).
    rewrite meminj_dom_compose. reflexivity.
    rewrite H. rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
    destruct (j12 b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j34 bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    exploit H15; eauto. unfold meminj_dom. rewrite Hb. reflexivity.
    intros [X Y].
    destruct (j bi) as [[? ?] | ] eqn:Hfbi.
    {
      eapply Mem.valid_block_inject_1 in Hfbi; eauto.
    }
    edestruct H23; eauto. erewrite <- inject_tid; eauto.
    inv Hm0. inv mi_thread. erewrite <- Hjs; eauto.
  - red. intros. unfold compose_meminj in H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H0.
    destruct (j34 bi) as [[b2' d']|] eqn: Hj2; inv H2.
    exploit H16; eauto. unfold meminj_dom. rewrite H. reflexivity.
    intros [A B]. split; auto.
    intro. apply B. red. erewrite inject_block_tid; eauto.
Qed.

Lemma injp_ext_comp_acci : forall w11 w12 w11' w12' w1 w2,
    match_injp_ext_comp_world w11 w12 w1 ->
    external_mid_hidden w11 w12 ->
    match_injp_ext_comp_world w11' w12'  w2 ->
    injp_acci w11 w11' -> injp_acci w12 w12' ->
    injp_acci w1 w2.
Proof.
  intros. inv H. inv H1. inv H0.
  rename j0 into j12'. rename j1 into j34'.
  rename m0 into m1'. rename m7 into m4'.
  rename m6 into m3'. rename m5 into m2'.
  inv H2. inv H3.
  constructor; eauto.
  - destruct H13 as [S13 H13]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. red in X. unfold compose_meminj in X.
    destruct (j12 b) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j34 b2) as [[b3 d2]|] eqn:Hj23; try congruence.
    eapply Hconstr1 in Hj12; eauto. congruence.
    erewrite <- inject_other_thread; eauto.
  - destruct H23 as [S23 H23]. split. auto.
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
    destruct (j34' bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    destruct (j12 b1) as [[? ?] | ] eqn:Hb1.
    + apply H15 in Hb1 as Heq. rewrite Hb1' in Heq. inv Heq.
      destruct (j34 b) as [[? ?] |] eqn: Hb2.
      unfold compose_meminj in Hb. rewrite Hb1, Hb2 in Hb. congruence.
      exfalso. exploit H25; eauto.
      erewrite <- inject_tid; eauto.
      erewrite <- inject_val_tid. 3: eauto. auto. eauto.
      intros [X Y].
      eapply Mem.valid_block_inject_2 in Hb1; eauto.
    + exploit H16; eauto. intros [X Y].
      destruct (j34 bi) as [[? ?] |] eqn: Hb2.
      exfalso. eapply Mem.valid_block_inject_1 in Hb2; eauto.
      exploit H25; eauto.
  - red. intros. unfold compose_meminj in H, H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H.
    + 
      destruct (j34 bi) as [[b2' d']|] eqn: Hj2; inv H2.
      apply H15 in Hj1 as Hj1'. rewrite Hj1' in H0.
      destruct (j34' bi) as [[b2'' d'']|] eqn: Hj2'; inv H0.
      exploit H26; eauto. intros A. erewrite inject_tid; eauto.
      erewrite inject_block_tid. 3: eauto. eauto. eauto.
    + destruct (j12' b1) as [[bi d]|] eqn: Hj1'; inv H0.
      destruct (j34' bi) as [[b2' d'']|] eqn: Hj2'; inv H1.
      exploit H17; eauto. 
  - red. intros. unfold compose_meminj in H. rename b2 into b3.
    destruct (j12 b1) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j34 b2) as [[b3' d2]|] eqn:Hj23; try congruence. inv H.
    red in H18. specialize (H18 _ _ _ _ Hj12 H0 H1 H2) as Hp2'.
    eapply Mem.perm_inject in H1 as Hp3. 3: eauto. 2: eauto.
    red in H27. assert (H0': fst b2 <> Mem.tid (Mem.support m3)).
    erewrite <- inject_block_tid. 3: eauto. 2: eauto.
    erewrite <- inject_tid; eauto.
    assert (Hp3' : ~ Mem.perm m3' b2 (ofs1 + d) Max Nonempty).
    (** We cannot prove this because [ext] doens not enforce [free_preserved]
     *)
    admit.
    specialize (H27 _ _ _ _ Hj23 H0' Hp3 Hp3') as Hp4.
    rewrite Z.add_assoc. auto.
Admitted.

(** Is this correct? do we have to enforce internal [ro] and [mpd]
    properties for c_ext (and prove them in passes) to absorb it? *)
Lemma cctrans_injp_ext:
  cctrans (c_injp @ c_ext @ c_injp) c_injp.
Proof.
  constructor. econstructor. instantiate (1:= injp_ext_cctrans).
  (* Compute (GS.gworld (c_injp @ c_ext @ c_injp)). *)
  - red. intros w2 se1 se2 q1 q2 Hse Hq. inv Hse. inv Hq.
    inv H4. clear Hm1 Hm2 Hm3. simpl in H2, H3.
    rename m0 into m1. rename m3 into m2.
    (* Compute (GS.ccworld (c_injp @ c_ext @ c_injp)). *)
    exists (se1,((injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm)),(se1,(tt,(injpw f m1 m2 Hm))))).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. eapply match_stbls_dom; eauto.
      constructor. constructor. constructor; eauto.
    + exists (cq vf1 sg vargs1 m1). split. constructor; simpl; eauto.
      eapply val_inject_dom; eauto. eapply val_inject_list_dom; eauto.
      exists (cq vf1 sg vargs1 m1). split. constructor; simpl; eauto.
      reflexivity. generalize dependent vargs1.
      induction 1. constructor. constructor. reflexivity. auto.
      apply Mem.extends_refl.
      econstructor; eauto. constructor.
    + constructor. rewrite meminj_dom_compose. auto. apply Mem.extends_refl.
    + constructor. intros. unfold meminj_dom in H6.
      destr_in H6.
      intros. eexists. eexists. split. eauto.
      unfold meminj_dom. rewrite H7. do 2 f_equal. lia.
    + intros r1 r4 [wpa [t wpb]] wp2 [wpa' [t' wpb']] MS.
      intros [ACE1 [X ACE2]] [ACI1 [Y ACI2]] [r2 [Hr1 [r3 [Hr2 Hr3]]]].
      simpl in *. destruct Hr2 as [z [Z Hr2]]. clear X Y Z.
      destruct wpa' as [j12 m1' m2' Hm1']. destruct wpb' as [j23 m2'_ m3' Hm2'].
      inv Hr1. inv Hr2. inv Hr3. simpl in *. inv H6. inv H13.
      clear Hm1 Hm2 Hm3 Hm4 Hm5 Hm6. rename m1'0 into m1'.
      rename m2'0 into m2'. rename m2'1 into m3'. rename m2'2 into m4'.
      assert (Hm': Mem.inject (compose_meminj j12 j23) m1' m4').
      eapply Mem.inject_compose. eauto.
      eapply Mem.extends_inject_compose. eauto. eauto.
      exists (injpw (compose_meminj j12 j23) m1' m4' Hm').
      repeat apply conj.
      * eapply injp_ext_comp_acce.
        2: { econstructor; eauto. }
        2: eauto. 2: eauto. constructor.
      * admit.
      * econstructor; simpl; eauto.
        eapply val_inject_compose. eauto.
        rewrite <- (compose_meminj_id_left j23).
        eapply val_inject_compose. eauto. eauto.
  - red. intros [wpa [x wpb]] wp2 [se2 [w1 [se2' [y w2]]]].
    intros se1 se3 q1 q3 [Hs1 [Hs2 Hs3]] [q2 [Hq1 [q2' [Hq2 Hq3]]]].
    intros [ACI1 [X ACI2]]. simpl in ACI1, ACI2. clear X. simpl in x,y.
    intros MS. inv MS. simpl in H, H0.
    destruct w1 as [j12' m1' m2' Hm12'].
    destruct w2 as [j34' m3' m4' Hm34'].
    inv H.
    assert (Hm14' : Mem.inject (compose_meminj j12' j34') m1' m4').
    eapply Mem.inject_compose; eauto. eapply Mem.extends_inject_compose; eauto.
    inv Hq1. inv Hq2. inv Hq3. inv H3. inv H16. auto.
    exists (injpw (compose_meminj j12' j34') m1' m4' Hm14').
    repeat apply conj.
    + admit.
    + inv Hs1. inv Hs2. inv Hs3.
      constructor; eauto. eapply Genv.match_stbls_compose; eauto.
    + inv Hq1. inv H3. inv Hq2. inv Hq3. inv H15.
      econstructor; simpl; eauto. eapply val_inject_compose. eauto.
      rewrite <- (compose_meminj_id_left j34').
      eapply val_inject_compose. eauto. eauto.
      eapply CKLRAlgebra.val_inject_list_compose. econstructor.
      split. eauto. rewrite <- (compose_meminj_id_left j34').
      simpl in H10.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    +  intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. inv MR. simpl in H,H1.
       destruct wp2' as [j13'' m1'' m3'' Hm13'].
       simpl in H, H1.
       assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j34' m3' m4' Hm34')).
       admit.
       admit.
Admitted.




