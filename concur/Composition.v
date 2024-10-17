Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra VCompBig CallConvLibs StackingRefine.


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

Lemma move_wt_ext : cctrans (c_injp @ wt_c @ c_ext) (wt_c @ c_injp @ c_ext).
Proof.
  constructor.
  econstructor. instantiate (1:= fun a b => fst a = fst (snd b) /\ snd (snd a) = snd (snd b)).
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
    + destruct wp1' as [w1' [ss w2']]. destruct ss.
      destruct H1 as [ACCE1 [_ ACCE2]]. simpl in ACCE1, ACCE2.
      destruct wp1 as [wp1 [tt wp2aa]]. simpl in H4, H5. destruct wp2 as [tt1 [x y]]. simpl in H4, H5. subst x y.
      rename wp2aa into wp2.
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
    simpl in wp1. destruct wp2 as [ss [x y]]. destruct ss.
    destruct wp1 as [wp1 [ss wp2]]. destruct ss. inv H2.  simpl in H3, H4. subst x y.
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



(** Unification of the outgoing side *)

Definition cc_compcert : GS.callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp_new.

(** The C-level simulation convention *)
Definition cc_c_level : GS.callconv li_c li_c := ro @ wt_c @ c_injp.

Definition cc_compcert_1 : GS.callconv li_c li_asm :=
    cc_c_level @
    cc_c_locset @ cc_stacking_injp @ cc_mach_asm.


(** The first expand of cc_compcert for both directions *)
Theorem cc_compcert_merge:
  forall p tp,
  GS.forward_simulation cc_compcert_1 (Clight.semantics1 p) (Asm.semantics tp) ->
  GS.forward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros.
  unfold cc_compcert, cc_compcert_1 in *.
Admitted.

Require Import CallConv.
Require Import InjpAccoComp.
Inductive ro_injp_match : (unit * injp_world) * (unit * injp_world) -> (unit * injp_world) -> Prop :=
|ro_injp_match_intro w1 w2 w3 a b c:
  match_12_cctrans (w1, w2) w3 ->
  ro_injp_match ((a, w1),(b,w2)) (c,w3).
      
Lemma cctrans_ro_injp_compose : cctrans ((ro @ c_injp) @ (ro @ c_injp)) (ro @ c_injp).
Proof.
  constructor. econstructor. instantiate (1:= ro_injp_match).
  - (*incoming construction*)
    red. intros [se [[xse m] w2]]. intros. inv H. inv H0. inv H1. inv H2.
    inv H. inv H2. inv H5. simpl in H2, H6. inv H. inv H7. clear Hm1 Hm2 Hm3.
    inv H0. rename se into se1. rename m0 into m1. rename m3 into m2.
    (* Compute  GS.ccworld ((ro @ c_injp) @ ro @ c_injp). *)
    exists (se1, (se1, (row se1 m1, injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm)),(se1,(row se1 m1,injpw f m1 m2 Hm)))).
    repeat apply conj; eauto.
    + simpl. split. split. constructor. reflexivity. constructor; eauto. eapply match_stbls_dom; eauto.
      split. econstructor. reflexivity. econstructor; eauto.
    + exists (cq vf1 sg vargs1 m1). split.
      exists (cq vf1 sg vargs1 m1). split.
      econstructor; simpl; eauto. constructor. eauto.
      econstructor; simpl; eauto.
      eapply val_inject_dom; eauto.
      eapply val_inject_list_dom; eauto.
      exists (cq vf1 sg vargs1 m1). split.
      econstructor; eauto. simpl. constructor. eauto.
      econstructor; eauto. constructor.
    + simpl. constructor. econstructor.
      econstructor. rewrite meminj_dom_compose. reflexivity.
      econstructor; eauto. intros. unfold meminj_dom in H0.
      destruct (f b1) as [[? ?]|] eqn: Hf; inv H0. congruence.
      intros. exists b2, ofs2. split. auto. unfold meminj_dom. rewrite H5.
      replace (ofs2 - ofs2) with 0 by lia. reflexivity.
    + intros r1 r3 wp1 wp2 wp1' Hmatch [[_ Hae1] [_ Hae2]] HACCI Hr. simpl in Hae1, Hae2.
      destruct wp1' as [[wx11' wp11'] [wx12' wp12']]. simpl. simpl in *.
      destruct wp1 as [[wx11 wp11] [wx12 wp12]]. simpl in *. destruct HACCI as [[_ HAci1] [_ HAci2]].
      simpl in *. destruct wp11' as [j12 m1' m2' Hm1']. destruct wp12' as [j23 m2'_ m3' Hm2'].
      destruct Hr as [r2 [[r1' [Hrx Hr1]] [r2' [Hry Hr2]]]].
      inv Hrx. inv Hry. inv Hr1. inv Hr2. inv H7. inv H14. clear Hm1 Hm2 Hm3 Hm4 Hm5 Hm6.
      rename m1'0 into m1'.
      rename m2'0 into m2'. rename m2'1 into m3'.
      exists (tt, injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm1' Hm2')).
      repeat apply conj; eauto.
      -- eapply injp_comp_acce. 3: apply Hae1. 3:apply Hae2.
         econstructor; eauto.
         econstructor; eauto.
      -- inv Hmatch. inv H15. simpl. eapply injp_comp_acci; eauto. econstructor; eauto.
      -- exists (cr vres1 m1'). split. constructor. eauto.
        econstructor; simpl; eauto. eapply val_inject_compose; eauto.
  - (* outgoing construction *)
    red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [se [[xse [wx11 w11]] [xxse [wx12 w12]]]].
    simpl in HACI. destruct HACI as [[_ ACI1] [_ ACI2]]. simpl in ACI1, ACI2.
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    destruct Hs as [[Hsx Hs1] [Hsy Hs2]]. inv Hsx. inv Hsy. simpl in H0. destruct wx11. subst.
    simpl in H1. destruct wx12. subst.
    destruct Hq as [q2 [[q1' [Hqx Hq1]] [q2' [Hqy Hq2]]]]. inv Hqx. inv Hqy.
    assert (m2'_ = m2').
    { inv Hq1. inv Hq2. simpl in *. inv H4. inv H13.
      reflexivity. }
    subst m2'_.
    exists (xse, (row xse m1', injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23'))).
    repeat apply conj; eauto.
    + simpl. eauto.
    + simpl. inv H; simpl in *.
      eapply injp_comp_acci; eauto.
      econstructor; eauto.
    + econstructor; eauto. constructor. constructor.
      inv Hs1. inv Hs2. econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + inv Hq1. inv Hq2.
      inv H4. inv H13. simpl in *. exists (cq vf1 sg vargs1 m1). split.
      econstructor; eauto. constructor. inv H0. eauto.
      econstructor; simpl; eauto. eapply val_inject_compose; eauto.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    + (** The accessbility construction : use acco*)
      intros r1 r3 [tt wp2'] [_ ACCO1] [r1' [Hr1 Hr2]]. simpl in ACCO1. inv Hr1. inv Hr2. simpl in H3,H4.
      destruct wp2' as [j13'' m1'' m3'' Hm13'].
      simpl in H3, H4. inv H. simpl in H6. (* inv H0. inv H1. inv Hq1. inv Hq2. *)
      assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j23' m2' m3' Hm23')).
      destruct w0, w2.  inv H5.
      exploit external_mid_hidden_acci; eauto. 
      exploit injp_acce_outgoing_constr; eauto.
      intros (j12'' & j23'' & m2'' & Hm12'' & Hm23'' & COMPOSE & ACCE1 & ACCE2 & HIDDEN & _).
      exists ((tt,injpw j12'' m1'' m2'' Hm12''),(tt,injpw j23'' m2'' m3'' Hm23'')).
      repeat apply conj; simpl; eauto.
      -- inv H4.
         rename vres2 into vres3. exploit compose_meminj_midvalue; eauto.
         intros [vres2 [RES1 RES2]]. 
         exists (cr vres2 m2''). split.
         exists (cr vres1 m1'0). split. econstructor; eauto. inv H2. constructor.
         inv H0. inv Hq1. inv H12. eauto.
         repeat econstructor; eauto.
         exists (cr vres2 m2''). split. econstructor; eauto. constructor.
         inv H1. inv Hq2. inv H12. inv ACCE1. econstructor; eauto.
         destruct H19 as [_ [X _]]. auto.
         econstructor; eauto. constructor.
      -- simpl. econstructor. econstructor; eauto. constructor; eauto.
Qed.


Lemma cctrans_inv {I J: invariant li_c}: cctrans (I @ J) (J @ I).
Proof.
   constructor.
  econstructor. instantiate (1:= eq).
  - red. intros [xse [w1 w2]] se1 se q1 q2 [Hs1 Hs2] [q1' [Hq1 Hq2]].
    inv Hs1. inv Hs2. inv Hq1. inv Hq2.
    exists (se, (w2 , w1)). repeat apply conj; eauto.
    + repeat constructor; eauto.
    + repeat econstructor; eauto.
    + intros. subst. exists (tt,tt). repeat apply conj; simpl; eauto.
      destruct wp1' as [a b].
      destruct H6 as [r' [Hr1 Hr2]]. inv Hr1. inv Hr2.
      repeat econstructor; eauto.
  - red. intros [wa wb]. intros wp2 [se [wa' wb']] se1 se2 q1 q2 [Hs1 Hs2] [q' [Hq1 Hq2]] [ACE1 ACE2] Hm.
    subst wp2.
    inv Hs1. inv Hs2. inv Hq1. inv Hq2.  simpl in ACE1, ACE2.
    exists (se2, (wb', wa')). repeat apply conj; eauto.
    + repeat constructor; eauto.
    + repeat econstructor; eauto.
    + intros. destruct wp2' as [wt wr]. exists (wt, wr).
      repeat constructor; eauto.
      destruct H4 as [r' [Hr1 Hr2]].
      inv Hr1. inv Hr2.
      repeat econstructor; eauto.
Qed.

Lemma cctrans_ro_wt_c : cctrans (ro @ wt_c) (wt_c @ ro).
Proof.
  eapply cctrans_inv; eauto.
Qed.        

Lemma cctrans_wt_c_ro : cctrans (wt_c @ ro) (ro @ wt_c).
Proof.
  eapply cctrans_inv; eauto.
Qed.

Lemma cctrans_lessdef_c_ext: cctrans c_ext (lessdef_c @ c_ext).
Proof.
  constructor. 
  econstructor. instantiate (1:= fun a b => a = snd b).
  - red. intros. destruct w2 as [se [tt [m1 m2 Hm]]].
    inv H. inv H1. inv H2. destruct H0 as [q' [Hq1 Hq2]].
    inv Hq1. inv Hq2. inv H7. clear Hm1 Hm2. uncklr.
    exists (extw m m3 Hm). repeat apply conj.
    + constructor.
    + constructor. uncklr. eauto. uncklr.
      eapply Val.lessdef_list_trans; eauto. constructor. auto.
    + simpl. reflexivity.
    + intros r1 r2 [m1' m2' Hm'] wp2 [m1'' m2'' Hm''] Hmat ACE ACI Hr.
      simpl in ACE, ACI. destruct wp2. inv Hmat. simpl in H0. subst w0.
      exists (tt, extw m1'' m2'' Hm''). repeat apply conj; simpl; eauto.
      exists r1. split. destruct r1. econstructor; eauto.
      eauto.
  - red. intros [m1 m2 Hm] wp2 [m1' m2' Hm'] se1 se2 q1 q2 Hse Hq ACI Hmat.
    destruct wp2. simpl in Hmat. subst w0. inv Hse. inv Hq. inv H1. clear Hm1 Hm2.
    uncklr.
    exists (se2, (tt, (extw m0 m3 Hm'))). repeat apply conj; simpl; eauto.
    + exists (cq vf1 sg vargs1 m0). split. econstructor; eauto.
      eapply lessdef_list_refl.
      econstructor; uncklr; eauto. constructor.
    + intros r1 r2 [tt [m1'' m2'' Hm'']]. intros [ACE1 ACE2] [r' [Hr1 Hr2]].
      simpl in ACE2.
      exists (extw m1'' m2'' Hm''). repeat apply conj; simpl; eauto.
      inv Hr1. inv Hr2. inv H7. econstructor; uncklr; eauto.
      eapply Val.lessdef_trans; eauto. constructor.
Qed.

Lemma cctrans_wt_c_compose : cctrans (wt_c @ c_injp @ wt_c @ lessdef_c) (wt_c @ c_injp).
Proof.
  constructor.
  econstructor. instantiate (1:= fun a b => fst (snd a) = snd b).
  - red. intros [se [[se' sg] [j mx my Hm]]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]]. 
    inv Hse1. inv Hse2. inv Hq1. inv Hq2. inv H4. clear Hm4 Hm5 Hm6. simpl in H1, H2.
    simpl in H0. destruct H0. subst sg0. simpl in H. subst se'.
    (*Compute (GS.ccworld (wt_c @ c_injp @ wt_c @ lessdef_c)).
     = (Genv.symtbl * (Genv.symtbl * signature * (Genv.symtbl * (injp_world * (Genv.symtbl * (Genv.symtbl * signature * unit))))))%type
     : Type *)
    exists (se, (se, sg, (se2, ((injpw j m1 m2 Hm),(se2,(se2,sg,tt)))))). repeat apply conj; simpl; eauto.
    + repeat apply conj; eauto. constructor; eauto. constructor; eauto.
    + exists (cq vf1 sg vargs1 m1). split. constructor; eauto.
      exploit  has_type_inject_list; eauto. intros (vargs2' & Htype & Hinj & Hext).
      exists (cq vf2 sg vargs2' m2). split. constructor; eauto. constructor.
      exists (cq vf2 sg vargs2' m2). split. econstructor; eauto.
      constructor; eauto.
    +
      (* Compute (GS.gworld (wt_c @ c_injp @ wt_c @ lessdef_c)). *)
      intros r1 r2 [t1 [[j' m1' m2' Hm'] [t2 t3]]]. simpl in t1,t2,t3.
      intros [t4 wp2]. intros [t5 [[j'' m1'' m2'' Hm''] [t6 t7]]].
      intros Hmatch [_ [ACE [_ _]]] [_ [ACI [_ _]]] Hr.
      simpl in Hmatch. subst wp2. simpl in ACE, ACI.
      exists (tt, injpw j'' m1'' m2'' Hm''). repeat apply conj; eauto.
      rename r2 into r5.
      destruct Hr as [r2 [Hr1 [r3 [Hr2 [r4 [Hr3 Hr4]]]]]].
      inv Hr1. inv Hr2. inv H8. clear Hm4 Hm5 Hm6. inv Hr3. inv Hr4. simpl in *.
      exists (cr vres1 m1'0). split. econstructor; eauto.
      econstructor; eauto. simpl. eapply Mem.val_inject_lessdef_compose; eauto.
      constructor.
  - red.
    intros [t1 [[j m1 m2 Hm] [t2 t3]]] [t4 wp2].
    intros [se1 [[se2 sg] [se3 [[j' m1' m2' Hm'] [se4 [[se5 sg'] tt]]]]]].
    intros se0 se6 q1 q2 Hse1 Hq [_ [ACI [_ _]]] Hr. simpl in ACI.
    destruct Hse1 as [a [b [c d]]]. inv a. inv b. inv c. inv d. 
    destruct Hq as [q1' [Hq1 [q2' [Hq2 [q3' [Hq3 Hq4]]]]]].
    inv Hq1. inv Hq2. inv H5. clear Hm4 Hm5 Hm6. inv Hq3. inv Hq4. simpl in H2, H4.
    simpl in H0. subst. simpl in H. subst. simpl in Hr. subst wp2. destruct H1. simpl in H. subst.
    destruct H5. simpl in H. subst. simpl in H0, H1.
    exists (se1,((se1, sg0), injpw j' m0 m3 Hm')). repeat apply conj; eauto.
    + simpl. eauto.
    + split. constructor. reflexivity. constructor; eauto.
    + simpl.  exists (cq vf1 sg0 vargs1 m0). split. econstructor; eauto.
      econstructor; eauto. simpl.  
      eapply val_inject_lessdef_list_compose; eauto. constructor.
    + intros r1 r2 [t8 [j'' m1'' m2'' Hm'']] [_ ACE] Hr. simpl in ACE.
      destruct Hr as [r' [Hr1 Hr2]]. inv Hr1. inv Hr2. simpl in H5. inv H9.
      clear Hm4 Hm5 Hm6. simpl in H.
      (* Compute (GS.gworld (wt_c @ c_injp @ wt_c @ lessdef_c)). *)
      exists (tt, ((injpw j'' m1' m2' Hm''), (tt,tt))). repeat apply conj; simpl; eauto.
      exists (cr vres1 m1'). split. econstructor; eauto.
      set (res' := Val.ensure_type vres2 (proj_sig_res sg0) ).
      exists (cr res' m2'). split. econstructor; eauto. simpl.
      eapply has_type_inject; eauto. constructor.
      exists (cr res' m2'). split. econstructor; eauto. simpl.
      eapply Val.ensure_has_type.
      econstructor; eauto. unfold res'. destruct vres2, (proj_sig_res sg0); auto.
Qed.

Lemma cctrans_injp_ext_ccstacking : cctrans (locset_injp @ locset_ext @ cc_stacking_injp) cc_stacking_injp.
Admitted.

Lemma cctrans_wt_loc_stacking : cctrans (wt_loc @ cc_stacking_injp) (cc_stacking_injp).
Proof.
  constructor. econstructor. instantiate (1:= fun a b => snd a = b).
  - red. intros [[j m1 my Hm] sg ls1 rs2 sp2 m2]. intros.
    inv H. inv H0. clear Hm4 Hm5 Hm6.
    (* Compute GS.ccworld (wt_loc @ cc_stacking injp). *)
    exists (se1, (se1, sg, stkjw (injpw j m1 m2 Hm) sg ls1 rs2 sp2 m2)). repeat apply conj; eauto.
    + econstructor. constructor. constructor. constructor; eauto.
    + exists (lq vf1 sg ls1 m1). split. econstructor; eauto. constructor.
      intros l Hl. destruct Hl.
      * apply always_has_mreg_type.
      * cbn -[Z.add Z.mul]. rewrite <- (type_of_chunk_of_type ty) at 2.
        inv H16 . destruct H1 as [A B]. exploit B; eauto.
        intros [b [Hload]]. simpl in H1.
        eapply (val_has_type_inject); eauto.
        unfold load_stack in Hload. unfold Mem.loadv in Hload.
        destr_in Hload.
        eapply Mem.load_type. eauto.
      * econstructor; eauto. 
    + intros r1 r2 [t1 [j' m1' m2' Hm']] wp2 [t2 [j'' m1'' m2'' Hm'']].
      intros Hmatch [_ ACE] [_ ACI] Hr. simpl in ACE, ACI. simpl in Hmatch. subst wp2.
      destruct Hr as [r' [Hr1 Hr2]]. inv Hr1. inv Hr2. simpl in H.
      exists (injpw j'' m1'' m2'' Hm''). repeat apply conj; eauto.
      econstructor; eauto.
  - red. intros [t1 [j m1 m2 Hm]] wp2. intros [xse [[xse2 sg] [[j' m1' m2'x Hm'] sg' ls1 rs2 sp2 m2']]].
    intros se1 se2 q1 q2 [Hse1 Hse2] [q' [Hq1 Hq2]] [_ ACI] Hmatch. inv Hse1. inv Hse2. inv Hq1. inv Hq2.
    simpl in ACI.
    exists (stkjw (injpw j' m1' m2' Hm') sg' ls1 rs2 sp2 m2'). repeat apply conj; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + intros r1 r2 [j'' m1'' m2'' Hm''] ACE Hr. simpl in ACE.
      exists (tt, injpw j'' m1'' m2'' Hm''). repeat apply conj; simpl; eauto.
      inv Hr. exists (lr ls1' m1''). split.
      econstructor. constructor.
      intros. apply always_has_mreg_type.
      econstructor; eauto.
Qed.

Lemma cc_collapse :
  cctrans
    ( ro @ c_injp @ 
      c_injp @
      (wt_c @ c_ext) @ c_ext @
      c_injp @
      c_ext @ c_injp @ c_injp @
      (ro @ c_injp) @ (ro @ c_injp) @ (ro @ c_injp) @
      c_injp @                                   (* Unusedglob *)
      (wt_c @ c_ext @ cc_c_locset) @            (* Alloc *)
      locset_ext @                              (* Tunneling *)
      (wt_loc @ cc_stacking_injp) @ (* Stacking *)
      (mach_ext @ cc_mach_asm)
    )
    cc_compcert_1.
Proof.
  unfold cc_compcert_1. unfold cc_c_level.
  etransitivity.
  
  rewrite !cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 c_injp).
  rewrite cctrans_injp_comp.
  
  rewrite (cc_compose_assoc_1 c_injp).
  rewrite (cc_compose_assoc_1 (c_injp @ wt_c)).
  rewrite (cc_compose_assoc_2 c_injp).
  rewrite move_wt_ext.
  
  rewrite !cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 c_ext).
  rewrite  cctrans_ext_comp.

  rewrite (cc_compose_assoc_1 c_injp).
  rewrite (cc_compose_assoc_1 (c_injp @ c_ext)).
  rewrite (cc_compose_assoc_2 c_injp).
  rewrite cctrans_injp_ext.

  rewrite (cc_compose_assoc_1 c_injp).
  rewrite (cc_compose_assoc_1 (c_injp @ c_ext)).
  rewrite (cc_compose_assoc_2 c_injp).
  rewrite cctrans_injp_ext.

  rewrite (cc_compose_assoc_1 c_injp).
  rewrite cctrans_injp_comp.

  rewrite (cc_compose_assoc_1 ro).
  rewrite cctrans_ro_wt_c.

  rewrite cc_compose_assoc_2.
  rewrite !(cc_compose_assoc_1 ro).
  rewrite (cc_compose_assoc_1 (ro @ c_injp)).
  rewrite cctrans_ro_injp_compose.
  rewrite (cc_compose_assoc_1 (ro @ c_injp)).
  rewrite cctrans_ro_injp_compose.
  rewrite (cc_compose_assoc_1 (ro @ c_injp)).
  rewrite cctrans_ro_injp_compose.

  rewrite cc_compose_assoc_2.

  rewrite (cc_compose_assoc_1 c_injp).
  rewrite cctrans_injp_comp.

  rewrite (cc_compose_assoc_1 wt_c).
  rewrite cctrans_wt_c_ro.

  rewrite cc_compose_assoc_2.
  rewrite cctrans_lessdef_c_ext.
  rewrite cc_compose_assoc_2.

  rewrite (cc_compose_assoc_1 wt_c).
  rewrite (cc_compose_assoc_1 (wt_c @ _ )).
  rewrite (cc_compose_assoc_1 ((wt_c @ _ )@_ )).
  rewrite (cc_compose_assoc_2 (wt_c @ _)).
  rewrite (cc_compose_assoc_2 wt_c).
  rewrite cctrans_wt_c_compose.

  rewrite cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 wt_loc).
  rewrite cctrans_wt_loc_stacking.

  rewrite (cc_compose_assoc_1 cc_c_locset).
  rewrite CL_trans_ext.

  rewrite cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 c_ext).
  rewrite cctrans_ext_comp.

  rewrite (cc_compose_assoc_1 c_ext).
  rewrite CL_trans_ext1.

  rewrite cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 c_injp).
  rewrite CL_trans_injp1.

  rewrite cc_compose_assoc_2.
  rewrite (cc_compose_assoc_1 locset_ext).
  rewrite (cc_compose_assoc_1 locset_injp).
  rewrite cctrans_injp_ext_ccstacking.

  

  

  

  (*Q1: how to deal with the c_ext*)
  (*Q2: if we can prove cc_stacking_injp preserving callee_save regs, should we break it into LM? seems
       we can reuse more results? Or the LM trans lemmas cannot be uses because of the one-wayness?*)

  (** If we can prove Tunneling using injp instead of ext, than we can keep cc_stacking injp as it is*)

Abort.
