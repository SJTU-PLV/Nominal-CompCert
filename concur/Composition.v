Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig VCompBig.

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
    Unusedglob : injp (currently inj)
    
    ?
    Alloc : wt_c @ ext @ CL
 *)

(**  step1 : injp @ injp @ wt_c @ ext @ ext @ ext @ injp @ id ==========> wt_c @ injp *)

(**  1. injp @ wt_c @ ext @ injp 
     2. wt_c @ injp @ ext @ injp
     3. wt_c @ injp
 *)

(** lemmas about [wt_c] *)

Program Coercion cc_inv {li : language_interface} (I : invariant li) : GS.callconv li li :=
  {|
    GS.ccworld := inv_world I;
    GS.ccworld_world := world_unit;
    GS.match_senv := fun w => rel_inv (symtbl_inv I w);
    GS.match_query := fun w => rel_inv (query_inv I w);
    GS.match_reply := fun w => rel_inv (reply_inv I w)
  |}.
Next Obligation.
  inv H. reflexivity.
Qed.
Next Obligation.
  inv H. auto.
Qed.


Infix "@" := GS.cc_compose (at level 30, right associativity).


Inductive match_wt_1 : (injp_world * (unit * injp_world)) -> (unit * (injp_world * injp_world)) -> Prop :=
|match_wt_1_intro w1 w2 tt:
  match_wt_1 (w1, (tt, w2)) (tt, (w1, w2)).

Lemma move_wt_injp : cctrans (c_injp @ wt_c @ c_injp) (wt_c @ c_injp @ c_injp).
Proof.
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

Lemma cctrans_injp_ext:
  cctrans (c_injp @ c_ext @ c_injp) c_injp.
Proof.
  (** TODO: in 1 step or two steps, not sure yet*)
  Abort.



