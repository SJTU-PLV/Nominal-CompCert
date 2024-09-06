Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig VCompBig.
Require Import StackingproofC CallConv.
Import GS.

Section TRANS.

  Context {li1 li2} (cc : LanguageInterface.callconv li1 li2).
  Variable L1 : semantics li1 li1.
  Variable L2 : semantics li2 li2.

  Hypothesis OLDSIM: Smallstep.forward_simulation cc cc L1 L2.

  Lemma NEWSIM: GS.forward_simulation cc L1 L2.
  Proof.
    intros. inv OLDSIM. constructor.
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

End TRANS.
(*    
Program Definition cc_id {li : language_interface} : callconv li li :=
  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.
 *)

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
  intros. generalize (NEWSIM LanguageInterface.cc_id L1 L2).
  intro. apply H0. auto.
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

Require Import Extends.

(** c_ext cannot be defined using cc_unit_world because [cc_c] uses <> diamond constructer for match_reply*)
Program Definition c_ext : callconv li_c li_c := cc_c ext.
(*  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := cc_c_query ext w;
    match_reply w := cc_c_reply ext w;
  |}.
*)
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
    destruct H6 as [r1' [[? [A0 A]][? [B0 B]]]]. inv A. inv B. simpl in *.
    exists tt. split. eauto.
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
    exists (tt,tt). split. reflexivity. split. exists r1. destruct H2 as [? [X H2]]. inv H2. simpl in *.
    split. exists tt. split. eauto.
    econstructor; simpl; eauto. eapply val_inject_id.
    eapply Val.lessdef_refl.
    eapply Mem.extends_refl.
    exists tt. split. eauto.
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
  - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto.
Qed.


(** Big Problem : bring lower cklrs to C level *)

Program Instance lens_injp_locset : Lens (signature * injp_world) injp_world :=
  {
    get := snd;
    set := fun w wp => (fst w, wp);
  }.

Program Instance injp_world_id_l : World (signature * injp_world) :=
    {
      w_state := injp_world;
      w_lens := lens_injp_locset;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.
(* cc_locset *)
Program Definition locset_injp : callconv li_locset li_locset :=
  {|
    ccworld := signature * injp_world;
    ccworld_world := injp_world_id_l;
    match_senv w := CKLR.match_stbls injp (snd w);
    match_query w := cc_locset_query injp (fst w) (snd w);
    match_reply w := cc_locset_reply injp (fst w) (snd w);    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Infix "@" := GS.cc_compose (at level 30, right associativity).

Inductive match12_stacking : injp_world -> (injp_world * unit) -> Prop :=
|match12_stacking_intro : forall f m1 m2 Hm Hm' t,
    match12_stacking (injpw f m1 m2 Hm) ((injpw f m1 m2 Hm'),t).

Lemma Asmtrans : cctrans (cc_stacking_injp) (locset_injp @ cc_locset_mach).
Proof.
  simpl. econstructor. instantiate (1:= match12_stacking).
  - red. intros w2 se1 se2 q1 q2 Hse Hq.
    destruct w2 as [se [[sig wx] [sig' rs]]].
    destruct Hse as [Hse1 Hse2]. simpl in Hse1, Hse2. inv Hse2.
    destruct Hq as [q1' [Hq1 Hq2]]. inv Hq2. simpl in Hq1. inv Hq1.
    inv H9. simpl in H4, Hse1, H8.
    set (rs2 := (make_locset rs lmw_m lmw_sp)).
    inv H5.
    + (*no stack-allocated arguments *)
      red in H.
    exists (stkw injp (injpw f m1 m_ Hm) sig' ls1 lmw_sp m_).
    repeat apply conj; eauto.
    -- econstructor; eauto. admit. (*to de added in LM*)
       intros. apply H8. constructor. constructor; eauto with mem.
       split. intro. extlia. intros. exfalso. admit.
       intros. rewrite H in H0. inv H0. extlia.
    -- simpl. constructor.
    -- intros. inv H0. simpl in H1, H3.
       exists (wp1', tt). simpl. repeat apply conj; eauto.
       simpl.  inv H1. constructor; eauto.
       simpl. inv H2. constructor; eauto.
       inv H3.
       set (ls2' := make_locset rs2' m2' lmw_sp).
       exists (lr ls2' m2'). split.
       constructor; eauto. constructor.
       constructor; eauto.

       red in H8.
       intros. specialize (H8 (R r)) as HH.
       exploit HH. constructor.
       intro VINJ1.
       exploit H16. eauto. intro VINJ2. simpl in VINJ1.
       admit. (** need fix, about callee-save regs *)
       eauto with mem.
       intros. rewrite H in H0. inv H0. extlia.
    +
     assert (Hm' : Mem.inject f m1 lmw_m). admit. simpl in Hse1.
     exists (stkw injp (injpw f m1 lmw_m Hm') sig' ls1 (Vptr sb sofs) lmw_m).
     repeat apply conj; eauto.
     -- inv Hse1. constructor; eauto. erewrite <- Mem.support_free; eauto.
     -- econstructor; eauto. admit. (*to de added in LM*)
       intros. apply H8. constructor. constructor; eauto with mem.
       split. intros. do 2 eexists. split. reflexivity. split.
       eapply Mem.free_range_perm. eauto. eauto.
       intros. exploit H2; eauto. intros [v Hv]. exists v. split. auto.
       exploit H8. eapply loc_external_arg. eauto.
       simpl. setoid_rewrite Hv. simpl. auto.
       intros. red. intros. inv H3.
       intro. exploit Mem.perm_inject. eauto. apply Hm1. eauto.
       replace (ofs - delta + delta) with ofs by lia.
       intros.
       eapply Mem.perm_free_2; eauto. 
    -- simpl. admit. (** match should contain [args_removed] *)
    -- intros. inv H3. simpl in H5, H11.
       exists (wp1', tt). simpl. repeat apply conj; eauto.
       simpl. inv H5. constructor; eauto.
       simpl. inv H11. constructor; eauto.
       inv H3.
       set (ls2' := make_locset rs2' m2' lmw_sp).
       exists (lr ls2' m2'). split.
       constructor; eauto. constructor.
       constructor; eauto.

       red in H8.
       intros. specialize (H8 (R r)) as HH.
       exploit HH. constructor.
       intro VINJ1.
       exploit H16. eauto. intro VINJ2. simpl in VINJ1.
       admit. (** need fix, about callee-save regs *)
       eauto with mem.
       intros. rewrite H in H0. inv H0. extlia.
      intros. inv H0. simpl in H1, H3.
       exists (wp1', tt). simpl. repeat apply conj; eauto.
       simpl.  inv H1. constructor; eauto.
       simpl. inv H2. constructor; eauto.
       inv H3.
       set (ls2' := make_locset rs2' m2' lmw_sp).
       exists (lr ls2' m2'). split.
       constructor; eauto. constructor.
       constructor; eauto.

       red in H8.
       intros. specialize (H8 (R r)) as HH.
       exploit HH. constructor.
       intro VINJ1.
       exploit H16. eauto. intro VINJ2. simpl in VINJ1.
       admit. (** need fix, about callee-save regs *)
       eauto with mem.
       intros. rewrite H in H0. inv H0. extlia.


      admit. (** same but more complicated *)
  - red. intros. simpl in wp1, wp2, w1.
    inv H0. inv H. cbn in H1. inv H2.
    Compute ccworld (locset_injp @ cc_locset_mach).
    exists (se2, (sg, (injpw f m1 m2 Hm), (lmw sg rs2 m2 sp2))).
    repeat apply conj; simpl; eauto.
    + inv H1. constructor; eauto.
    + set (ls2 := make_locset rs2 m2 sp2).
      exists (lq vf2 sg ls2 m2). split.
      constructor; eauto. red. intros; simpl; eauto.
      inv H. eauto. inv H6. admit.
      constructor.
      constructor; eauto. admit.
    + 
        

      

  intros.




(** Idea: first try to compose all C level passes? Clight -> LTL *)

(** Idea: Since we have totally the same incoming and outgoing lemmas. The [inj] is useless? *)
(* inj *)
(*
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

*)

(** 4.1 The self-simulation mechniasm? *)  
(** 4.Modify the proofs of each pass *)
(** 5.Compose the compiler *)

  


(** *)
