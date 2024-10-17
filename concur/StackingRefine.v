Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Linear Mach Locations Conventions.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra InjpAccoComp VCompBig.
Require Import Separation StackingproofC CallConv CallConvLibs.
Import GS.

Local Open Scope sep_scope.

Record cc_stacking_world_injp :=
  stkjw {
    stk_w : injp_world;
    stk_sg : signature;
    stk_ls1 : Locmap.t;
    stk_rs2 : regset;
    stk_sp2 : val;
    stk_m2 : mem;
    }.

Definition stacking_get_injp (ws: cc_stacking_world_injp) := stk_w ws.

Definition stacking_set_injp (ws: cc_stacking_world_injp) (w : injp_world) :=
  match ws with stkjw w' sg ls1 rs2 sp2 m2 => stkjw w sg ls1 rs2 sp2 m2 end.

Program Instance lens_stacking_injp : Lens (cc_stacking_world_injp) injp_world :=
  {
    get := stacking_get_injp;
    set := stacking_set_injp;
  }.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.

Program Instance STKworld : World (cc_stacking_world_injp) :=
  {
    w_state := injp_world;
    w_lens := lens_stacking_injp;
    w_acci := injp_acci;
    w_acce := injp_acce;
    w_acci_trans := injp_acci_preo;
  }.

Inductive pointer_tid (tid : nat) : val -> Prop :=
|pointer_tid_intro b ofs:
  fst b = tid -> pointer_tid tid (Vptr b ofs).
                                          
Inductive cc_stacking_injp_mq: (cc_stacking_world_injp) -> _ -> _ -> Prop :=
| cc_stacking_mq_intro vf1 vf2 sg ls1 m1 sp2 ra2 rs2 m2 f
    (SPL: pointer_tid (Mem.tid (Mem.support m1)) sp2)
    (RA: ra2 <> Vundef)
    (Hm: Mem.inject f m1 m2):
  vf1 <> Vundef -> Val.inject f vf1 vf2 ->
  (forall r, Val.inject f (ls1 (Locations.R r)) (rs2 r)) ->
  m2 |= contains_init_args sg f ls1 m2 sp2 ->
  (forall b ofs, loc_init_args (size_arguments sg) sp2 b ofs ->
            loc_out_of_reach f m1 b ofs) ->
  Val.has_type sp2 Tptr ->
  Val.has_type ra2 Tptr ->
  cc_stacking_injp_mq
    (stkjw (injpw f m1 m2 Hm) sg ls1 rs2 sp2 m2)
    (lq vf1 sg ls1 m1)
    (mq vf2 sp2 ra2 rs2 m2).

Inductive cc_stacking_injp_mr : (cc_stacking_world_injp) -> _ -> _ -> Prop :=
| cc_stacking_mr_intro sg ls1 ls1' m1' sp2 m2 rs2 rs2' m2' f'
    (Hm' : Mem.inject f' m1' m2'):
    (forall r,
      In r (regs_of_rpair (loc_result sg)) ->
      Val.inject f' (ls1' (Locations.R r)) (rs2' r)) ->
    (forall r,
        is_callee_save r = true -> rs2 r = rs2' r) ->
        
      (* Val.inject f' (ls1 (Locations.R r)) (rs2' r)) -> *)
    Mem.unchanged_on (loc_init_args (size_arguments sg) sp2) m2 m2' ->
    (forall b ofs, loc_init_args (size_arguments sg) sp2 b ofs ->
                   loc_out_of_reach f' m1' b ofs) ->
    cc_stacking_injp_mr
      (stkjw (injpw f' m1' m2' Hm') sg ls1 rs2 sp2 m2)
      (lr ls1' m1')
      (mr rs2' m2').

Program Definition cc_stacking_injp : GS.callconv li_locset li_mach := {|
    GS.ccworld := cc_stacking_world_injp;
    GS.ccworld_world := STKworld;
    GS.match_senv w := CKLR.match_stbls injp (stacking_get_injp w);
    GS.match_query := cc_stacking_injp_mq;
    GS.match_reply := cc_stacking_injp_mr
                                                                      |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.

Lemma cctrans_locset_injp_stacking : cctrans (locset_injp @ cc_stacking_injp) cc_stacking_injp.
Proof.
  constructor.
  econstructor. instantiate (1:= match_12_cctrans).
  - red. intros [w sg ls1 rs3 sp3 m3] se1 se2 q1 q2 Hse Hq.
    inv Hse. simpl in H2. inv Hq. inv H3. clear Hm Hm0.
    (* Compute  ccworld (locset_injp @ cc_stacking_injp). *)
    exists (se1, (sg, injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm1), (stkjw(injpw f m1 m2 Hm1) sg ls1 rs3 sp3 m2))).
    repeat apply conj.
    + simpl. split. econstructor; eauto. eapply match_stbls_dom; eauto.
      econstructor; eauto.
    + simpl. exists (lq vf1 sg ls1 m1). split. econstructor; simpl; eauto.
      eapply val_inject_dom; eauto. red. intros.
      inv H2.
      eapply val_inject_dom; eauto. destruct H14 as [A [B C]].
      exploit C; eauto. intros [v' [D E]].
      eapply val_inject_dom; eauto.
      econstructor; eauto.
    + simpl. constructor; eauto. rewrite meminj_dom_compose. reflexivity.
    + simpl. econstructor; eauto. intros. unfold meminj_dom in H3.
      destruct (f b1) as [[? ?]|] eqn: Hf; inv H3. congruence.
      intros. exists b2, ofs2. split. auto. unfold meminj_dom. rewrite H4.
      replace (ofs2 - ofs2) with 0 by lia. reflexivity.
    + simpl. intros r1 r3 wp1 wp2 wp1' Hmatch [Hae1 Hae2] [Hai1 Hai2] Hr.
      simpl in Hae1, Hae2. destruct wp1' as [wp11' wp12'].
      destruct wp1 as [wp11 wp12]. simpl in *.
      destruct wp11' as [j12 m1' m2' Hm1'].
      destruct wp12' as [j23 m2'_ m3' Hm2'].
      destruct Hr as [r' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H3. clear Hm'0 Hm'2 Hm'1.
      clear Hm0 Hm2 Hm3. rename m1'0 into m1'. rename m2'0 into m2'.
      exists (injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm1' Hm2')).
      repeat apply conj; eauto.
      -- eapply injp_comp_acce. 3: apply Hae1. 3: apply Hae2.
         econstructor; eauto.
         econstructor; eauto.
      -- inv Hmatch. eapply injp_comp_acci; eauto. econstructor; eauto.
      -- econstructor; eauto. intros.
         eapply val_inject_compose; eauto.
         intros.  red. intros.
         specialize (H25 _ _ H3). red in H25.
         unfold compose_meminj in H4. repeat destr_in H4.
         intro. exploit H25; eauto.
         replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
         eapply Mem.perm_inject; eauto.
  - red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [x [[sg' w11] [w12 sg ls2 rs3 sp3 m3]]].
    inv HACI. simpl in H1,H2. simpl in wp1, wp2.
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    destruct Hs as [Hs1 Hs2]. inv Hs1. inv Hs2.
    destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2. inv H5. simpl in H4. rename ls0 into ls2.
    rename m1 into m1'. rename m2 into m2'. rename m3 into m3'.
    exists (stkjw (injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23')) sg' ls1 rs3 sp3 m3' ).
    repeat apply conj; eauto.
    + simpl. inv H; simpl in *.
      eapply injp_comp_acci; eauto.
      econstructor; eauto.
      econstructor; eauto.
    + econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + simpl.
      econstructor; simpl; eauto. inv SPL. constructor.
      erewrite inject_tid; eauto.
      eapply val_inject_compose; eauto.
      intros. eapply val_inject_compose; eauto. eapply H4; eauto. constructor.
      destruct H29 as [A [B C]]. split. auto. split. auto. intros.
      exploit C; eauto. intros [v [Hl Hinj]].  exists v.
      split. eauto. eapply val_inject_compose. eapply H4; eauto. constructor. eauto.
      eauto.
      intros.  red. intros.
      specialize (H30 _ _ H5). red in H30.
      unfold compose_meminj in H11. repeat destr_in H11.
      intro. exploit H30; eauto.
      replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
      eapply Mem.perm_inject; eauto.
    + (** The accessbility construction : use acco*)
      intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. simpl in MR.
      destruct wp2' as [j13'' m1'' m3'' Hm13']. inv MR.
      simpl in H3, H4. 
      assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j23' m2' m3' Hm23')).
      destruct wp1 as [w w0]. destruct w, w0.  inv H0.
      exploit external_mid_hidden_acci; eauto. econstructor; eauto.
      exploit injp_acce_outgoing_constr; eauto.
      intros (j12'' & j23'' & m2'' & Hm12'' & Hm23'' & COMPOSE & ACCE1 & ACCE2 & HIDDEN & OUT).
      exists ((injpw j12'' m1'' m2'' Hm12''),(injpw j23'' m2'' m3'' Hm23'')).
      repeat apply conj; eauto.
      -- simpl.
         generalize (loc_result_always_one sg'). intro Hresult.
         destruct Hresult as [r Hresult]. rewrite Hresult in *.
         exploit H22; eauto. simpl. left. reflexivity. intro Hinjresult.
         exploit compose_meminj_midvalue. rewrite COMPOSE in Hinjresult. eauto.
         intros [vres2 [RES1 RES2]]. 
         set (ls2' l := if Loc.eq l (R r) then vres2 else ls1' l).
         exists (lr ls2' m2''). split. econstructor; eauto. simpl.
         red. intros. rewrite Hresult in H5.  inv H5. simpl.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H11.
         constructor.
         econstructor; eauto. intros. rewrite Hresult in H5. inv H5.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H11.
      -- simpl. econstructor; eauto.
Qed.
        
      
