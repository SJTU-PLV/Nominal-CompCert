Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Memory.
Require Import Smallstep.
Require Import Inject InjectFootprint.
Require Import CKLRAlgebra.
Require Import Callconv ForwardSim.

(** * Test1: compose injp' ⋅ injp' = injp' *)

(*
L1 <=injp'->injp' L2 ->
L2 <=injp'->injp' L3 ->
L1 <= injp'-> injp' L3
*)

Section COMPOSE_FORWARD_SIMULATIONS.

Context (L1: semantics li_c li_c) (L2: semantics li_c li_c) (L3: semantics li_c li_c).
(*
Definition symtbl_dom (se: Genv.symtbl) : meminj :=
  fun b => if Mem.sup_dec b (Genv.genv_sup se) then Some (b,0)
        else None.
*)
Definition source_inj (se: Genv.symtbl) (f : meminj) :=
  fun b => if Mem.sup_dec b (Genv.genv_sup se) then
        Some (b,0) else meminj_dom f b.

Lemma source_inj_meminj_dom_incr : forall se f,
    inject_incr (meminj_dom f) (source_inj se f).
Proof.
  intros. intro. intros.
  unfold source_inj.
  unfold meminj_dom in *.
  destruct (f b); try discriminate. inv H.
  destruct Mem.sup_dec; eauto.
Qed.

Global Instance source_inj_incr se:
  Monotonic (@source_inj se) (inject_incr ++> inject_incr).
Proof.
  intros f g Hfg b b' delta Hb.
  unfold source_inj in *.
  destruct (Mem.sup_dec). eauto.
  eapply meminj_dom_incr; eauto.
Qed.

Lemma source_inj_compose se f:
  compose_meminj (source_inj se f) f = f.
Proof.
  apply Axioms.functional_extensionality; intros b.
  unfold compose_meminj, source_inj, meminj_dom.
  destruct (Mem.sup_dec).
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  rewrite Hfb.
  replace (0 + ofs) with ofs by extlia.
  reflexivity.
Qed.

Lemma block_inject_dom se f b1 b2:
  block_inject f b1 b2 ->
  block_inject (source_inj se f) b1 b1.
Proof.
  unfold source_inj,meminj_dom.
  intros (delta & Hb).
  exists 0.
  rewrite Hb; eauto.
  destruct Mem.sup_dec; eauto.
Qed.

Lemma val_inject_dom se f v1 v2:
  Val.inject f v1 v2 ->
  Val.inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  - unfold source_inj, meminj_dom.
    rewrite H. destruct Mem.sup_dec; eauto.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Lemma memval_inject_dom se f v1 v2:
  memval_inject f v1 v2 ->
  memval_inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  eapply val_inject_dom; eauto.
Qed.

Lemma val_inject_list_dom se f vs1 vs2:
  Val.inject_list f vs1 vs2 ->
  Val.inject_list (source_inj se f) vs1 vs1.
Proof.
  induction 1; constructor; eauto using val_inject_dom.
Qed.

Lemma global_blocks_pointer:
  forall se m b ofs q n b' ofs',
    Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b (Mem.mem_contents m)) = (Fragment (Vptr b' ofs') q n) ->
    sup_In b (Genv.genv_sup se) ->
    sup_In b' (Genv.genv_sup se).
Proof.
Admitted.

Lemma mem_mem_inj_dom se f m1 m2:
  Mem.mem_inj f m1 m2 ->
  Mem.mem_inj (source_inj se f) m1 m1.
Proof.
  intros H.
  split.
  - unfold source_inj, meminj_dom. intros b1 b2 delta ofs k p Hb1 Hp.
    destruct Mem.sup_dec; destruct (f b1); inv Hb1;
    replace (ofs + 0) with ofs by extlia; auto.
  - unfold source_inj, meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (Mem.sup_dec); destruct (f b1) as [[b1' delta'] | ]; inv Hb1;
    eauto using Z.divide_0_r.
  - unfold source_inj, meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (Mem.sup_dec) ; destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
    replace (ofs + 0) with ofs by extlia.
    {
      set (mv:= (Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m1)))).
      destruct mv eqn:Hmem; constructor.
      destruct v eqn:Hv; econstructor.
      rewrite pred_dec_true. reflexivity.
      eapply global_blocks_pointer; eauto.
      rewrite Ptrofs.add_zero. reflexivity.
    }
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
Qed.

Lemma mem_source_inj se f m1 m2:
  Mem.sup_include (Genv.genv_sup se) (Mem.support m1) ->
  Mem.inject f m1 m2 ->
  Mem.inject (source_inj se f) m1 m1.
Proof.
  intros H.
  split.
  - eapply mem_mem_inj_dom.
    eapply Mem.mi_inj; eauto.
  - unfold source_inj, meminj_dom. intros.
    erewrite Mem.mi_freeblocks; eauto.
    rewrite pred_dec_false; eauto.
    intro. apply H1. apply H. eauto.
  - unfold source_inj, meminj_dom; intros.
    destruct Mem.sup_dec; eauto. inv H1. apply H; eauto.
    destruct (f b) as [[b'' delta'] | ] eqn:Hb; inv H1.
    eapply Mem.valid_block_inject_1; eauto.
  - red. unfold source_inj, meminj_dom. intros.
    destruct Mem.sup_dec; inv H2; eauto.
    destruct Mem.sup_dec; inv H3; eauto.
    destruct (f b2); inv H6; eauto.
    destruct Mem.sup_dec; inv H3; eauto.
    destruct (f b1); inv H7; eauto.                              
    destruct (f b1); inv H7.
    destruct (f b2); inv H6.
    eauto.
  - unfold source_inj, meminj_dom. intros.
    destruct (Mem.sup_dec); eauto. inv H1.
    split; try extlia. rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
    destruct (f b); inv H1.
    split; try extlia.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  - unfold source_inj, meminj_dom. intros.
    destruct Mem.sup_dec; inv H1.
    rewrite Z.add_0_r in H2; eauto.
    destruct (f b1); inv H4.
    rewrite Z.add_0_r in H2; eauto.
Qed.

Lemma match_stbls'_dom f se1 se2:
  Genv.match_stbls' f se1 se2 ->
  Genv.match_stbls' (source_inj se1 f) se1 se1.
Proof.
  intros Hse. unfold source_inj, meminj_dom. split; eauto; intros.
  - rewrite pred_dec_true in H0; eauto. inv H0. reflexivity.
  - eexists. rewrite pred_dec_true; eauto.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
  - destruct (Mem.sup_dec); eauto; inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H1. reflexivity.
Qed.

Lemma loc_unmapped_dom f b ofs:
  loc_unmapped (meminj_dom f) b ofs <->
  loc_unmapped f b ofs.
Proof.
  unfold meminj_dom, loc_unmapped.
  destruct (f b) as [[b' delta] | ].
  - split; discriminate.
  - reflexivity.
Qed.

Definition source_world f m1 m2 (Hm: Mem.inject f m1 m2) (se:Genv.symtbl) (Hse: Mem.sup_include (Genv.genv_sup se) (Mem.support m1)) :=
     injpw (source_inj se f) m1 m1 (mem_source_inj se f m1 m2 Hse Hm).

Lemma match_stbls_dom' f se1 se2:
  Genv.match_stbls' f se1 se2 ->
  Genv.match_stbls (source_inj se1 f) se1 se1.
Proof.
  intros Hse. unfold source_inj. unfold meminj_dom. split; eauto; intros.
  - destruct Mem.sup_dec; try congruence. eauto.
  - inv Hse. exists b2. destruct Mem.sup_dec; try congruence.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct Mem.sup_dec. inv H. reflexivity.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
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
  econstructor; eauto. rewrite add_repr.
  rewrite Ptrofs.add_assoc. auto.
  exists Vundef. split; constructor.
Qed.


Lemma compose_fsim_components_old_new:
  fsim_components (cc_c injp) (cc_c injp) L1 L2 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L2 L3 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L3.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  (*How to construct w1 here? add the well-form condition into fsim_components *)
  set (ff_match_states :=
         fun se1 se3 (w: injp_world) (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2 w12 w23,
             match_states se1 se1 w12 (snd i) s1 s2 /\
             match_states' se1 se3 w23 (fst i) s2 s3 /\
               match_senv (cc_c injp) w12 se1 se1 /\
               match_senv' (cc_c' injp') w23 se1 se3 /\
               forall r1 r2 r3, match_reply (cc_c injp) w12 r1 r2 /\
                             match_reply' (cc_c' injp') w23 r2 r3 ->
                           match_reply' (cc_c' injp') w r1 r3).
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { congruence. }
  intros se1 se2 w Hse2 Hcompat. cbn in *.
  destruct w as [j m1 m2 Hm]. inversion Hse2. subst.
  set (w1 := source_world j m1 m2 Hm se1 H5).
  assert (Hse1: injp_match_stbls w1 se1 se1).
  { constructor; eauto.
    eapply  match_stbls_dom'; eauto.
  }
  assert (Hvalid1: Genv.valid_for (skel L1) se1).
  {
    inv Hcompat. eauto.
  }
  rewrite Hsk in Hcompat.
  (* exploit props; eauto. intros Fsim1.*)
  (* exploit props'; eauto. intros Fsim2. *)
  split.
- (* valid query *)
  intros q1 q3 Hq13.
  assert (match_query (cc_c injp) w1 q1 q1).
  {
    unfold w1. inv Hq13. cbn in *. inv H1. constructor; cbn in *.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    econstructor; eauto. eauto.
  }
  etransitivity.
  eapply fsim_match_valid_query'; eauto.
  eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros q1 q3 s1 Hq13 Hs1.
  assert (match_query (cc_c injp) w1 q1 q1).
  {
    unfold w1. inv Hq13. cbn in *. inv H1. constructor; cbn in *.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    econstructor; eauto. eauto.
  }
  edestruct (@fsim_match_initial_states) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states') as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; eauto.
  intuition eauto.
  admit. (*TODO, compose proof in Injectfootprint and the oracle*)
- (* final states *)
  intros. destruct H as (s3 & w12 & w23 & A & B & C & D & E).
  edestruct (@fsim_match_final_states) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states') as (r3 & Hr3 & Hr23); eauto.
  exists r3. split. eauto. eapply E. split. eapply Hr12. eauto.
- (* external states *)
  intros. destruct H as (s3 & w12 & w23 & A & B & C & D & E).
  edestruct (@fsim_match_external) as (w12A & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external') as (w23A & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  {
    cbn in *. destruct w12A as [j12 m1' m2' Hm12'].
    inv Hq12. cbn in *. inv H3. rename m0 into m1'. rename m3 into m2'.
    destruct w23A as [j23 m2'' m3' Hm23'].
    inv Hq23. cbn in *. inv H13. rename m3 into m3'.
    exists (injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm4 Hm7)).
    exists (cq vf3 sg vargs3 m3').
    repeat apply conj; eauto.
    - (*match_query*)
      econstructor; cbn; eauto. eapply val_inject_compose; eauto.
      eapply val_inject_list_compose; eauto.
    - (*match_stbls'*)
      clear - Hw23 Hw12. cbn in *. inv Hw12. inv Hw23.
      constructor; eauto.
      eapply Genv.match_stbls_stbls'_compose; eauto.
    - (*after_external*)
      cbn.
      intros r1 r3 s1' [w13' [Hw Hr13]] Hafter.
      inv Hr13. inv H7. cbn in *. rename f into j13'. rename Hm11 into INJ13'.
      cbn in Hw. rename m1'0 into m1'A. rename m2'0 into m3'A.
      rename m1' into m1A. rename m2' into m2A. rename m3' into m3A.
      rename Hm4 into INJ12. rename Hm7 into INJ23.
      inversion Hw as [? ? ? ? ? ? ? ? RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
      generalize (inject_implies_image_in _ _ _ INJ12).
      intros IMGIN12.
      generalize (inject_implies_image_in _ _ _ INJ23).
      intros IMGIN23.
      generalize (inject_implies_dom_in _ _ _ INJ12).
      intros DOMIN12.
      generalize (inject_implies_dom_in _ _ _ INJ23).
      intros DOMIN23.
      generalize (inject_implies_dom_in _ _ _ INJ13').
      intros DOMIN13'.
      generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
      intros SUPINCL1.
      generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
      intros SUPINCL3.
      generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
      intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
      subst. cbn in *.
      set (m2'A := m2' m1A m2A m1'A j12 j23 j12' m2'_sup INJ12 ).
      assert (INJ12' :  Mem.inject j12' m1'A m2'A). eapply INJ12'; eauto.
      assert (INJ23' :  Mem.inject j23' m2'A m3'A). eapply INJ23'; eauto.
      set (w12' := injpw j12' m1'A m2'A INJ12').
      set (w23' := injpw j23' m2'A m3'A INJ23').
      rename vres2 into vres3.
      exploit compose_meminj_midvalue; eauto.
      intros [vres2 [RES1 RES2]].
      assert (UNC21:Mem.unchanged_on (loc_out_of_reach j12 m1A) m2A m2'A).
      eapply UNCHANGE21; eauto.
      (* end of injp decomposition *)
      set (r2 := cr vres2 m2'A ).
      edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
      instantiate (1:= r2).
      exists w12'. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. red. unfold compose_meminj.
      rewrite H7. reflexivity.
      constructor; eauto. constructor; eauto.
      edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
      instantiate (1:= (cr vres3 m3'A)). exists w23'.
      split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply UNCHANGE22; eauto. eapply out_of_reach_trans; eauto.
      constructor; eauto. constructor.
      exists (i23', i12'), s3'. split; auto. exists s2', w12, w23; eauto.
  }
- (* simulation *)
  intros. destruct H0 as (s3 & w12 & w23 & MS1 & MS2 & MENV1 & MENV2 & RESULT).
  destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation') as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus') as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3', w12, w23; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3', w12, w23; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3, w12, w23; auto.
Admitted.

(*
Lemma compose_fsim_components':
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L2 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L2 L3 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L3.
Proof.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se3 (w: injp_world) (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se1 (id_world w) (snd i) s1 s2 /\
             match_states' se1 se3 w (fst i) s2 s3).
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { etransitivity; eauto. }
  intros se1 se2 w Hse2 Hcompat. cbn in *.
  assert (Hse1: injp_match_stbls' (id_world w) se1 se1).
  { clear - Hse2.
    inv Hse2. constructor; eauto.
    inv H. constructor; intros; eauto.
    - unfold meminj_dom in H2. destruct (f b1); try discriminate
    
  }
  assert (Hse1: Genv.valid_for (skel L1) se1).
  {}
  { rewrite <- Hsk. eapply match_senv_valid_for; eauto. }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query by eauto.
  eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3; auto.
Qed.
*)
Lemma compose_forward_simulations_old_new:
  forward_simulation (cc_c injp) (cc_c injp) L1 L2 ->
  forward_simulation' (cc_c' injp') (cc_c' injp') L2 L3 ->
  forward_simulation' (cc_c' injp') (cc_c' injp') L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components_old_new; auto.
Qed.

End COMPOSE_FORWARD_SIMULATIONS.
