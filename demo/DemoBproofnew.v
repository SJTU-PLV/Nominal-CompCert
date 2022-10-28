Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler CA.
Require Import CKLRAlgebra Extends Inject InjectFootprint.

Require Import Asmgenproof0 Asmgenproof1.

Section injp_CA.

Section MS.
Variable w: ccworld (cc_c injp @ cc_c_asm).

Definition se := fst (fst w).
Definition injw := snd (fst w).
Definition caw0 := snd (w).
Definition sg := caw_sg caw0.
Definition rs0 := caw_rs caw0.
Definition m2 := caw_m caw0.

Definition sp0 := rs0 RSP.
Definition ra0 := rs0 RA.
Definition vf0 := rs0 PC.
Definition bx0 := rs0 RBX. (*only used callee_save register in this sample*)
(*cc_c_asm_mq*)

Inductive new_blockv (s:sup) : val -> Prop :=
  new_blockv_intro : forall b ofs, ~ sup_In b s -> new_blockv s (Vptr b ofs).

Definition ge := Genv.globalenv se DemoB.prog.

Inductive match_state_c_asm : state -> (sup * Asm.state) -> Prop :=
  |match_ca_callg i m m2' b:
     let sp := rs0 RSP in let ra := rs0 RA in
     sp <> Vundef -> Val.has_type sp Tptr ->
     ra <> Vundef -> Val.has_type ra Tptr ->
     valid_blockv (Mem.support m2) sp ->
     rs0 PC = Vptr b Ptrofs.zero ->
     Genv.find_funct_ptr ge b = Some (Internal func_g) ->
     injp_match_mem injw m m2' ->
     args_removed sg sp0 m2 m2' ->
     rs0 RDI = Vint i ->
     match_state_c_asm (Callstateg i m) ((Mem.support m2),State rs0 m2 true)
  |match_ca_callf w' i m m2' tm (rs: regset) vfc sb:
     let sp := rs RSP in let ra := rs RA in let vf := rs PC in
(*     rs RA = Vptr b Ptrofs.zero (*position after Pcall_s*) ->
     Genv.find_funct_ptr ge b = Some (Internal func_g) -> *)
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RBX = Vint i ->
     rs RDI = Vint (Int.sub i Int.one) ->
     args_removed int_int_sg sp tm m2' ->
     Val.has_type sp Tptr -> Val.has_type ra Tptr ->
     sp = Vptr sb Ptrofs.zero ->
     sup_In sb (Mem.support tm) -> ~ sup_In sb (Mem.support m2) ->
     (forall i, loc_out_of_reach (injp_mi w') m sb i) ->
     vf <> Vundef -> ra <> Vundef -> vfc <> Vundef ->
     Val.inject (injp_mi w') vfc vf ->
     Mem.loadv Mptr tm (Val.offset_ptr sp (Ptrofs.repr 16)) = Some ra0 ->
     Mem.loadv Mptr tm (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     Mem.loadv Many64 tm (Val.offset_ptr sp (Ptrofs.repr 8)) = Some bx0 ->
     (forall r, is_callee_save r = true /\ r <> BX -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     match_state_c_asm (Callstatef vfc i m) ((Mem.support m2),State rs tm true)
  |match_ca_returnf w' m2' i rig m tm (rs: regset):
     let sp := rs RSP in
(*     rs PC = Vptr b Ptrofs.zero (*position after Pcall_s*) ->
     Genv.find_funct_ptr ge b = Some (Internal func_g) -> *)
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RBX = Vint i -> rs RAX = Vint rig ->
     Mem.unchanged_on (fun b ofs => True) m2' tm ->
     Mem.support m2' = Mem.support tm ->
     Mem.loadv Mptr tm (Val.offset_ptr sp (Ptrofs.repr 16)) = Some ra0 ->
     Mem.loadv Mptr tm (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     Mem.loadv Many64 tm (Val.offset_ptr sp (Ptrofs.repr 8)) = Some bx0 ->
     (forall r, is_callee_save r = true /\ r <> BX -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     match_state_c_asm (Returnstatef i rig m) ((Mem.support m2), State rs tm true)
  |match_ca_returng w' m2' m tm (rs: regset) ri:
(*     rs PC = Vptr b Ptrofs.??? (*position after Pfreeframe*) ->
     Genv.find_funct_ptr ge b = Some (Internal func_g) -> *)
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RAX = Vint ri ->
     Mem.unchanged_on (fun b ofs => True) m2' tm ->
     Mem.support m2' = Mem.support tm ->
     rs RSP = rs0 RSP -> rs PC = rs0 RA ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     (*cc_c_asm_mr*)
     match_state_c_asm (Returnstateg ri m) ((Mem.support m2), State rs tm false).
End MS.

Axiom not_win: Archi.win64 = false.
Lemma size_int_int_sg_0:
  size_arguments int_int_sg = 0.
Proof.
  unfold size_arguments, int_int_sg, loc_arguments. replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int :
  loc_arguments int_int_sg = One (R DI)::nil.
Proof.
  unfold loc_arguments.
  replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_int_sg = One AX.
Proof.
  unfold loc_result.
  replace Archi.ptr64 with true by reflexivity.
  reflexivity.
Qed.

Lemma match_program_id :
  match_program (fun _ f0 tf => tf = id f0) eq prog prog.
Proof.
  red. red. constructor; eauto.
    constructor. constructor. eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor. constructor; eauto. constructor; eauto.
    constructor; eauto.
    constructor; eauto. constructor; eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor.
Qed.

Lemma loadv_unchanged_on : forall P m m' chunk b ptrofs v,
    Mem.unchanged_on P m m' ->
    (forall i, let ofs := Ptrofs.unsigned ptrofs in
    ofs <= i < ofs + size_chunk chunk -> P b i) ->
    Mem.loadv chunk m (Vptr b ptrofs) = Some v ->
    Mem.loadv chunk m' (Vptr b ptrofs) = Some v.
Proof.
  intros. unfold Mem.loadv in *. cbn in *.
  eapply Mem.load_unchanged_on; eauto.
Qed.

Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.

Ltac rlia := rewrite maxv; lia.
Ltac Plia := try rewrite !Ptrofs.unsigned_zero; try rewrite!Ptrofs.unsigned_repr; try rlia.
Ltac Ap64 := replace Archi.ptr64 with true by reflexivity.
Ltac Ap64' H0 := replace Archi.ptr64 with true in H0 by reflexivity.

Lemma load_result_Mptr_eq:
    forall v, v <> Vundef -> Val.has_type v Tptr ->
         Val.load_result Mptr v = v.
Proof.
  intros. unfold Mptr. Ap64. cbn.
  unfold Tptr in H0. Ap64' H0.
  destruct v; cbn in *; eauto; try congruence; eauto.
  inv H0. inv H0. inv H0.
Qed.

Lemma enter_fung_exec:
  forall m (rs0: regset),
      (rs0 RSP) <> Vundef -> Val.has_type (rs0 RSP) Tptr ->
      (rs0 RA) <> Vundef -> Val.has_type (rs0 RA) Tptr ->
      exists m1 m2 m3 m4 m5 sp,
    Mem.alloc m 0 24 = (m1,sp)
    /\ Mem.store Mptr m1 sp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2
    /\ Mem.store Mptr m2 sp (Ptrofs.unsigned (Ptrofs.repr 16)) (rs0 RA) = Some m3
    /\ Mem.storev Many64 m3 (Vptr sp (Ptrofs.repr 8)) (rs0 RBX) = Some m4
    /\ Mem.load Many64 m4 sp (Ptrofs.unsigned (Ptrofs.repr 8)) = Some (rs0 RBX)
    /\ Mem.load Mptr m4 sp (Ptrofs.unsigned (Ptrofs.repr 16)) = Some (rs0 RA)
    /\ Mem.load Mptr m4 sp (Ptrofs.unsigned (Ptrofs.zero)) = Some (rs0 RSP)
    /\ Mem.free m4 sp 0 24 = Some m5
    /\ Mem.unchanged_on (fun _ _ => True) m m5.
Proof.
  intros m rs0 RSP1 RSP2 RA1 RA2.
  destruct (Mem.alloc m 0 24) as [m1 sp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  assert (STORE: {m2| Mem.store Mptr m1 sp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H. simpl in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_zero.
  red. exists  0. lia. destruct STORE as [m2 STORE1].
  assert (STORE: {m3| Mem.store Mptr m2 sp (Ptrofs.unsigned (Ptrofs.repr 16)) (rs0 RA) = Some m3}).
  apply Mem.valid_access_store.
  red. split. red. intros.
  rewrite Ptrofs.unsigned_repr in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem. rlia.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_repr.
  exists 2. lia. rlia.
  destruct STORE as [m3 STORE2].
  assert (STORE: {m4| Mem.storev Many64 m3 (Vptr sp (Ptrofs.repr 8)) (rs0 RBX) = Some m4}).
  apply Mem.valid_access_store.
  red. split. red. intros.
  rewrite Ptrofs.unsigned_repr in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem. rlia.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_repr.
  exists 2. lia. rlia.
  destruct STORE as [m4 STORE3].
  cbn in STORE3. apply Mem.load_store_same in STORE3 as LOAD1.
  apply Mem.load_store_same in STORE2 as LOAD2.
  erewrite <- Mem.load_store_other in LOAD2; eauto.
  apply Mem.load_store_same in STORE1 as LOAD3.
  erewrite <- Mem.load_store_other in LOAD3; eauto.
  erewrite <- Mem.load_store_other in LOAD3; eauto.
  cbn in *. rewrite load_result_Mptr_eq in LOAD2; eauto.
  rewrite load_result_Mptr_eq in LOAD3; eauto.
  assert (FREE: {m5|  Mem.free m4 sp 0 24 = Some m5}).
  apply Mem.range_perm_free.
  red. intros. eauto with mem. destruct FREE as [m5 FREE].
  assert (UNC1 : Mem.unchanged_on (fun _ _ => True) m m1).
  eapply Mem.alloc_unchanged_on; eauto.
  assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp) m1 m5).
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on; eauto.
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on; eauto.
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on; eauto.
  eapply Mem.free_unchanged_on; eauto.
  apply Mem.fresh_block_alloc in ALLOC as FRESH.
  exists m1,m2,m3,m4,m5,sp. intuition eauto.
  - inv UNC1. inv UNC2. constructor.
    + eauto with mem.
    + intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst. congruence. eauto with mem.
    + intros. etransitivity. apply unchanged_on_contents0.
      intros. subst. apply Mem.perm_valid_block in H0. congruence. eauto with mem.
      eauto.
  - right. left. unfold Mptr. Ap64. cbn. Plia. lia.
  - right. left. unfold Mptr. Ap64. cbn. Plia. lia.
  - right. right. cbn. Plia. lia.
Qed.

Lemma undef_regs_pc :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs PC = rs PC.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq PC r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rdi :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RDI = rs RDI.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RDI r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rsp :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RSP = rs RSP.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RSP r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Ltac Pgso := rewrite Pregmap.gso; try congruence.
Ltac Pgss := rewrite Pregmap.gss.

Lemma injp_CA_simulation: forward_simulation
                 (cc_c injp @ cc_c_asm)
                 (cc_c injp @ cc_c_asm)
                 Bspec (Asm.semantics prog).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_c_asm w s1 s2 /\
                         caw_sg (snd w) = int_int_sg).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as [[se [f ? ? Hm]] [sg rs0 m2'0]]; destruct Hse; subst; cbn in *; eauto.
  -  (*valid_query*)
    intros. destruct H0 as [qm [Hq1 Hq2]]. inv Hq1. inv Hq2.
    simpl. cbn in *. subst vf.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto. inv H; eauto.
  - (* initial *)
    intros q1 q3 s1 [q2 [Hq1 Hq2]] Hi1. inv Hi1.
    inv Hq1. inv Hq2. cbn in *. inv H7.
    exists (Mem.support m2'0, State rs0 m2'0 true).
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    2: inv H; eauto.
    repeat apply conj.
    + econstructor; eauto.
      inv H17. subst sp. congruence.
    + eauto.
    + subst vf. unfold Genv.find_funct in TRAN.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      subst.
      econstructor; cbn; eauto. inv H17. subst sp. congruence.
      rewrite loc_arguments_int in H6. simpl in H6. inv H6. inv H3. reflexivity.
    + eauto.
  - (* final_state *)
    intros s1 s3 r1 Hms Hf1. inv Hf1. inv Hms. inv H0. cbn in *.
    exists (rs,tm). split. constructor.
    exists (cr (Vint s) m2'). split.
    exists w'. split. eauto. constructor; eauto.
    constructor; eauto. eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. auto.
    constructor. eauto with mem.
    intros. inv H0. rewrite size_int_int_sg_0 in H11. extlia.
    intros. inv H0. rewrite size_int_int_sg_0 in H11. extlia.
    intros. inv H0. rewrite size_int_int_sg_0 in H2. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. inv EXT1. inv MS.
    inv H0. cbn in *. inv H4. inv H5. cbn in *.
    inv H. eapply Genv.match_stbls_incr in H4; eauto.
    2:{
      intros. exploit H29; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    exists ((se2,(injpw f' m m2' Hm4)),(caw int_int_sg rs tm)).
    exists (rs,tm). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + exists (cq vf1 int_int_sg (Vint (Int.sub aif Int.one)::nil) m2').
      split.
      -- constructor; eauto. simpl. constructor.
      -- econstructor; eauto.
         rewrite loc_arguments_int. simpl. congruence.
         subst sp. rewrite H11. constructor; eauto.
    + constructor. apply H4.
      inversion H25. eauto with mem.
      inversion H26. eauto with mem.
    + reflexivity.
    + (*after_external*)
      intros r1 r3 s1' [r2 [Hr1 Hr2]] Haf1.
      destruct Hr1 as [w [Hw Hr1]]. inv Haf1. inv Hr1. inv Hr2.
      cbn in *.
      exists ((Mem.support m2'0), (State rs' tm' true)). repeat apply conj.
      -- constructor. inversion H36; eauto.
         unfold inner_sp. rewrite H40. subst sp. rewrite H11.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- econstructor; cbn.
         ++ etransitivity; eauto. constructor; eauto.
         ++ eauto.
         ++ generalize (H34 BX). intro. exploit H; eauto.
            simpl. intro A. rewrite A. eauto.
         ++ rewrite loc_result_int in H1. simpl in H1.
            inv H1. reflexivity.
         ++ eapply Mem.unchanged_on_implies; eauto.
            intros. red. intro. inv H2. rewrite size_int_int_sg_0 in H32. extlia.
         ++ eauto.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ intros. rewrite H34. rewrite H23. eauto. eauto. apply H.
         ++ inversion H36. eauto with mem.
      -- reflexivity.
  - (*internal_steps*)
    intros. inv H0; inv H1; inv H0;cbn in *.
    ++ inv H10. (*step_zero*)
      subst sp ra.
      destruct (enter_fung_exec m2'0 rs0) as (m2'1 & m2'2 & m2'3 & m2'4 & m2'5 & sp &
                                              ALLOC & STORE1 & STORE2 & STORE3
                                             & LOAD1 & LOAD2 & LOAD3 & FREE & UNC); eauto.
      inv H7.
      assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2'0)) (Genv.globalenv se2 prog) (State rs0 m2'0 true) E0 s2'
             /\ ms (Returnstateg Int.zero m) (Mem.support m2'0, s2')).
      { 
        (*execution of Asm code*)
        eexists. split.
        - (*plus steps*)
          econstructor.
      (*Pallocframe*)
      econstructor; eauto. unfold fn_code. cbn. rewrite Ptrofs.unsigned_zero. simpl.
      reflexivity. simpl. rewrite ALLOC. rewrite Ptrofs.add_zero. rewrite STORE1.
      rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
      rewrite !Pregmap.gso; try congruence. rewrite H8. simpl. rewrite Ptrofs.add_zero_l.
      reflexivity.
      (*save RBX*)
      eapply star_step; eauto.
      econstructor; eauto. Simplif.
      cbn. rewrite Ptrofs.unsigned_one. cbn. reflexivity.
      simpl. replace Archi.ptr64 with true by reflexivity.
      simpl. unfold exec_store. cbn. unfold eval_addrmode. replace Archi.ptr64 with true by reflexivity.
      cbn. replace Archi.ptr64 with true by reflexivity.
      rewrite Ptrofs.add_zero_l. rewrite Int64.add_zero_l.
      unfold Ptrofs.of_int64.
      rewrite Int64.unsigned_repr.
      rewrite STORE3. unfold nextinstr_nf. unfold nextinstr.
      rewrite undef_regs_pc.
      rewrite Pregmap.gss.
      Local Opaque undef_regs. simpl.
      rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one. simpl.
      reflexivity. unfold Int64.max_unsigned. simpl. lia.
      (* move i from DI to BX*)
      eapply star_step; eauto.
      econstructor; eauto. Simplifs.
      cbn.
      rewrite Ptrofs.unsigned_repr; try rlia. cbn. reflexivity.
      simpl. rewrite !Pregmap.gso; try congruence.
      rewrite undef_regs_rdi. rewrite !Pregmap.gso; try congruence.
      unfold nextinstr. rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss.
      simpl. rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one.
      rewrite Ptrofs.unsigned_repr. simpl. reflexivity. rlia.
      (* compare i = 0 ?*)
      eapply star_step; eauto. econstructor; eauto. Simplifs.
      cbn. rewrite Ptrofs.unsigned_repr; try rlia. cbn. reflexivity.
      simpl. Pgso. Pgss. rewrite H13. simpl.
      rewrite Int.and_idem. unfold Vzero.
      unfold compare_ints. unfold nextinstr.
      Pgso. Pgso. Pgso. Pgso. Pgso. Pgss. cbn. rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_one. rewrite Ptrofs.unsigned_repr; try rlia.
      cbn.
      reflexivity.
      (* test *)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      cbn. rewrite Ptrofs.unsigned_repr; try rlia. cbn. reflexivity.
      simpl. Pgso. Pgso. Pgso. Pgso. Pgso. Pgss.
      assert (Int.eq i Int.zero = true).
      unfold Int.eq. unfold zeq. rewrite Int.unsigned_zero.
      unfold Int.unsigned. rewrite ZERO. cbn. reflexivity.
      rewrite H2. simpl.
      assert (FF: Int.eq Int.one Int.zero = false).
      unfold Int.eq. rewrite Int.unsigned_one. rewrite Int.unsigned_zero.
      cbn. reflexivity.
      rewrite FF.
      unfold nextinstr. Pgss. cbn.
      Ltac compute_pc := rewrite Ptrofs.add_unsigned;
      rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
      compute_pc. reflexivity.
      (* set RAX *)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      Ltac find_instr := cbn; rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
      find_instr.
      simpl.
      unfold nextinstr_nf, nextinstr. rewrite undef_regs_pc.
      Pgso. cbn. compute_pc. reflexivity.
      (* jmp *)
      eapply star_step. econstructor; eauto. Simplif.
      find_instr. simpl. unfold goto_label. cbn. unfold lb0,lb1, lb2.
      rewrite pred_dec_false; try congruence.
      rewrite pred_dec_false; try congruence.
      rewrite pred_dec_true; try congruence.
      reflexivity.
      (* restore BX *)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. replace Archi.ptr64 with true by reflexivity.
      unfold exec_load. unfold eval_addrmode.
      Ap64. cbn. rewrite undef_regs_rsp. do 11 Pgso.
      rewrite undef_regs_rsp. Pgso. Pgss. rewrite Int64.add_zero_l.
      cbn. Ap64. cbn. rewrite Ptrofs.add_zero_l. unfold Ptrofs.of_int64.
      rewrite Int64.unsigned_repr.
      rewrite LOAD1.
      unfold nextinstr_nf, nextinstr. rewrite undef_regs_pc. Pgso.
      Pgss. cbn. compute_pc. reflexivity. cbn. lia.
      (* Pfreeframe *)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. cbn. unfold Mem.loadv. rewrite undef_regs_rsp.
      do 3 Pgso. rewrite undef_regs_rsp. do 11 Pgso. rewrite undef_regs_rsp.
      Pgso. Pgss. cbn. rewrite Ptrofs.add_zero_l.
      rewrite LOAD2. rewrite Ptrofs.add_zero_l.
      rewrite LOAD3. Plia. cbn. rewrite FREE.
      unfold nextinstr. cbn. compute_pc.
      reflexivity.
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. cbn. unfold inner_sp. rewrite <- H0.
      rewrite pred_dec_true; eauto.
      apply star_refl. traceEq. traceEq.
      - constructor; eauto. cbn in *.
        inv H11. 2:{ rewrite size_int_int_sg_0 in H12. extlia. }
        apply Mem.fresh_block_alloc in ALLOC as FRESH.
        exploit Mem.alloc_right_inject; eauto. intro INJ1.
        exploit Mem.store_outside_inject; eauto.
        intros. inversion Hm1. eauto. intro INJ2.
        exploit Mem.store_outside_inject; eauto.
        intros. inversion Hm1. eauto. intro INJ3.
        exploit Mem.store_outside_inject; eauto.
        intros. inversion Hm1. eauto. intro INJ4.
        exploit Mem.free_right_inject; eauto.
        intros. inversion Hm1. eauto. intro INJ5.
        econstructor. instantiate (1:= injpw f m m2'5 INJ5). all: eauto.
        + constructor; eauto. 
          -- red. intros. inversion UNC. eapply unchanged_on_perm; eauto.
          -- eauto with mem.
          -- eapply Mem.unchanged_on_implies; eauto.
             intros. cbn. eauto.
          -- red. intros. congruence.
        + eauto with mem.
        + intros.
          cbn. repeat try Pgso; destruct r; cbn in *; try congruence; eauto.
        + cbn. inversion UNC. eauto.
      }
      destruct H2 as [s2' [STEP MS]].
      exists (Mem.support m2'0, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2'0), (Genv.globalenv se1 prog); clear; intros.
      pattern (State rs0 m2'0 true),E0,s2'. eapply plus_ind2; eauto; intros.
      * apply plus_one; eauto.
      * eapply plus_trans; eauto.
        apply plus_one. auto.
    ++
      (*step_read*)
      admit.
    ++ (*step_call*)
      admit.
    ++ (*step_return*)
      admit.
  - constructor. intros. inv H.
Admitted.


End injp_CA.
(*
Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply injp_protection.
  eapply compose_forward_simulations.
  eapply self_wt.
  rewrite <- !(cc_compose_assoc) at 1.
  eapply compose_forward_simulations.
  rewrite cc_compose_assoc at 1.
  rewrite cc_compose_assoc at 1.
  rewrite <- cc_ca_cllmma at 1.
  rewrite cc_cllmma_ca.
  eapply CA.
  eapply semantics_asm_rel; eauto.
Qed.
*)
