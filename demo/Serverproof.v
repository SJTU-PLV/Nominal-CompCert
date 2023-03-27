Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import Server Serverspec.

Require Import CallConv Compiler CA.
Require Import CKLRAlgebra Extends Inject InjectFootprint.

Require Import Asmgenproof0 Asmgenproof1.

Section CAinjp_b1.

Section MS.

Variable w: ccworld (cc_c_asm_injp).
Variable se tse: Genv.symtbl.
Let ge := Genv.globalenv se b1.
Let tge := Genv.globalenv tse b1.

Let wp := cajw_injp w.
Let sg := cajw_sg w.
Let rs0 := cajw_rs w.
Let m2 := match wp with injpw _ _ m2 _ => m2 end.
Let s2 := Mem.support m2.
Hypothesis GE: match_stbls injp wp se tse.
Let sp0 := rs0 RSP.
Let ra0 := rs0 RA.
Let vf0 := rs0 PC.
Let bx0 := rs0 RBX. (*only used callee_save register in this sample*)

Inductive new_blockv (s:sup) : val -> Prop :=
  new_blockv_intro : forall b ofs, ~ sup_In b s -> new_blockv s (Vptr b ofs).

Inductive match_state_c_asm : state -> (sup * Asm.state) -> Prop :=
|match_call1 m1 b b' ofs eb input j Hm delta:
  wp = injpw j m1 m2 Hm ->
  sp0 <> Vundef -> ra0 <> Vundef ->
  Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
  valid_blockv (Mem.support m2) sp0 ->
  vf0 = Vptr eb Ptrofs.zero ->
  Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
  j b = Some (b', delta) ->
  rs0 RDI = Vint input ->
  rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
  match_state_c_asm (Call1 (Vptr b ofs) input m1) (s2, State rs0 m2 true)
|match_call2 m1 b ofs j Hm (rs:regset) m1' m2' Hm' output sb b' delta eb:
    let sp := rs RSP in let ra := rs RA in let vf := rs PC in
    sp = Vptr sb Ptrofs.zero ->
    wp = injpw j m1 m2 Hm ->
    (forall ofs, loc_out_of_reach j m1 sb ofs) ->
    Mem.range_perm m2' sb 0 16 Cur Freeable ->
    injp_acc wp (injpw j m1' m2' Hm') ->
    rs PC = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
    j b = Some (b', delta) -> rs RDI = Vint output ->
    ra = Vptr eb (Ptrofs.repr 4) ->
    Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
    sup_In sb (Mem.support m2') -> ~ sup_In sb s2 ->
    (forall b d, j b = Some (sb,d) -> False) ->
    vf <> Vundef ->
    Mem.loadv Mptr m2' (Val.offset_ptr sp (Ptrofs.repr 8)) = Some ra0 ->
    Mem.loadv Mptr m2' (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
    valid_blockv s2 sp0 ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include s2 (Mem.support m2')  ->
     match_state_c_asm (Call2 (Vptr b ofs) output m1') (s2, State rs m2' true)
|match_return1 j j' m1 m1'' m2'' Hm Hm'' (rs:regset) eb sb:
    let sp := rs RSP in
    sp = Vptr sb Ptrofs.zero ->
     wp = injpw j m1 m2 Hm ->
     (forall ofs, loc_out_of_reach j m1 sb ofs) ->
     Mem.range_perm m2'' sb 0 16 Cur Freeable ->
     injp_acc wp (injpw j' m1'' m2'' Hm'') ->
     rs PC = Vptr eb (Ptrofs.repr 4) ->
     Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
     (forall b d, j' b = Some (sb,d) -> False) ->
     Mem.loadv Mptr m2'' (Val.offset_ptr sp (Ptrofs.repr 8)) = Some ra0 ->
     Mem.loadv Mptr m2'' (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     ~ sup_In sb s2 ->
     valid_blockv (Mem.support m2) sp0 ->
     (forall r, is_callee_save r = true  -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support m2'') ->
     match_state_c_asm (Return1 m1'') (s2, State rs m2'' true)
|match_return2 j' m2'' m1'' (rs:regset) Hm'':
  (injp_acc wp (injpw j' m1'' m2'' Hm'')) ->
   rs RSP = rs0 RSP -> rs PC = rs0 RA ->
   (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
   Mem.sup_include s2 (Mem.support m2'') ->
   match_state_c_asm (Return2 m1'') (s2, State rs m2'' false).

End MS.

Axiom not_win: Archi.win64 = false.

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
Ltac Ap64_in H0 := replace Archi.ptr64 with true in H0 by reflexivity.

Lemma size_int__void_sg_0:
  size_arguments int__void_sg = 0.
Proof.
  unfold size_arguments, int__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma size_int_fptr__void_sg_0:
  size_arguments int_fptr__void_sg = 0.
Proof.
  unfold size_arguments, int_fptr__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int_fptr :
  loc_arguments int_fptr__void_sg = One (R DI):: One (R SI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_arguments_int :
  loc_arguments int__void_sg = One (R DI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_fptr__void_sg = One AX.
Proof.
  unfold loc_result. Ap64. reflexivity.
Qed.

Lemma match_program_id :
  match_program (fun _ f0 tf => tf = id f0) eq b1 b1.
Proof.
  red. red. constructor; eauto.
  constructor. constructor. eauto. simpl. econstructor; eauto.
  constructor. eauto.
  constructor; cbn; eauto. constructor; eauto.
  econstructor.
  apply linkorder_refl.
  constructor. constructor; eauto.
  constructor. eauto. econstructor.
  apply linkorder_refl. eauto.
  constructor; eauto.
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

Lemma load_result_Mptr_eq:
    forall v, v <> Vundef -> Val.has_type v Tptr ->
         Val.load_result Mptr v = v.
Proof.
  intros. unfold Mptr. Ap64. cbn.
  unfold Tptr in H0. Ap64_in H0.
  destruct v; cbn in *; eauto; try congruence; eauto.
  inv H0. inv H0. inv H0.
Qed.

Lemma enter_fung_exec:
  forall m (rs0: regset),
      (rs0 RSP) <> Vundef -> Val.has_type (rs0 RSP) Tptr ->
      (rs0 RA) <> Vundef -> Val.has_type (rs0 RA) Tptr ->
      exists m1 m2 m3 m4 sp,
    Mem.alloc m 0 16 = (m1,sp)
    /\ Mem.store Mptr m1 sp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2
    /\ Mem.store Mptr m2 sp (Ptrofs.unsigned (Ptrofs.repr 8)) (rs0 RA) = Some m3
    /\ Mem.load Mptr m3 sp (Ptrofs.unsigned (Ptrofs.repr 8)) = Some (rs0 RA)
    /\ Mem.load Mptr m3 sp (Ptrofs.unsigned (Ptrofs.zero)) = Some (rs0 RSP)
    /\ Mem.free m3 sp 0 16 = Some m4
    /\ Mem.unchanged_on (fun _ _ => True) m m3
    /\ Mem.unchanged_on (fun _ _ => True) m m4.
Proof.
  intros m rs0 RSP1 RSP2 RA1 RA2.
  destruct (Mem.alloc m 0 16) as [m1 sp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  assert (STORE: {m2| Mem.store Mptr m1 sp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H. simpl in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_zero.
  red. exists  0. lia. destruct STORE as [m2 STORE1].
  assert (STORE: {m3| Mem.store Mptr m2 sp (Ptrofs.unsigned (Ptrofs.repr 8)) (rs0 RA) = Some m3}).
  apply Mem.valid_access_store.
  red. split. red. intros.
  rewrite Ptrofs.unsigned_repr in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem. rlia.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_repr.
  exists 1. lia. rlia.
  destruct STORE as [m3 STORE2].
  apply Mem.load_store_same in STORE1 as LOAD1.
  apply Mem.load_store_same in STORE2 as LOAD2.
  erewrite <- Mem.load_store_other in LOAD1; eauto.
  cbn in *. rewrite load_result_Mptr_eq in LOAD2; eauto.
  rewrite load_result_Mptr_eq in LOAD1; eauto.
  2:{ right. left. unfold Mptr. Ap64. cbn. Plia. lia. }
  assert (FREE: {m4|  Mem.free m3 sp 0 16 = Some m4}).
  apply Mem.range_perm_free.
  red. intros. eauto with mem. destruct FREE as [m4 FREE].
  assert (UNC1 : Mem.unchanged_on (fun _ _ => True) m m1).
  eapply Mem.alloc_unchanged_on; eauto.
  assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp) m1 m3).
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on; eauto.
  eapply Mem.store_unchanged_on; eauto.
  assert (UNC3: Mem.unchanged_on (fun b ofs => b <> sp) m1 m4).
  eapply Mem.unchanged_on_trans; eauto.
  eapply Mem.free_unchanged_on; eauto.
  apply Mem.fresh_block_alloc in ALLOC as FRESH.
  exists m1,m2,m3,m4,sp. intuition eauto.
  - inv UNC1. inv UNC2. constructor.
    + eauto with mem.
    + intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst. congruence. eauto with mem.
    + intros. etransitivity. apply unchanged_on_contents0.
      intros. subst. apply Mem.perm_valid_block in H0. congruence. eauto with mem.
      eauto.
  - inv UNC1. inv UNC3. constructor.
    + eauto with mem.
    + intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst. congruence. eauto with mem.
    + intros. etransitivity. apply unchanged_on_contents0.
      intros. subst. apply Mem.perm_valid_block in H0. congruence. eauto with mem.
      eauto.
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

Lemma undef_regs_rsi :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RSI = rs RSI.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RSI r'). subst.
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

Lemma undef_regs_rax :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RAX = rs RAX.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RAX r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rbx :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RBX = rs RBX.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RBX r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_callee_save :
  forall (rs:regset) r,
    is_callee_save r = true ->
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs (preg_of r) = rs (preg_of r).
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  destruct r; cbn in *; try congruence;
    intros; destruct H0 as [A|[B|[C|[D|[E|F]]]]]; subst; try congruence.
Qed.

Lemma undef_regs_nil :
  forall rs,
    undef_regs nil rs = rs.
Proof.
  intros. reflexivity. Qed.

Ltac Pgso := rewrite Pregmap.gso; try congruence.
Ltac Pgss := rewrite Pregmap.gss.

(*we can proof d = 0 by the representable property of f in a Mem.inject,
 but this is strong enough here *)
Lemma symbol_address_inject : forall ge tge f b ofs id,
    Genv.match_stbls f ge tge ->
    Genv.symbol_address ge id  ofs = Vptr b ofs ->
    exists b' d, f b = Some (b',d) /\
            Ptrofs.add ofs (Ptrofs.repr d) = ofs /\
          Genv.symbol_address tge id ofs = Vptr b' ofs.
Proof.
  intros.
  eapply Op.symbol_address_inject in H as H1. rewrite H0 in H1.
  inv H1. unfold Genv.symbol_address in H4.
  destruct Genv.find_symbol; try congruence.
  inv H4.
  exists b0, delta. intuition eauto.
  rewrite !H3. eauto.
  rewrite !H3. eauto.
Qed.

Lemma CAinjp_simulation_L1: forward_simulation
                 (cc_c_asm_injp)
                 (cc_c_asm_injp)
                 L1 (Asm.semantics b1).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_c_asm w se2 s1 s2 /\
                          cajw_sg w = int_fptr__void_sg).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as [[f ? ? Hm] sg rs0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  -  (*valid_query*)
    intros. inv H.
    simpl. cbn in *.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros q1 q2 s1 Hq Hi1. inv Hi1.
    inv Hq.
    inv H18. 2:{ rewrite size_int_fptr__void_sg_0 in H3. extlia. }
    rename tm0 into m2. rename m into m1.
    exists (Mem.support m2, State rs0 m2 true).
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    repeat apply conj.
    + econstructor; eauto. inv H17.
      subst tsp0. congruence.
    + eauto.
    + subst tvf. unfold Genv.find_funct in TRAN.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      subst targs. rewrite loc_arguments_int_fptr in H11. simpl in H11. inv H11. inv H8.
      inv H4. inv H7.
      econstructor; cbn; eauto.
      inv H17. subst tsp0. congruence.
    + eauto.
  - (* final_state *)
    intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms. inv H. cbn in *.
    exists (rs, m2''). split. constructor.
    econstructor; eauto.
    intros. inv H. rewrite size_int_fptr__void_sg_0 in H9. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. cbn. inv EXT1. inv MS.
    inv H. cbn in *. inv H11. cbn in *.
    symmetry in H8. inv H8.
    eapply Genv.match_stbls_incr in H2; eauto.
    2:{
      intros. exploit H34; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    exists (cajw (injpw f m m2' Hm'1) int__void_sg rs).
    exists (rs,m2'). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      rewrite H12.
      assert (Val.inject f (Vptr b ofs) (Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)))).
      econstructor; eauto.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + rename m into m'. rename m1 into m. rename m2 into tm. rename m2' into tm'.
      econstructor; eauto.
      -- rewrite loc_arguments_int. cbn. rewrite H14.
         constructor; eauto.
      -- rewrite H12. econstructor; eauto.
      -- intros. rewrite size_int__void_sg_0 in H.
         subst sp. rewrite H7 in H. inv H. extlia.
      -- subst sp. rewrite H7. constructor.
      -- subst ra. rewrite H15. constructor.
      -- subst sp. rewrite H7. constructor. eauto.
      -- eapply args_removed_tailcall_possible.
         red. apply size_int__void_sg_0.
      -- congruence.
      -- subst ra. rewrite H15. congruence.
    + constructor; eauto.
      inversion H31. eauto with mem.
    + (*after_external*)
      intros r1 r2 s1' Hr Haf1.
      inv Haf1. inv Hr.
      cbn in *.
      rename m into m1'.
      inv H36. rename m' into m1''. rename tm' into m2''.
      exists ((Mem.support m2), (State rs' m2'' true)). repeat apply conj.
      -- constructor. inversion H44; eauto.
         unfold inner_sp. cbn.
         rewrite H39. subst sp. rewrite H7.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- assert ( RANGEPERM: Mem.range_perm m2'' sb 0 16 Cur Freeable). 
         { red. intros. inversion H44.
           eapply unchanged_on_perm; eauto.
           red. intros. exploit H19; eauto.
         }
         econstructor; cbn.
         rewrite H39. eauto.
         reflexivity. eauto. eauto. instantiate (1:= Hm'5). all: eauto.
         ++ etransitivity. instantiate (1:= injpw f m1' m2' Hm'1).
            constructor; eauto.
            constructor; eauto.
         ++ rewrite H40. eauto.
         ++ intros. destruct (f b0) as [[sb' d']|] eqn: Hf.
            * apply H45 in Hf as Hf'. rewrite H in Hf'. inv Hf'. eauto.
            * exploit H46; eauto. intros [A B]. eauto.
         ++ rewrite H39. subst sp. rewrite H7 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H44. 2: eauto.
            intros. red. intros. exploit H19; eauto.
         ++ rewrite H39. subst sp. rewrite H7 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H44. 2: eauto.
            intros. red. intros. exploit H19; eauto.
         ++ intros. rewrite H37; eauto.
         ++ inversion H44. eauto with mem.
      -- reflexivity.
  - (*internal_steps*)
    Local Opaque undef_regs.
    Ltac compute_pc := rewrite Ptrofs.add_unsigned;
                       rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
    Ltac find_instr := cbn; try rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
    intros. inv H; inv H0; inv H; cbn in *.
    ++ (*step_xor*)
      inv H14. symmetry in H7. inv H7.
      destruct (enter_fung_exec m2 rs0) as (m2'1 & m2'2 & m2'3 & m2'4 & sp &
                                              ALLOC & STORE1 & STORE2
                                             & LOAD1 & LOAD2 &  FREE & X & UNC); eauto.
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      exploit Mem.alloc_right_inject; eauto. intro INJ1.
      exploit Mem.store_outside_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ2.
      exploit Mem.store_outside_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ3.
      exploit Mem.free_right_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ4.
      eapply Genv.find_symbol_match in FINDKEY as FINDK'; eauto.
      destruct FINDK' as [b_mem' [VINJM FINDK']].
      rename H13 into Hpc. rename H17 into Hrdi. rename H18 into Hrsi.
      set (output := Int.xor input key).
      assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs0 m2 true) E0 s2'
             /\ ms (Call2 (Vptr b ofs) output m1) (Mem.support m2, s2')).
      { 
        (*execution of Asm code*)
        eexists. split.
        - (*plus steps*)
          econstructor.
      (*Pallocframe*)
      econstructor; eauto.
      find_instr. simpl.
      rewrite ALLOC. rewrite Ptrofs.add_zero. rewrite STORE1.
      rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
      repeat try Pgso. rewrite Hpc. cbn.
      rewrite Ptrofs.add_zero_l. reflexivity.
      (*read key*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. simpl.
      unfold exec_load. unfold Mem.loadv. unfold eval_addrmode. Ap64. cbn.
      unfold Genv.symbol_address in *. rewrite FINDK'. Ap64.
      rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_zero.
      exploit Mem.load_inject. apply INJ3. apply LOADKEY. eauto.
      intros [v2' [LOADK' INJV2]]. inv INJV2. rewrite Z.add_0_r in LOADK'.
      fold Ptrofs.zero. rewrite LOADK'.
      unfold nextinstr_nf, nextinstr. rewrite undef_regs_pc. Pgso. Pgss.
      cbn.
      rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one. simpl.
      reflexivity.
      (*xor*)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. Ap64. do 2 Pgso. rewrite undef_regs_rdi.
      rewrite undef_regs_rax. do 4 Pgso. Pgss.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_pc. Pgso. Pgss. cbn.
      compute_pc. reflexivity.
      (*call*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      compute_pc. reflexivity.
      apply star_refl. traceEq.
        - constructor; eauto.
          econstructor; eauto.
          + do 3 Pgso. rewrite undef_regs_rsp.
            Pgso. Pgso. rewrite undef_regs_rsp. Pgso. Pgso.
            Pgss. reflexivity.
          + simpl. reflexivity.
          + intros. red. intros. inversion Hm0. exploit mi_mappedblocks; eauto.
          + apply Mem.free_range_perm in FREE. eauto.
          + instantiate (1:= INJ3).
          constructor; eauto.
          -- red. eauto.
          -- eapply Mem.ro_unchanged_trans.
             eapply Mem.ro_unchanged_alloc; eauto.
             eapply Mem.ro_unchanged_trans.
             eapply Mem.ro_unchanged_store; eauto.
             eapply Mem.ro_unchanged_store; eauto.
             erewrite <- Mem.support_store; eauto.
             red. eauto using Mem.perm_store_2.
             red. intro. eapply Mem.valid_block_alloc; eauto.
             red. intros. eapply Mem.perm_alloc_4; eauto.
             intro. apply Mem.fresh_block_alloc in ALLOC.
             subst. congruence.
          -- red. intros.
             inversion X. eapply unchanged_on_perm; eauto.
          -- eauto with mem.
          -- eapply Mem.unchanged_on_implies; eauto.
             intros. cbn. eauto.
          -- red. intros. congruence.
          + repeat Pgso. rewrite undef_regs_rdi. Pgss.
            unfold output. rewrite Hrdi. reflexivity.
          + Pgso. Pgss. reflexivity.
          + apply Mem.valid_new_block in ALLOC as VALID. unfold Mem.valid_block in *.
          erewrite Mem.support_store. 2: eauto.
          erewrite Mem.support_store; eauto.
          + intros.
            inversion Hm0. exploit mi_mappedblocks; eauto.
          + Pgss. rewrite undef_regs_rsi. repeat Pgso. rewrite undef_regs_rsi.
            repeat Pgso.
          + intros. cbn. repeat try Pgso; destruct r; cbn in *; try congruence; eauto.
            rewrite not_win in H. inv H.
          + cbn. inversion X. eauto.
      }
      destruct H as [s2' [STEP MS]].  cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
      pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
      ++ (*step_free*)
     assert ({m2''1| Mem.free m2'' sb 0 16 = Some m2''1}).
     {
       apply Mem.range_perm_free; eauto.
     }
     destruct X as [m2'1 FREE'].
     exploit Mem.free_right_inject. apply Hm''. eauto.
     intros. exploit H11; eauto. intro INJ'.
     symmetry in H3. inv H3.  inv H15.
     assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs m2'' true) E0 s2'
             /\ ms (Return2 m) (Mem.support m2, s2')).
     {
       eexists. split.
       econstructor. econstructor; eauto. find_instr.
      (* Pfreeframe *)
       simpl. cbn. unfold Mem.loadv. subst sp. rewrite H1 in *.
       cbn in H12. cbn in H13. cbn. rewrite H12. rewrite H13.
       Plia. cbn. rewrite FREE'. unfold nextinstr. cbn. rewrite H9.
       cbn. compute_pc. reflexivity.
       (*Pret*)
       eapply star_step; eauto. econstructor; eauto. Simplif.
       find_instr. cbn. unfold inner_sp. rewrite <- H.
       rewrite pred_dec_true; eauto.
       eapply star_refl. traceEq.
      - constructor; eauto.
        econstructor. instantiate (1:= INJ'). all: eauto.
        + cbn. inv H8.
          constructor; eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
          -- red. eauto using Mem.perm_free_3.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1 := fun b ofs => loc_out_of_reach f m1 b ofs /\ b <> sb).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. congruence.
             intros. simpl. intuition auto. subst.
             unfold Mem.valid_block in H8. cbn in H14. congruence.
        + intros. cbn.
          cbn. repeat try Pgso; eauto; destruct r; cbn in *; try congruence; eauto.
        + cbn. cbn. inv H8.
          erewrite (Mem.support_free _ _ _ _ _ FREE'). inv H26. eauto.
      }
      destruct H3 as [s2' [STEP MS]].  cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
      pattern (State rs m2'' true),E0,s2'. eapply plus_ind2; eauto; intros.
      * apply plus_one; eauto.
      * eapply plus_trans; eauto.
        apply plus_one. auto.
  - constructor. intros. inv H.
Qed.

End CAinjp_b1.

Theorem self_simulation_wt :
  forward_simulation wt_c wt_c L1 L1.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [se' sg].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd w = int_fptr__void_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. reflexivity.
  - intros. inv H. exists s1. exists s1. constructor; eauto. inv H0.
    inv H1. cbn. eauto.
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
  - intros. subst.
    exists (se2, int__void_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0. constructor; cbn; eauto.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H0. inv H1.
      inv H. cbn. constructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

(* Self-sim using ro *)
Require Import ValueAnalysis.

Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_Callstateg : forall vf i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call1 vf i m)
| sound_Callstatef : forall vf o m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call2 vf o m)
| sound_Returnstatef : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return1 m)
| sound_Returnstateg : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return2 m).
End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma L1_ro : preserves L1 ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + constructor; eauto.
    + constructor; eauto.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor. eapply ro_acc_trans; eauto.
    eapply ro_acc_sound; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Theorem self_simulation_ro :
  forward_simulation ro ro L1 L1.
Proof.
  eapply preserves_fsim. eapply L1_ro; eauto.
Qed.

Lemma semantics_preservation_L1:
  forward_simulation cc_compcert cc_compcert L1 (Asm.semantics b1).
Proof.
  unfold cc_compcert.
  eapply compose_forward_simulations.
  eapply self_simulation_ro.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  eapply compose_forward_simulations.
  eapply CAinjp_simulation_L1.
  eapply semantics_asm_rel; eauto.
Qed.

Section CAinjp_b2.

Section MS.

Variable w0: ccworld (ro @ cc_c_asm_injp).
Let row := snd (fst w0).
Let w := snd w0.
Let wp:= cajw_injp w.

Variable se tse: Genv.symtbl.

Let ge := Genv.globalenv se b2.
Let tge := Genv.globalenv tse b2.

Hypothesis GE: match_stbls injp wp se tse.


Let sg := cajw_sg w.
Let rs0 := cajw_rs w.
Let m2 := match wp with injpw _ _ m2 _ => m2 end.
Let s2 := Mem.support m2.

Let sp0 := rs0 RSP.
Let ra0 := rs0 RA.
Let vf0 := rs0 PC.
Let bx0 := rs0 RBX. (*only used callee_save register in this sample*)

Inductive match_state_ro_c_asm : state -> (sup * Asm.state) -> Prop :=
|match_call1_ro m1 b b' ofs eb input j Hm delta:
  wp = injpw j m1 m2 Hm ->
  sp0 <> Vundef -> ra0 <> Vundef ->
  Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
  valid_blockv (Mem.support m2) sp0 ->
  vf0 = Vptr eb Ptrofs.zero ->
  Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
  j b = Some (b', delta) ->
  rs0 RDI = Vint input ->
  rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
  sound_memory_ro se m1 ->
  match_state_ro_c_asm (Call1 (Vptr b ofs) input m1) (s2, State rs0 m2 true)
|match_call2_ro m1 b ofs j Hm (rs:regset) m1' m2' Hm' output sb b' delta eb:
    let sp := rs RSP in let ra := rs RA in let vf := rs PC in
    sp = Vptr sb Ptrofs.zero ->
    wp = injpw j m1 m2 Hm ->
    (forall ofs, loc_out_of_reach j m1 sb ofs) ->
    Mem.range_perm m2' sb 0 16 Cur Freeable ->
    injp_acc wp (injpw j m1' m2' Hm') ->
    rs PC = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
    j b = Some (b', delta) -> rs RDI = Vint output ->
    ra = Vptr eb (Ptrofs.repr 3) ->
    Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
    sup_In sb (Mem.support m2') -> ~ sup_In sb s2 ->
    (forall b d, j b = Some (sb,d) -> False) ->
    vf <> Vundef ->
    Mem.loadv Mptr m2' (Val.offset_ptr sp (Ptrofs.repr 8)) = Some ra0 ->
    Mem.loadv Mptr m2' (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
    valid_blockv s2 sp0 ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include s2 (Mem.support m2')  ->
     sound_memory_ro se m1' ->
     match_state_ro_c_asm (Call2 (Vptr b ofs) output m1') (s2, State rs m2' true)
|match_return1_ro j j' m1 m1'' m2'' Hm Hm'' (rs:regset) eb sb:
    let sp := rs RSP in
    sp = Vptr sb Ptrofs.zero ->
     wp = injpw j m1 m2 Hm ->
     (forall ofs, loc_out_of_reach j m1 sb ofs) ->
     Mem.range_perm m2'' sb 0 16 Cur Freeable ->
     injp_acc wp (injpw j' m1'' m2'' Hm'') ->
     rs PC = Vptr eb (Ptrofs.repr 3) ->
     Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
     (forall b d, j' b = Some (sb,d) -> False) ->
     Mem.loadv Mptr m2'' (Val.offset_ptr sp (Ptrofs.repr 8)) = Some ra0 ->
     Mem.loadv Mptr m2'' (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     ~ sup_In sb s2 ->
     valid_blockv (Mem.support m2) sp0 ->
     (forall r, is_callee_save r = true  -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support m2'') ->
     sound_memory_ro se m1'' ->
     match_state_ro_c_asm (Return1 m1'') (s2, State rs m2'' true)
|match_return2_ro j' m2'' m1'' (rs:regset) Hm'':
  (injp_acc wp (injpw j' m1'' m2'' Hm'')) ->
   rs RSP = rs0 RSP -> rs PC = rs0 RA ->
   (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
   Mem.sup_include s2 (Mem.support m2'') ->
   sound_memory_ro se m1'' ->
   match_state_ro_c_asm (Return2 m1'') (s2, State rs m2'' false).

End MS.

Ltac rlia := rewrite maxv; lia.
Ltac Plia := try rewrite !Ptrofs.unsigned_zero; try rewrite!Ptrofs.unsigned_repr; try rlia.
Ltac Ap64 := replace Archi.ptr64 with true by reflexivity.
Ltac Ap64_in H0 := replace Archi.ptr64 with true in H0 by reflexivity.

Lemma match_program_id' :
  match_program (fun _ f0 tf => tf = id f0) eq b2 b2.
Proof.
  red. red. constructor; eauto.
  constructor. constructor. eauto. simpl. econstructor; eauto.
  constructor. eauto.
  constructor; cbn; eauto. constructor; eauto.
  econstructor.
  apply linkorder_refl.
  constructor. constructor; eauto.
  constructor. eauto. econstructor.
  apply linkorder_refl. eauto.
  constructor; eauto.
Qed.

Ltac Pgso := rewrite Pregmap.gso; try congruence.
Ltac Pgss := rewrite Pregmap.gss.

Definition source_mem (w: injp_world) := match w with injpw _ m1 _ _ => m1 end.

Lemma CAinjp_simulation_L2: forward_simulation
                 (ro @ cc_c_asm_injp)
                 (ro @ cc_c_asm_injp)
                 L2 (Asm.semantics b2).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_ro_c_asm w se1 se2 s1 s2 /\
                          cajw_sg (snd w) = int_fptr__void_sg /\
                          ro_mem (snd (fst w)) = source_mem (cajw_injp (snd w))).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as  [[? [? ?]] [[f ? ? Hm] sg rs0]]; destruct Hse as [Hi Hse];
    inv Hi; inv Hse; subst; cbn in *; eauto.
  -  (*valid_query*)
    intros q1' q2 [q1 [Hqi Hq]]. inv Hqi. inv Hq.
    simpl. cbn in *.
    generalize  match_program_id'. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros q1' q2 s1 [q1 [Hqi Hq]] Hi1. inv Hi1.
    inv Hqi. inv Hq.
    inv H19. 2:{ rewrite size_int_fptr__void_sg_0 in H4. extlia. }
    rename tm0 into m2. rename m into m1.
    exists (Mem.support m2, State rs0 m2 true).
    generalize  match_program_id'. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    repeat apply conj.
    + econstructor; eauto. inv H18.
      subst tsp0. congruence.
    + eauto.
    + subst tvf. unfold Genv.find_funct in TRAN.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      subst targs. rewrite loc_arguments_int_fptr in H12. simpl in H12. inv H12. inv H9.
      inv H7. inv H8.
      econstructor; cbn; eauto.
      inv H18. subst tsp0. congruence.
      inv H. eauto.
    + eauto.
    + inv H. eauto.
  - (* final_state *)
    intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms. inv H. cbn in *. inv H0.
    exists (rs, m2''). split. constructor.
    exists (cr Vundef m). split. constructor. constructor.
    inv H3. constructor; eauto. inversion H18. eauto.
    econstructor; eauto.
    intros. inv H. rewrite size_int_fptr__void_sg_0 in H1. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. cbn. inv EXT1. inv MS.
    inv H. cbn in *. inv H12. cbn in *.
    symmetry in H9. inv H9.
    eapply Genv.match_stbls_incr in H2; eauto.
    2:{
      intros. exploit H36; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    exists ((s,row s m),(cajw (injpw f m m2' Hm'1) int__void_sg rs)).
    exists (rs,m2'). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id'. intro TRAN.
      rewrite H13.
      assert (Val.inject f (Vptr b ofs) (Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)))).
      econstructor; eauto.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + rename m into m'. rename m1 into m. rename m2 into tm. rename m2' into tm'.
      exists (cq (Vptr b ofs) int__void_sg (Vint output :: nil) m'). split.
      constructor. constructor. eauto.
      econstructor; eauto.
      -- rewrite loc_arguments_int. cbn. rewrite H15.
         constructor; eauto.
      -- rewrite H13. econstructor; eauto.
      -- intros. rewrite size_int__void_sg_0 in H.
         subst sp. rewrite H8 in H. inv H. extlia.
      -- subst sp. rewrite H8. constructor.
      -- subst ra. rewrite H16. constructor.
      -- subst sp. rewrite H8. constructor. eauto.
      -- eapply args_removed_tailcall_possible.
         red. apply size_int__void_sg_0.
      -- congruence.
      -- subst ra. rewrite H16. congruence.
    + constructor; eauto.
    + constructor; eauto.
      inversion H33. eauto with mem.
    + (*after_external*)
      intros r1' r2 s1' [r1 [Hri Hr]] Haf1.
      inv Haf1. inv Hri. inv H. inv Hr.
      cbn in *.
      rename m into m1'. inv H0.
      inv H39. rename m' into m1''. rename tm' into m2''.
      exists ((Mem.support m2), (State rs' m2'' true)). repeat apply conj.
      -- constructor. inversion H46; eauto.
         unfold inner_sp.  cbn.
         rewrite H42. subst sp. rewrite H8.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- assert ( RANGEPERM: Mem.range_perm m2'' sb 0 16 Cur Freeable). 
         { red. intros. inversion H46.
           eapply unchanged_on_perm; eauto.
           red. intros. exploit H20; eauto.
         }
         econstructor; cbn.
         rewrite H42. eauto.
         reflexivity. eauto. eauto. instantiate (1:= Hm'5). all: eauto.
         ++ etransitivity. instantiate (1:= injpw f m1' m2' Hm'1).
            constructor; eauto.
            constructor; eauto.
         ++ rewrite H43. eauto.
         ++ intros. destruct (f b0) as [[sb' d']|] eqn: Hf.
            * apply H47 in Hf as Hf'. rewrite H in Hf'. inv Hf'. eauto.
            * exploit H48; eauto. intros [A B]. eauto.
         ++ rewrite H42. subst sp. rewrite H8 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H46. 2: eauto.
            intros. red. intros. exploit H20; eauto.
         ++ rewrite H42. subst sp. rewrite H8 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H46. 2: eauto.
            intros. red. intros. exploit H20; eauto.
         ++ intros. rewrite H40; eauto.
         ++ inversion H46. eauto with mem.
         ++ eapply ro_acc_sound; eauto.
     -- reflexivity.
     -- reflexivity.            
  - (*internal_steps*)
    Local Opaque undef_regs.
    Ltac compute_pc := rewrite Ptrofs.add_unsigned;
                       rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
    Ltac find_instr := cbn; try rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
    intros. inv H; inv H0; inv H; cbn in *. inv H1.
    ++ (*step_xor*)
      inv H13. symmetry in H8. inv H8.
      destruct (enter_fung_exec m2 rs0) as (m2'1 & m2'2 & m2'3 & m2'4 & sp &
                                              ALLOC & STORE1 & STORE2
                                             & LOAD1 & LOAD2 &  FREE & X & UNC); eauto.
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      exploit Mem.alloc_right_inject; eauto. intro INJ1.
      exploit Mem.store_outside_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ2.
      exploit Mem.store_outside_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ3.
      exploit Mem.free_right_inject; eauto.
      intros. inversion Hm0. eauto. intro INJ4.
      rename H14 into Hpc. rename H18 into Hrdi. rename H19 into Hrsi.
      set (key := Int.repr 42).
      set (output := Int.xor input key).
      assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b2) (State rs0 m2 true) E0 s2'
             /\ ms (Call2 (Vptr b ofs) output m1) (Mem.support m2, s2')).
      { 
        (*execution of Asm code*)
        eexists. split.
        - (*plus steps*)
          econstructor.
      (*Pallocframe*)
      econstructor; eauto.
      find_instr. simpl.
      rewrite ALLOC. rewrite Ptrofs.add_zero. rewrite STORE1.
      rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
      repeat try Pgso. rewrite Hpc. cbn.
      rewrite Ptrofs.add_zero_l. reflexivity.
      (*xor*)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. Ap64. do 2 Pgso.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_pc. Pgso. Pgss. cbn.
      rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one. simpl.
      reflexivity.
      (*call*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      compute_pc. reflexivity.
      apply star_refl. traceEq.
        - constructor; eauto.
          econstructor; eauto.
          + do 3 Pgso. rewrite undef_regs_rsp.
            Pgso. Pgso. 
            Pgss. reflexivity.
          + simpl. reflexivity.
          + intros. red. intros. inversion Hm0. exploit mi_mappedblocks; eauto.
          + apply Mem.free_range_perm in FREE. eauto.
          + instantiate (1:= INJ3).
          constructor; eauto.
          -- red. eauto.
          -- eapply Mem.ro_unchanged_trans.
             eapply Mem.ro_unchanged_alloc; eauto.
             eapply Mem.ro_unchanged_trans.
             eapply Mem.ro_unchanged_store; eauto.
             eapply Mem.ro_unchanged_store; eauto.
             erewrite <- Mem.support_store; eauto.
             red. eauto using Mem.perm_store_2.
             red. intro. eapply Mem.valid_block_alloc; eauto.
             red. intros. eapply Mem.perm_alloc_4; eauto.
             intro. apply Mem.fresh_block_alloc in ALLOC.
             subst. congruence.
          -- red. intros.
             inversion X. eapply unchanged_on_perm; eauto.
          -- eauto with mem.
          -- eapply Mem.unchanged_on_implies; eauto.
             intros. cbn. eauto.
          -- red. intros. congruence.
          + repeat Pgso. rewrite undef_regs_rdi. Pgss.
            unfold output. rewrite Hrdi. reflexivity.
          + Pgso. Pgss. reflexivity.
          + apply Mem.valid_new_block in ALLOC as VALID. unfold Mem.valid_block in *.
          erewrite Mem.support_store. 2: eauto.
          erewrite Mem.support_store; eauto.
          + intros.
            inversion Hm0. exploit mi_mappedblocks; eauto.
          + Pgss. rewrite undef_regs_rsi. repeat Pgso.
          + cbn. rewrite <- H. constructor; eauto.
          + intros. cbn. repeat try Pgso; destruct r; cbn in *; try congruence; eauto.
            rewrite not_win in H1. inv H1.
          +  cbn. inversion X. eauto.
      }
      destruct H1 as [s2' [STEP MS]]. cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se2 b2); clear; intros.
      pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
      ++ (*step_free*)
     assert ({m2''1| Mem.free m2'' sb 0 16 = Some m2''1}).
     {
       apply Mem.range_perm_free; eauto.
     }
     destruct X as [m2'1 FREE'].
     exploit Mem.free_right_inject. apply Hm''. eauto.
     intros. exploit H11; eauto. intro INJ'.
     symmetry in H3. inv H3. rename m3 into m2. inv H15.
     assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs m2'' true) E0 s2'
             /\ ms (Return2 m) (Mem.support m2, s2')).
     {
       eexists. split.
       econstructor. econstructor; eauto. find_instr.
      (* Pfreeframe *)
       simpl. cbn. unfold Mem.loadv. subst sp. rewrite H1 in *.
       cbn in H12. cbn in H13. cbn. rewrite H12. rewrite H13.
       Plia. cbn. rewrite FREE'. unfold nextinstr. cbn. rewrite H9.
       cbn. compute_pc. reflexivity.
       (*Pret*)
       eapply star_step; eauto. econstructor; eauto. Simplif.
       find_instr. cbn. unfold inner_sp. rewrite <- H.
       rewrite pred_dec_true; eauto.
       eapply star_refl. traceEq.
      - constructor; eauto.
        econstructor. instantiate (1:= INJ'). all: eauto.
        + cbn. inv H8.
          constructor; eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
          -- red. eauto using Mem.perm_free_3.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1 := fun b ofs => loc_out_of_reach f m1 b ofs /\ b <> sb).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. congruence.
             intros. simpl. intuition auto. subst.
             unfold Mem.valid_block in H8. unfold s2 in H14. cbn in H14. congruence.
        + intros. cbn.
          cbn. repeat try Pgso; eauto; destruct r; cbn in *; try congruence; eauto.
        + cbn. unfold s2. cbn. inv H8.
          erewrite (Mem.support_free _ _ _ _ _ FREE'). inv H26. eauto.
      }
      destruct H3 as [s2' [STEP MS]]. unfold s2. cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
      pattern (State rs m2'' true),E0,s2'. eapply plus_ind2; eauto; intros.
      * apply plus_one; eauto.
      * eapply plus_trans; eauto.
        apply plus_one. auto.
  - constructor. intros. inv H.
Qed.
End CAinjp_b1.

Theorem self_simulation_wt :
  forward_simulation wt_c wt_c L1 L1.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [se' sg].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd w = int_fptr__void_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. reflexivity.
  - intros. inv H. exists s1. exists s1. constructor; eauto. inv H0.
    inv H1. cbn. eauto.
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
  - intros. subst.
    exists (se2, int__void_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0. constructor; cbn; eauto.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H0. inv H1.
      inv H. cbn. constructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

(* Self-sim using ro *)
Require Import ValueAnalysis.

Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_Callstateg : forall vf i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call1 vf i m)
| sound_Callstatef : forall vf o m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call2 vf o m)
| sound_Returnstatef : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return1 m)
| sound_Returnstateg : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return2 m).
End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma L1_ro : preserves L1 ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + constructor; eauto.
    + constructor; eauto.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor. eapply ro_acc_trans; eauto.
    eapply ro_acc_sound; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Theorem self_simulation_ro :
  forward_simulation ro ro L1 L1.
Proof.
  eapply preserves_fsim. eapply L1_ro; eauto.
Qed.

Lemma semantics_preservation_L1:
  forward_simulation cc_compcert cc_compcert L1 (Asm.semantics b1).
Proof.
  unfold cc_compcert.
  eapply compose_forward_simulations.
  eapply self_simulation_ro.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  eapply compose_forward_simulations.
  eapply CAinjp_simulation_L1.
  eapply semantics_asm_rel; eauto.
Qed.

(*
(* Final theorem *)
Require Import Linking Smallstep SmallstepLinking.

Lemma compose_transf_Clight_Asm_correct:
  forall M_C' tp spec,
  compose (Clight.semantics1 M_C) L_A = Some spec ->
  transf_clight_program M_C = OK M_C' ->
  link M_C' M_A = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply M_A_semantics_preservation.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.
*)
