Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.

Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.


Require Import Integers.
Require Import Values Memory.

Require Import CallconvBig InjectFootprint Injp.
Require Import CAnew.
Require Import Asm Asmrel.
Require Import Asmgenproof0 Asmgenproof1.
Require Import Encrypt EncryptSpec.

Import GS.

Section MS.
  
  Variable w: ccworld cc_c_asm_injp_new.
  Variable se tse : Genv.symtbl.
  Let ge := Genv.globalenv se b1.
  Let tge := Genv.globalenv tse b1.

  Let wp := cajw_injp w.
  Let sg := cajw_sg w.
  Let rs0 := cajw_rs w.
  Let m2 := match wp with injpw _ _ m2 _ => m2 end.
  Let s2 := Mem.support m2.
  Hypothesis GE: CKLR.match_stbls injp wp se tse.
  Let sp0 := rs0 RSP.
  Let ra0 := rs0 RA.
  Let vf0 := rs0 PC.
  
  Inductive match_states_c_asm : injp_world -> state -> (sup * Asm.state) -> Prop :=
  |match_initial i b ofs j m1 m2 Hm b' delta eb:
     wp = injpw j m1 m2 Hm ->
     sp0 <> Vundef -> ra0 <> Vundef ->
     Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
     valid_blockv s2 sp0 ->
     rs0 RDI = Vint i ->
     j b = Some (b', delta) ->
     rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
     vf0 = Vptr eb Ptrofs.zero ->
     Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
     match_states_c_asm wp (Initial i (Vptr b ofs) m1) (s2, State rs0 m2 true)
  |match_final j m1' m2' Hm' (rs: regset):
    rs RSP = rs0 RSP -> rs PC = rs0 RA ->
    (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
    Mem.sup_include s2 (Mem.support m2') ->
    injp_acci wp (injpw j m1' m2' Hm') ->
    injp_acce wp (injpw j m1' m2' Hm') ->
    match_states_c_asm wp (Final m1') (s2, State rs m2' false).
    
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


Lemma size_int_ptr__void_sg_0:
  size_arguments int_ptr__void_sg = 0.
Proof.
  unfold size_arguments, int_ptr__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int_ptr :
  loc_arguments int_ptr__void_sg = One (R DI) :: One (R SI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_ptr__void_sg = One AX.
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

Lemma undef_regs_spec: forall l rs r,
    (undef_regs l rs) r = if (In_dec preg_eq r l) then Vundef else rs r.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. destr. destr_in o. rewrite IHl. destr. Pgss. reflexivity.
    rewrite IHl. destr.
    rewrite IHl. destr. Pgso. intro.
    apply n. left. auto.
Qed.

(** This lemmas (and functional extensionality of register sets) are not necessary but can be used to simplify the proof *)
Lemma undef_regs_extension_1:
  forall l rs v r,
    (forall r' : preg, In r' l -> r <> r') ->
      (undef_regs l rs) # r <- v = undef_regs l (rs # r <- v).
Proof.
  intros.
  apply Axioms.functional_extensionality.
  intros. 
  destruct (preg_eq x r).
  - subst. Pgss. rewrite undef_regs_other; auto. Pgss. reflexivity.
  - Pgso. rewrite !undef_regs_spec. destr. Pgso.
Qed.

Lemma undef_regs_extension_2:
  forall l rs, (undef_regs l (undef_regs l rs)) = undef_regs l rs.
Proof.
  intros. apply Axioms.functional_extensionality.
  intros. rewrite !undef_regs_spec. destr.
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

Lemma load_result_Many64_eq:
    forall v,  Val.load_result Many64 v = v.
Proof.
  intros. reflexivity. Qed.


Lemma enter_func_exec:
  forall m (rs0: regset),
      (rs0 RSP) <> Vundef -> Val.has_type (rs0 RSP) Tptr ->
      (rs0 RA) <> Vundef -> Val.has_type (rs0 RA) Tptr ->
      exists m1 m2 m3 tsp,
    Mem.alloc m 0 16 = (m1,tsp)
    /\ Mem.store Mptr m1 tsp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2
    /\ Mem.store Mptr m2 tsp (Ptrofs.unsigned (Ptrofs.repr 8)) (rs0 RA) = Some m3
    /\ Mem.load Mptr m3 tsp (Ptrofs.unsigned (Ptrofs.repr 8)) = Some (rs0 RA)
    /\ Mem.load Mptr m3 tsp (Ptrofs.unsigned (Ptrofs.zero)) = Some (rs0 RSP)
    /\ Mem.unchanged_on (fun _ _ => True) m m3.
Proof.
  intros.
  destruct (Mem.alloc m 0 16) as [m1 tsp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  assert (STORE: {m2| Mem.store Mptr m1 tsp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H3. simpl in H3.
  unfold Mptr in H3. replace Archi.ptr64 with true in H3 by reflexivity. cbn in H3.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_zero.
  red. exists  0. lia. destruct STORE as [m2 STORE1].
  assert (STORE: {m3| Mem.store Mptr m2 tsp (Ptrofs.unsigned (Ptrofs.repr 8)) (rs0 RA) = Some m3}).
  apply Mem.valid_access_store.
  red. split. red. intros.
  rewrite Ptrofs.unsigned_repr in H3.
  unfold Mptr in H3. replace Archi.ptr64 with true in H3 by reflexivity. cbn in H3.
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
  exists m1,m2, m3,tsp. split. eauto. split. eauto. split. eauto. split. eauto. split. eauto.
  eapply mem_unchanged_on_trans_implies_valid. 
  eapply Mem.alloc_unchanged_on; eauto. instantiate (1:= fun b _ => b <> tsp).
  eapply Mem.unchanged_on_trans; eapply Mem.store_unchanged_on; eauto.
  intros. simpl. intro. subst. apply Mem.fresh_block_alloc in ALLOC. eapply ALLOC; eauto with mem.
Qed.
  
Lemma CAinjp_simulation_encrypt : forward_simulation (cc_c_asm_injp_new) L_E (Asm.semantics b1).
Proof.
  constructor.
  econstructor; eauto. instantiate (1:= fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun wp s1 s2 => match_states_c_asm w se2 wp s1 s2 /\ cajw_sg w = int_ptr__void_sg).
  eapply forward_simulation_plus with (match_states := ms);
    destruct w as [[f ? ? Hm] sg rs0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  - (* valid *)
    intros. inv H.
    simpl. cbn in *.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros. inv H. inv H0.
    exists (Mem.support m2, State rs0 m2 true).
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    split; auto. split; auto.
    + econstructor; eauto.
      inv H14. subst tsp0. congruence.
    + constructor; eauto.
      subst targs. rewrite loc_arguments_int_ptr in H9.
      simpl in H9. inv H9. inv H7. inv H9. inv H4.
      unfold Genv.find_funct in TRAN. subst tvf.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      econstructor; simpl; eauto.
      inv H14. subst tsp0. congruence.
      inv H3. reflexivity. subst i0. eauto.
  - (* final *)
    intros. inv H0. inv H. inv H0.
    cbn in *.
    exists (rs, m2'). exists (injpw j m m2' Hm').
    repeat apply conj; eauto. constructor.
    econstructor; eauto.
  - intros. inv H0.
  - (* step *)
    Local Opaque undef_regs.
    Ltac compute_pc := rewrite Ptrofs.add_unsigned;
                       rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
    Ltac find_instr := cbn; try rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
    intros. inv H. inv H0. inv H.
    cbn in *. inv H7. rename m3 into m2. rename m into m1.
     eapply Genv.find_symbol_match in FINDKEY as FINDK'; eauto.
     destruct FINDK' as [b_mem' [VINJM FINDK']].
    rename H18 into Hpc. rename H17 into Hrsi. rename H13 into Hrdi.
    assert (exists s2': Asm.state,
               plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs0 m2 true) E0 s2'
               /\ ms (injpw j m1 m2 Hm )(Final m') (Mem.support m2, s2')).
    {
      exploit enter_func_exec; eauto.
      intros (m2'1 & m2'2 & m2'3 & tsp & ALLOC & STORE1 & STORE2 & LOAD2 & LOAD1 & UNC).
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      exploit Mem.alloc_right_inject; eauto. intro INJ11.
      exploit Mem.store_outside_inject; eauto. intros. eapply FRESH. eapply Mem.valid_block_inject_2; eauto. intro INJ12.
      exploit Mem.store_outside_inject; eauto. intros. eapply FRESH. eapply Mem.valid_block_inject_2; eauto. intro INJ13.
      exploit Mem.store_mapped_inject; eauto.
      intros (m2'4 & STORE3 & INJ14).
      assert ({m2'5| Mem.free m2'4 tsp 0 16 = Some m2'5}).
      apply Mem.range_perm_free. red. intros. eauto with mem.
      destruct X as [m2'5 FREE].
      exploit Mem.free_right_inject; eauto.
      intros. apply FRESH. eapply Mem.valid_block_inject_2; eauto.
      intro INJ15.
      assert (ACCTL: injp_acc_tl (injpw j m1 m2 Hm) (injpw j m' m2'5 INJ15)).
      {
        constructor; eauto.
        - red. intros. elim H. eauto with mem.
        - red. intros. 
          eapply Mem.valid_block_alloc_inv in ALLOC as INV.
          2: { instantiate (1:= b0). eauto with mem. }
          destruct INV; eauto. subst. eapply Mem.alloc_result in ALLOC as RES; eauto.
          rewrite RES. reflexivity. congruence.
        - eapply Mem.ro_unchanged_store; eauto.
        - red. intros.
          assert (BNEQ: b0 <> tsp).
          {
            intro. subst. apply FRESH. auto.
          }
          erewrite <- Mem.loadbytes_alloc_unchanged. 2: eauto. 2: eauto.
          erewrite <- Mem.loadbytes_store_other. 2: eauto. 2: eauto.
          erewrite <- Mem.loadbytes_store_other. 2: eauto. 2: eauto.
          eapply Mem.ro_unchanged_trans. eapply Mem.ro_unchanged_store; eauto. 
          eapply Mem.ro_unchanged_free; eauto.
          apply Mem.support_store in STORE3 as SUP3. rewrite SUP3. eauto.
          red. intros. eauto with mem.
          eauto with mem. eauto. intros. intro. eapply H1; eauto. eauto with mem.
        - red. intros. eauto with mem.
        - red. intros.
          eapply Mem.perm_alloc_4; eauto. eauto with mem.
          intro. apply FRESH. subst. eauto.
        - apply Mem.support_store in STORE as SUP.
          split. constructor; rewrite SUP; reflexivity.
          eapply Mem.store_unchanged_on; eauto. intros.
          intro. red in H0. congruence.
        - apply Mem.support_store in STORE1 as SUP1.
          apply Mem.support_store in STORE2 as SUP2.
          apply Mem.support_store in STORE3 as SUP3.
          apply Mem.support_alloc in ALLOC as SUPA.
          apply Mem.support_free in FREE as SUPF.
          split. constructor; rewrite SUPF, SUP3, SUP2, SUP1, SUPA; simpl.
          rewrite Mem.update_list_length. reflexivity. reflexivity.
          eapply mem_unchanged_on_trans_implies_valid. eapply Mem.alloc_unchanged_on. eauto.
          instantiate (1:= fun b ofs => loc_out_of_reach j m1 b ofs /\ Mem.valid_block m2 b).
          2: { intros. simpl. split; eauto. }
          eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
          intros. intros [A B]. congruence.
          eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
          intros. intros [A B]. congruence.
          eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
          intros. intros [A B]. red in A. eapply A; eauto.
          apply Mem.store_valid_access_3 in STORE as HH. destruct HH as [C D].
          red in C. specialize (C (i0 -delta)). exploit C; eauto. lia.
          eauto with mem.
          eapply Mem.free_unchanged_on. eauto. intros. intros [A B]. congruence.
        - red. intros. congruence.
        - red. intros. congruence.
        - red. intros. elim H3. eauto with mem.
      }
      inv H12. symmetry in H.
      eexists. split.
      - (* steps *)
        econstructor.
        (* Pallocframe *)
        econstructor; eauto.
        find_instr. simpl. rewrite ALLOC. rewrite Ptrofs.add_zero. rewrite STORE1.
        rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
        repeat try Pgso. rewrite Hpc. cbn.
        rewrite Ptrofs.add_zero_l. reflexivity.
        (*read key*)
        eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. simpl.
        unfold exec_load. unfold Mem.loadv. unfold eval_addrmode. Ap64. cbn.
        unfold Genv.symbol_address in *. rewrite FINDK'. Ap64.
        rewrite Ptrofs.add_zero_l.
        unfold Ptrofs.of_int64. rewrite Int64.unsigned_zero.
        exploit Mem.load_inject. apply INJ13. apply LOAD. eauto.
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
        compute_pc.
        (* rewrite !undef_regs_extension_1.
        rewrite undef_regs_extension_2.
        rewrite <- undef_regs_extension_1. *)
        reflexivity.
        (*store output*) 
        eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
        Ap64. unfold exec_store. cbn. unfold eval_addrmode. Ap64. simpl. cbn.
        rewrite undef_regs_rsi. repeat Pgso.
        rewrite undef_regs_rdi. Pgss. rewrite undef_regs_rsi. repeat Pgso.
        rewrite Hrsi. cbn. Ap64.
        rewrite Int64.add_zero_l.
        unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
        2: { unfold Int64.max_unsigned. cbn. lia. }
        rewrite Ptrofs.add_zero.
        unfold Mem.storev. 
        erewrite Mem.address_inject; eauto with mem.
        rewrite Hrdi. cbn. rewrite STORE3.
        unfold nextinstr_nf, nextinstr. cbn.
        rewrite undef_regs_nil.
        rewrite !undef_regs_pc. Pgss. cbn.
        compute_pc.
        reflexivity.
        (*free *)
        eapply star_step. eauto. econstructor; eauto. Simplif. find_instr. cbn.
        unfold Mem.loadv. rewrite !undef_regs_rsp. Pgso. rewrite undef_regs_rsp.
        repeat Pgso. rewrite undef_regs_rsp. Pgso. Pgso. Pgss.
        simpl. rewrite !Ptrofs.add_zero_l.
        assert (b' <> tsp).
        {
          intro. subst. apply FRESH.
          eapply Mem.valid_block_inject_2; eauto.
        }
        erewrite Mem.load_store_other; eauto. rewrite LOAD2.
        erewrite Mem.load_store_other; eauto. rewrite LOAD1.
        rewrite Ptrofs.unsigned_zero.
        unfold free'. simpl.
        rewrite FREE. unfold nextinstr. cbn.
        compute_pc. reflexivity.
        (*ret*)
        eapply star_step. econstructor; eauto. Simplif. find_instr. cbn.
        unfold inner_sp. rewrite H. rewrite pred_dec_true.
        reflexivity. auto.
        eapply star_refl.
        traceEq. traceEq. traceEq.
      - econstructor; eauto.  cbn.
        set (w := {| cajw_injp := injpw j m1 m2 Hm; cajw_sg := int_ptr__void_sg; cajw_rs := rs0 |}).
        set (gw:= injpw j m1 m2 Hm).
        replace (gw) with (cajw_injp w) by reflexivity.
        replace (m2) with (match cajw_injp w with |injpw _ _ m2 _ => m2 end) by reflexivity.
        econstructor; eauto; unfold w; cbn.
        + intros.
          repeat try Pgso; eauto; destruct r; cbn in *; try congruence; eauto.
          Ap64_in H1. simpl in H1. rewrite not_win in H1. congruence.
        + inv ACCTL. destruct H21 as [_ [? _]]. eauto.
        + eapply injp_acc_tl_i. eauto.
        + eapply injp_acc_tl_e. eauto.
    }
    destruct H as [s2' [STEP MS]].  cbn.
    exists (Mem.support m2, s2'). intuition eauto.
    revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
    pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
  - auto using well_founded_ltof.
Qed.
