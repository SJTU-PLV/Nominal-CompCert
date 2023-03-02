Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen SymbtablegenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemanticsArchi.
Require Import LocalLib AsmInject AsmInjectArchi.
Require Import Asmgenproof0 RelocProgGlobalenvs MemoryAgree.
Require Import Symbtablegenproof.
Import ListNotations.

Open Scope Z_scope.
Local Open Scope list_scope.
Close Scope asm.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.


Section PRESERVATION.
  
(** Transformation *)
Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv instr_size tprog.

Hypothesis TRANSF: match_prog instr_size prog tprog.

Let match_inj := match_inj instr_size prog tprog.


Let glob_block_valid := glob_block_valid prog.
Let match_states := match_states instr_size prog tprog.


Axiom low_half_equal : forall id ofs, Asm.low_half ge id ofs = low_half tge id ofs.

Lemma eval_offset_equal: forall ofs,
      Asm.eval_offset ge ofs = eval_offset tge ofs.
Proof.
  unfold Asm.eval_offset, eval_offset.
  intros. destr. eapply low_half_equal.
Qed.

Lemma exec_load_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk rd ra ofs
                          (INJ: j = Mem.flat_inj (Mem.support m1))
                          (MINJ: magree j  m1 m2)
                          (MATCHINJ: match_inj j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1), 
    Asm.exec_load ge sz chunk rs1 m1 rd ra ofs = Next rs1' m1' ->
    exists rs2' m2',
      exec_load sz tge chunk rs2 m2 rd ra ofs = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.
  unfold exec_load.
  destr_in H.
  rewrite <- eval_offset_equal.
  exploit Val.offset_ptr_inject;eauto. intros.
  exploit loadv_inject;eauto.
  intros (v2 & LOADV & INJ').
  rewrite LOADV. do 2 eexists. split;eauto.
  inv H. eapply match_states_intro; eauto.
  apply nextinstr_pres_inject.
  apply regset_inject_expand; eauto.
Qed.

Lemma exec_store_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk rs ra ofs
                          (INJ: j = Mem.flat_inj (Mem.support m1))
                          (MINJ: magree j  m1 m2)
                          (MATCHINJ: match_inj j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1), 
    Asm.exec_store ge sz chunk rs1 m1 rs ra ofs = Next rs1' m1' ->
    exists rs2' m2',
      exec_store sz tge chunk rs2 m2 rs ra ofs = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.
  unfold exec_store.
  destr_in H.
  rewrite <- eval_offset_equal.
  exploit Val.offset_ptr_inject;eauto. intros.
  exploit storev_pres_inject;eauto.
  intros (v2 & STOREV & INJ').
  exploit (Mem.support_storev). apply Heqo. intros SUP.  
  rewrite STOREV. do 2 eexists. split;eauto.
  inv H. eapply match_states_intro; eauto.
  eapply storev_pres_match_inj;eauto.
  rewrite <- SUP.
  apply nextinstr_pres_inject. auto.
  eapply storev_pres_glob_block_valid;eauto.
Qed.

Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Hint Resolve (* nextinstr_nf_pres_inject *) nextinstr_pres_inject regset_inject_expand
  regset_inject_expand_vundef_left undef_regs_pres_inject
  Val.zero_ext_inject Val.sign_ext_inject Val.longofintu_inject Val.longofint_inject
  Val.singleoffloat_inject Val.loword_inject Val.floatofsingle_inject Val.intoffloat_inject Val.maketotal_inject
  Val.intoffloat_inject Val.floatofint_inject Val.intofsingle_inject Val.singleofint_inject
  Val.longoffloat_inject Val.floatoflong_inject Val.longofsingle_inject Val.singleoflong_inject
  (* eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject *)
  Val.neg_inject Val.negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject Val.mul_inject Val.mull_inject Val.mulhs_inject Val.mulhu_inject
  Val.mullhs_inject Val.mullhu_inject Val.shr_inject Val.shrl_inject Val.or_inject Val.orl_inject
  Val.xor_inject Val.xorl_inject Val.and_inject Val.andl_inject Val.notl_inject
  Val.shl_inject Val.shll_inject Val.vzero_inject Val.notint_inject
  Val.shru_inject Val.shrlu_inject Val.ror_inject Val.rorl_inject
  cmp_inject cmpu_inject cmplu_lessdef cmpl_inject cmpf_inject cmpfs_inject
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef (* eval_testcond_inject *) Val.offset_ptr_inject
  divs_inject divls_inject divu_inject divlu_inject
  mods_inject modu_inject modls_inject modlu_inject
  get0w_inject get0l_inject
  Val.maketotal_inject
  intuofsingle_inject singleofintu_inject longuoffloat_inject longuofsingle_inject singleoflongu_inject intuoffloat_inject floatofintu_inject floatoflongu_inject
  inject_symbol_address : inject_db.


Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
      reflexivity
  end.

Ltac solve_match_states :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ |- exists _, _ ] => eexists; solve_match_states
  | [ |- Next _ _ = Next _ _ /\ match_states _ _ ] =>
    split; [reflexivity | econstructor; eauto; solve_match_states]
  | [ |- (exec_instr _ _ _ _ = Next _ _) /\ match_states _ _ ] =>
    split; [simpl; solve_exec_instr | econstructor; eauto; solve_match_states]
  | [ |- regset_inject _ _ _ ] =>
    eauto 10 with inject_db
  end.




Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i ofs f b
                        (INJ : j = Mem.flat_inj (Mem.support m1))
                        (MINJ: magree j m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr instr_size (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsmArchi.exec_instr instr_size ge i rs1 m1 = Next rs1' m1' ->
    exists rs2' m2',
      exec_instr instr_size tge i rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros.
  destruct i; inv H2; simpl in *;
    try first [solve_store_load | solve_match_states].
  
  eapply regset_inject_expand;eauto.
  eapply inject_symbol_address. eauto.
  
  repeat eapply regset_inject_expand;eauto.
  eapply inject_symbol_address. eauto.

  eapply Val.offset_ptr_inject. eauto.
Qed.


Lemma prog_main_eq: AST.prog_main prog = prog_main tprog.
Proof.
  unfold match_prog,transf_program in *.
  repeat destr_in TRANSF.
  simpl. auto.
Qed.


Lemma initial_state_gen_pres_match: forall m0 m0' m1 rs0 rs
    (INIT: Genv.init_mem prog = Some m0)
    (INIT': init_mem instr_size tprog = Some m0'),
    magree (Mem.flat_inj (Mem.support m0)) m0 m0' ->
    RealAsmArchi.initial_stack_regset prog m0 m1 rs0 ->
    exists st, initial_state_gen instr_size tprog rs m0' st /\ match_states (State rs0 m1) st.
Proof.
  intros. inv H0.
  (* regset *)
  set (rs1' := Pregmap.set X1 Vnullptr
                 (Pregmap.set X2 Vnullptr
                    (Pregmap.set PC (Genv.symbol_address tge (AST.prog_main prog) Ptrofs.zero)
                       (Pregmap.init Vundef)))).
  exists (State rs1' m0').
  split.
  - unfold rs1'. unfold tge.
    erewrite -> prog_main_eq. econstructor.
  - econstructor;eauto.
    + exploit init_meminj_match_sminj;eauto.
    + unfold rs1,rs1'. repeat apply regset_inject_expand;eauto.
      unfold regset_inject. intros. unfold Pregmap.init. econstructor.
      eapply inject_symbol_address.
      exploit init_meminj_match_sminj;eauto.
      unfold Vnullptr. destr;eauto.
      unfold Vnullptr. destr;eauto.
    + unfold Symbtablegenproof.glob_block_valid. intros.      
      exploit (Genv.find_def_not_fresh). apply INIT. apply H0. auto.
Qed.



Let agree_inj_instrs := agree_inj_instrs instr_size prog tprog.
Let agree_inj_int_funct := agree_inj_int_funct instr_size prog tprog.
Let inject_pres_match_sminj := inject_pres_match_sminj instr_size prog tprog.

Theorem step_simulation:
  forall S1 t S2,
    RealAsmArchi.step instr_size ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      step instr_size tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.
  -  (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instrs (Mem.flat_inj (Mem.support m)) MATCHINJ b b2 f ofs delta i); eauto.
    intros FIND.
    exploit (exec_instr_step (Mem.flat_inj (Mem.support m)) rs rs'0 m m'0 rs' m' i); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply exec_step_internal; eauto.

  - (* External call *)
    exploit extcall_arguments_inject;eauto.
    intros (args' & INJLIST & EXTARGS').
    exploit external_call_inject;eauto.
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP & INJ). subst.
    
    set (rs'1 :=  (Pregmap.set PC (rs'0 X1)
                     (set_pair (loc_external_result (ef_sig ef)) res' (undef_caller_save_regs rs'0)))).
    exists (State rs'1 m2'').
    split.
    + assert (rs'0 PC = Vptr b Ptrofs.zero).
      unfold regset_inject in RSINJ. generalize (RSINJ PC).
      rewrite H. intros. inv H3. unfold Mem.flat_inj in H7. destr_in H7.
      inv H7. rewrite Ptrofs.add_zero_l. auto.
      
      eapply exec_step_external;eauto.
      * eapply agree_inj_ext_funct;eauto.
        unfold Symbtablegenproof.glob_block_valid in GBVALID.
        generalize (GBVALID b (Gfun (External ef))). intros.
        unfold Genv.find_funct_ptr in H0. repeat destr_in H0.
        unfold ge in Heqo. apply H4 in Heqo.
        unfold Mem.flat_inj. unfold Mem.valid_block in Heqo.
        destr.
      * assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
        { eapply transf_prog_pres_senv; eauto. }
        rewrite <- SENVEQ. eauto.
      * eauto.
    + econstructor;eauto.
      * unfold rs'1. eapply regset_inject_expand;eauto.
        eapply set_pair_pres_inject;eauto.
        unfold regset_inject. intros.
        eapply val_inject_undef_caller_save_regs. eauto.
      * eapply extcall_pres_glob_block_valid; eauto.     
Qed.



(** ** Matching of the Final States*)
Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ X10). rewrite H0.
    inversion 1. auto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.
