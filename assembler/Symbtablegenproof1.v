Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen SymbtablegenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics.
Require Import RelocProgSemanticsArchi.
Require Import LocalLib AsmInject.
Require Import  RelocProgGlobalenvs MemoryAgree.
Require Import Symbtablegenproof SymbtablegenproofArchi.
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


Let match_states := match_states instr_size prog tprog.
Let init_mem_pres_inject := init_mem_pres_inject instr_size instr_size_bound prog tprog TRANSF.
(* set hypothesis *)
Lemma transf_initial_states : forall rs st1,
    RealAsm.initial_state prog st1 ->
    exists st2, initial_state instr_size tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs st1 INIT.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF. 2: congruence. destr_in TRANSF'. 
  inv INIT.
  exploit (init_mem_pres_inject m0);eauto.
  intros (m0' & INITM' & MINJ).
  (* exploit (Mem.alloc_parallel_inject (Mem.flat_inj (Mem.support m0)) *)
  (*              m0 m0' 0 (max_stacksize + align (size_chunk Mptr) 8) *)
  (*              m1 stk 0 (max_stacksize + align (size_chunk Mptr) 8));eauto;try lia. *)
  (*** TODO  *)
  exploit (Mem.valid_new_block m0);eauto. unfold Mem.valid_block. intros VALIDSTK.
  caseEq (Mem.alloc m0' 0 (max_stacksize + align (size_chunk Mptr) 8)).
  intros m1'  stk'  H0'.
  exploit (alloc_stack_pres_inject m0 m0');eauto.
  intros (MINJ1 &  STK &  MATINJ1). subst.  
  exploit (storev_pres_match_inj Mptr m1 m2);eauto.
  intros MATINJ2.
  edestruct storev_pres_inject as (m2' & ST & SMINJ). apply H1. apply MINJ1. econstructor. econstructor.
  (* stk' is valid *)
  unfold Mem.flat_inj. destruct (Mem.sup_dec stk' (Mem.support m1)).
  eauto. congruence.
  eapply eq_refl. constructor.
  (* regset *)
  set (rs0' := rs # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk' (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.

  (* instantiate the initial state*)
  exists (State rs0' m2').
  split. 
  (* initial_state *)
  - econstructor;eauto.
    econstructor;eauto.
  - econstructor;eauto.
    unfold regset_inject. intros.
    
    unfold rs0',rs0.
    apply val_inject_set.
    apply val_inject_set.
    apply val_inject_set.
    auto.
      (* main function *)
      destr_in TRANSF'. simpl.
     exploit (agree_inj_globs (Mem.flat_inj (Mem.support m2)) MATINJ2 ((AST.prog_main prog)) bmain). auto.
     intros (bmain' & ofs' & MAIN' & MAININJ).
     (* proof bmain is valid in m2 support *)
     exploit (Genv.find_symbol_not_fresh). apply H. apply H2. intros VALIDMAIN0.
     exploit (Mem.valid_block_alloc). apply H0. apply VALIDMAIN0. intros VALIDMAIN1.
     exploit (Mem.support_store). apply H1. intros SUPEQ.
     unfold Mem.valid_block in VALIDMAIN1.
     rewrite <- SUPEQ in VALIDMAIN1. unfold Mem.flat_inj in MAININJ.
     destruct (Mem.sup_dec bmain (Mem.support m2));try congruence.
     destr_in MAININJ.
     unfold Genv.symbol_address.
     rewrite MAIN'. econstructor.
     unfold Mem.flat_inj. destruct (Mem.sup_dec bmain' (Mem.support m2));try congruence. eauto.
     rewrite Ptrofs.add_unsigned. rewrite Ptrofs.add_zero.
     rewrite <- H6. rewrite Z.add_0_r. rewrite Ptrofs.unsigned_zero. auto.
     constructor.
     cbn [Val.offset_ptr].
     rewrite Ptrofs.sub_add_opp.
     econstructor.
     (* prove SSAsm.stkblock = stk' = stk *)
     exploit (Genv.init_mem_stack). eapply H. intros.
     exploit (init_mem_stack). eapply INITM'. intros.
     assert (stk' = SSAsm.stkblock).
     exploit Mem.alloc_result. eapply H0.
     unfold Mem.nextblock. unfold Mem.fresh_block. rewrite H3.
     simpl. intros. rewrite H5. unfold SSAsm.stkblock. auto.
     (* prove stk' in support m2 *)
     rewrite <- H5.
     exploit Mem.support_storev. apply H1. intros.
     rewrite <- H6. unfold Mem.flat_inj.
     destruct Mem.sup_dec. eauto.
     congruence.
     rewrite Ptrofs.add_zero. auto.
     (* glob block valid *)
     
     unfold glob_block_valid. intros.
     exploit (Genv.find_def_not_fresh). apply H. apply H3.
     unfold Mem.valid_block. intros.
     exploit Mem.support_alloc. apply H0. 
     exploit Mem.support_storev. apply H1.
     intros. rewrite <- H5. rewrite H6.
     exploit Mem.sup_include_incr. apply H4. auto.
Qed.


Theorem step_simulation:
  forall S1 t S2,
    RealAsm.step instr_size ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      step instr_size tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instrs (Mem.flat_inj (Mem.support m)) MATCHINJ b b2 f ofs delta i); eauto.
    intros FIND.
    exploit (exec_instr_step (Mem.flat_inj (Mem.support m)) rs rs'0 m m'0 rs' m' i); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply exec_step_internal; eauto.
    eapply (agree_inj_int_funct (Mem.flat_inj (Mem.support m)) MATCHINJ); eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instrs (Mem.flat_inj (Mem.support m)) MATCHINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros FIND.
    exploit (eval_builtin_args_inject (Mem.flat_inj (Mem.support m)) m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    exploit (external_call_inject ge (Mem.flat_inj (Mem.support m)) vargs vargs' m m'0 m' vres t ef);eauto.
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP & INJ).
    set (rs' := nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                             (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0))).
    exploit (fun b ofs => exec_step_builtin instr_size tge b ofs
                                         ef args res rs'0  m'0 vargs' t vres2 rs' m2'); eauto. 
    eapply (agree_inj_int_funct (Mem.flat_inj (Mem.support m)) MATCHINJ); eauto.
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj (Mem.flat_inj (Mem.support m))); eauto.
    + subst rs'. intros. 
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (fun h => set_res_pres_inject res j' 
                  rs1 rs2 h vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      eapply nextinstr_nf_pres_inject. auto.
      (* eauto with inject_db. *)
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    exploit loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    exploit (external_call_inject ge (Mem.flat_inj (Mem.support m)) args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP & INJ).
    exploit (fun ofs => exec_step_external instr_size tge b2 ofs ef args2 res'); eauto.
    eapply agree_inj_ext_funct; eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj (Mem.flat_inj (Mem.support m))); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        (* set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *. *)
        (* generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros. *)
        (* set (rs1 := (Asm.undef_regs dregs rs)) in *. *)
        (* set (rs2 := (Asm.undef_regs dregs rs'0)) in *. *)
        (* set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *. *)
        (* generalize (undef_regs_pres_inject j' rs1 rs2 cdregs). intros. *)
        (* set (rs3 := (Asm.undef_regs cdregs rs1)) in *. *)
        (* set (rs4 := (Asm.undef_regs cdregs rs2)) in *. *)
        (* generalize (set_pair_pres_inject j' rs3 rs4 res res'  *)
        (*                                  (Asm.loc_external_result (ef_sig ef))). *)
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        eapply set_pair_pres_inject.
        unfold regset_inject.
        eapply val_inject_undef_caller_save_regs.
        auto. auto.
        eapply val_inject_incr; eauto.
        apply Val.offset_ptr_inject; eauto.
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
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.

(** ** The Main Correctness Theorem *)
Lemma transf_program_correct:
  forward_simulation (RealAsm.semantics instr_size prog) 
                     (semantics instr_size tprog (Pregmap.init Vundef)).
Proof.
  intros. apply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF. cbn.
    auto.
    (* rewrite add_external_globals_pres_senv. cbn. auto. *)
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    (* intros. *)
    (* rewrite Pregmap.gi. auto. *)
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.

Instance symbtablegen_transflink (instr_size: instruction -> Z):
  TransfLink (match_prog instr_size).
Admitted.
