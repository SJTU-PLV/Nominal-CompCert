Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen SymbtablegenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics.
Require Import LocalLib AsmInject.
Import ListNotations.
Require Import AsmFacts MemoryAgree.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  

Lemma prog_instr_valid: forall prog tprog,
    transf_program instr_size prog = OK tprog ->
    Forall def_instrs_valid (map snd (AST.prog_defs prog)).
Proof.
  intros prog tprog TRANSF.
  unfold transf_program in TRANSF.
  destr_in TRANSF.
  inv w. auto.
Qed.

(* TODEL *)
Lemma int_funct_instr_valid: forall prog tprog f b,
    transf_program instr_size prog = OK tprog ->
    Globalenvs.Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
    Forall instr_valid (Asm.fn_code f).
Proof.
  intros prog tprog f b TF FIND.
  generalize (prog_instr_valid _ _ TF).
  intros NJ.
  generalize (Genv.find_funct_ptr_inversion _ _ FIND).
  intros (id, IN).
  generalize (in_map snd _ _ IN).
  cbn. intros IN'.
  rewrite Forall_forall in NJ.
  apply NJ in IN'.
  red in IN'. auto.
Qed.

(* TODEL *)
Lemma instr_is_valid: forall prog tprog f b i ofs,
    transf_program instr_size prog = OK tprog ->
    Globalenvs.Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
    Asm.find_instr instr_size ofs (Asm.fn_code f) = Some i ->
    instr_valid i.
Proof.
  intros prog tprog f b i ofs TF FIND FIND'.
  generalize (int_funct_instr_valid _ _ _ _ TF FIND).
  intros NJ.
  rewrite Forall_forall in NJ.
  auto. 
  apply NJ. 
  eapply Asmgenproof0.find_instr_in; eauto.
Qed.


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


(* dependent to x86 *)
Lemma eval_addrmode32_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode32 ge a rs1) (eval_addrmode32 tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode32, eval_addrmode32.
  destruct a. 
  destruct base, ofs, const; simpl in *. 
  - destruct p. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
  - destruct p,p0. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. apply Val.add_inject; auto. 
    inject_match. apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.
    (* 32bit need the following proof *)
    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if. auto. *)
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.

    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if. auto. *)
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p,p0.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.

    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. 
    inject_match. inject_match.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.    
    destr_valinj_left H1;inv H1; auto.

    destr_valinj_left H1;inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.

    destruct Archi.ptr64 eqn:PTR.    
    destr_valinj_left H1; inv H1; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.   

        
Qed.

    (* destr_pair_if. auto. *)
    (* eapply Val.inject_ptr; eauto. *)
    (* repeat unfold Ptrofs.of_int.  *)
    (* repeat rewrite Int.unsigned_zero.  *)
    (* repeat rewrite Ptrofs.add_zero. auto. *)
    (* destr_valinj_left H1; inv H1; auto. *)
    (* destr_pair_if. auto. *)
    (* eapply Val.inject_ptr; eauto. *)
    (* repeat unfold Ptrofs.of_int.  *)
    (* repeat rewrite Int.unsigned_zero.  *)
    (* repeat rewrite Ptrofs.add_zero. auto. *)   

Lemma eval_addrmode64_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode64 ge a rs1) (eval_addrmode64 tge a rs2).
Proof.
  intros. 
  destruct a. 
  destruct base, ofs, const; simpl in *.
  - destruct p. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.

    apply Val.mull_inject; auto.
  - destruct p,p0. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.addl_inject; auto.
  - destruct p. apply Val.addl_inject; auto.
    inject_match.
    (* dependent in ptr64 !! try to fix it !!!*)
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - destruct p.
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - destruct p,p0.
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - repeat apply Val.addl_inject; auto.
  - destruct p. inject_match. inject_match.
    apply inject_symbol_address; auto.
    * destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
    *  destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
Qed.

Lemma eval_addrmode_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode ge a rs1) (eval_addrmode tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode, eval_addrmode. destruct Archi.ptr64.
  + eapply eval_addrmode64_inject; eauto.
  + eapply eval_addrmode32_inject; eauto.
Qed.


End WITH_INSTR_SIZE.



