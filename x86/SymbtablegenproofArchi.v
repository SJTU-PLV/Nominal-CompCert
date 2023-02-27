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
  
(* injection lemmas dependent to architures *)
Lemma compare_ints_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_ints v1 v2 rs m) (compare_ints v1' v2' rs' m').
Proof.
  intros. unfold compare_ints, Asm.compare_ints.
  repeat apply regset_inject_expand; auto.
  - apply cmpu_inject; auto.
  - apply cmpu_inject; auto.
  - apply val_negative_inject. apply Val.sub_inject; auto.
  - apply sub_overflow_inject; auto.
Qed.

Lemma compare_longs_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    magree j m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
Proof.
  intros. unfold compare_longs, Asm.compare_longs.
  repeat apply regset_inject_expand; auto.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Ceq); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Clt); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply Val.vofbool_inject.
  - apply val_negativel_inject. apply Val.subl_inject; auto.
  - apply subl_overflow_inject; auto.
Qed.


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


(** Properties of executing addrmode, load, store and etc. *)

Section PRESERVATION.
  
(** Transformation *)
Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv instr_size tprog.

Hypothesis TRANSF: match_prog instr_size prog tprog.

Let match_inj := match_inj instr_size prog tprog.

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


Let glob_block_valid := glob_block_valid prog.
Let match_states := match_states instr_size prog tprog.

Lemma exec_load_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk rd a
                          (INJ: j = Mem.flat_inj (Mem.support m1))
                          (MINJ: magree j  m1 m2)
                          (MATCHINJ: match_inj j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1), 
    Asm.exec_load ge sz chunk m1 a rs1 rd = Next rs1' m1' ->
    exists rs2' m2',
      exec_load sz tge chunk m2 a rs2 rd = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.loadv chunk m1 (Asm.eval_addrmode ge a rs1)) eqn:MLOAD; try congruence.
  exploit loadv_inject; eauto. intros (v2 & MLOADV & VINJ).
  eexists. eexists. split.
  - unfold exec_load. rewrite MLOADV. auto.
  - inv H. eapply match_states_intro; eauto.
    apply nextinstr_pres_inject.
    apply undef_regs_pres_inject.
    apply regset_inject_expand; eauto.
Qed.


Lemma store_pres_glob_block_valid : forall m1 chunk b v ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid, Symbtablegenproof.glob_block_valid in *. intros.  
  eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma storev_pres_glob_block_valid : forall m1 chunk ptr v m2,
  Mem.storev chunk m1 ptr v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold Mem.storev. intros. destruct ptr; try congruence.
  eapply store_pres_glob_block_valid; eauto.
Qed.

Lemma exec_store_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk r a dregs
                         (INJ: j = Mem.flat_inj (Mem.support m1))
                         (MINJ: magree j m1 m2)
                         (MATCHINJ: match_inj j)
                         (RSINJ: regset_inject j rs1 rs2)
                         (GBVALID: glob_block_valid m1),
    Asm.exec_store ge sz chunk m1 a rs1 r dregs = Next rs1' m1' ->
    exists rs2' m2',
      exec_store sz tge chunk m2 a rs2 r dregs = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.storev chunk m1 (Asm.eval_addrmode ge a rs1) (rs1 r)) eqn:MSTORE; try congruence.
  exploit storev_mapped_inject; eauto. intros (m2' & MSTOREV & MINJ').
  exploit (Mem.support_storev). apply MSTORE. intros SUP.
  eexists. eexists. split.
  - unfold exec_store. rewrite MSTOREV. auto.
  - inv H. eapply match_states_intro; eauto.
    rewrite <- SUP. auto.
    rewrite <- SUP. auto.
    (* erewrite <- storev_pres_def_frame_inj; eauto. *)
    apply nextinstr_pres_inject. repeat apply undef_regs_pres_inject.
    rewrite <- SUP. auto.
    eapply storev_pres_glob_block_valid; eauto.
Qed.

Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    Val.opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.



Hint Resolve nextinstr_nf_pres_inject nextinstr_pres_inject regset_inject_expand
  regset_inject_expand_vundef_left undef_regs_pres_inject
  Val.zero_ext_inject Val.sign_ext_inject Val.longofintu_inject Val.longofint_inject
  Val.singleoffloat_inject Val.loword_inject Val.floatofsingle_inject Val.intoffloat_inject Val.maketotal_inject
  Val.intoffloat_inject Val.floatofint_inject Val.intofsingle_inject Val.singleofint_inject
  Val.longoffloat_inject Val.floatoflong_inject Val.longofsingle_inject Val.singleoflong_inject
  eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject
  Val.neg_inject Val.negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject Val.mul_inject Val.mull_inject Val.mulhs_inject Val.mulhu_inject
  Val.mullhs_inject Val.mullhu_inject Val.shr_inject Val.shrl_inject Val.or_inject Val.orl_inject
  Val.xor_inject Val.xorl_inject Val.and_inject Val.andl_inject Val.notl_inject
  Val.shl_inject Val.shll_inject Val.vzero_inject Val.notint_inject
  Val.shru_inject Val.shrlu_inject Val.ror_inject Val.rorl_inject
  compare_ints_inject compare_longs_inject compare_floats_inject compare_floats32_inject
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef eval_testcond_inject Val.offset_ptr_inject: inject_db.

Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
    reflexivity
  | [ |- context [eval_testcond _ _] ]=>
    unfold eval_testcond; solve_exec_instr
  | [ H: Asm.eval_testcond ?c ?r = _ |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite H; solve_exec_instr
  | [ H: _ = Asm.eval_testcond ?c ?r |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite <- H; solve_exec_instr
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

Ltac destr_eval_testcond :=
  match goal with
  | [ H : match Asm.eval_testcond ?c ?rs with | _ => _ end = Next _ _ |- _ ] =>
    let ETEQ := fresh "ETEQ" in (
      destruct (Asm.eval_testcond c rs) eqn:ETEQ); destr_eval_testcond
  | [ H : Some ?b = Asm.eval_testcond _ _ |- _ ] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.eval_testcond _ _ = Some ?b |- _] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.Next _ _ = Next _ _ |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some true) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some false) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | _ => idtac
  end.

Ltac destr_match_outcome :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ H: Asm.Next _ _ = Next _ _ |- _ ] => inv H; destr_match_outcome
  | [ H: match ?a with _ => _ end = Next _ _ |- _] =>
    let EQ := fresh "EQ" in (destruct a eqn:EQ; destr_match_outcome)
  | _ => idtac
  end.


Lemma goto_ofs_pres_mem : forall f l rs1 m1 rs1' m1',
    Asm.goto_ofs ge f l rs1 m1 = Next rs1' m1' -> m1 = m1'.
Proof.
  unfold Asm.goto_label. intros.
  unfold Asm.goto_ofs in H. 
  repeat destr_in H.
Qed.

Lemma goto_ofs_inject : forall rs1 rs2 f l j m1 m2 rs1' m1'
                            (RINJ: regset_inject j rs1 rs2),
    Asm.goto_ofs ge f l rs1 m1 = Next rs1' m1' ->
    exists rs2', goto_ofs f l rs2 m2 = Next rs2' m2 /\
            regset_inject j rs1' rs2'.
Proof.
  intros. unfold Asm.goto_ofs in H.
  destr_in H. destr_in H. inv H.
  unfold goto_ofs.
  generalize (RINJ PC). rewrite Heqv.
  intros NJ. inv NJ.
  eexists; split; eauto.
  apply regset_inject_expand; auto.
  eapply Val.inject_ptr; eauto.
  repeat rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut.
  repeat rewrite Ptrofs.add_assoc.
  auto.
Qed.

Local Open Scope asm.
Lemma goto_ofs_inject' : forall l f j rs1 rs2 m1 m2 rs1' m1'
                                (RINJ: regset_inject j rs1 rs2),
    Asm.goto_ofs ge f l ((rs1 # RAX <- Vundef) # RDX <- Vundef) m1 = Next rs1' m1' ->
    exists rs2',
      goto_ofs f l ((rs2 # RAX <- Vundef) # RDX <- Vundef) m2 = Next rs2' m2 /\
      regset_inject j rs1' rs2'.
Proof.
  intros. 
  eapply goto_ofs_inject; eauto.
  repeat apply regset_inject_expand; auto.
Qed.

Lemma extcall_pres_glob_block_valid : forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid,Symbtablegenproof.glob_block_valid in *. intros.
  eapply external_call_valid_block; eauto.
Qed.

(* TODO: it is architechture specific, we should move it to architechture directory *)
(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i ofs f b
                        (INJ : j = Mem.flat_inj (Mem.support m1))
                        (MINJ: magree j m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr instr_size (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsmArchi.exec_instr instr_size ge f i rs1 m1 = Next rs1' m1' ->
    exists rs2' m2',
      exec_instr instr_size tge i rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.

  intros.
  destruct i; inv H2; simpl in *;
    try first [solve_store_load |
               solve_match_states].

  - (* Pmov_rs *)
    apply nextinstr_nf_pres_inject.
    apply regset_inject_expand; auto.
    inv MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address.
    destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
    exploit agree_inj_globs; eauto.
    intros (b1 & ofs1 & GLBL & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  (* Divisions *)
  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.
     
  - (* Pcmov *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1')) c rs1 rs2); eauto.
    intros. inv H2.
    destr_eval_testcond; try solve_match_states.
    (* destruct (Asm.eval_testcond c rs2) eqn:EQ'. destruct b0; solve_match_states. *)
    (* solve_match_states. *)
    destruct v;solve_match_states.
    
    
  - (* Pjmp_l *)
    assert (instr_valid (Pjmp_l l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pjmp_s *)
    repeat destr_in H4.    
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address. destr_match; auto.
    exploit (agree_inj_globs symb b0); eauto.
    intros (b1 & ofs1 & LBLOFS & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  - (* Pjmp_r *)
    repeat destr_in H4.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
      
  - (* Pjcc *)
    assert (instr_valid (Pjcc c l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
    
  - (* Pjcc2 *)
    assert (instr_valid (Pjcc2 c1 c2 l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pjmptbl *)
    assert (instr_valid (Pjmptbl r tbl)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pcall_s *)
    repeat destr_in H4.
    generalize (RSINJ PC).
    (* support after storev *)
    exploit (Mem.support_storev). eapply Heqo. intros SUPEQ.
    rewrite SUPEQ in *.
    edestruct storev_mapped_inject as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    (* destruct ros; simpl; repeat apply regset_inject_expand; auto. *)
    exploit (inject_symbol_address). eapply MATCHSMINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.
    
  - (* Pcall_r *)
    repeat destr_in H4.
    generalize (RSINJ PC).
    (* support after storev *)
    exploit (Mem.support_storev). eapply Heqo. intros SUPEQ.
    rewrite SUPEQ in *.
    edestruct storev_mapped_inject as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.
    
  - (* Pret *)
    repeat destr_in H4. simpl.
    unfold loadvv in *. destr_in Heqo. 
    exploit loadv_inject;eauto. intros (v2 & LD & VI). rewrite LD.
    destr_in Heqo;inv Heqo;inv VI;
    eexists _, _; split; eauto;
    econstructor; eauto;
    repeat apply regset_inject_expand; auto;
    try apply Val.offset_ptr_inject; eauto.
    
  - (* Pallocframe *)
    assert (instr_valid (Pallocframe sz ofs_ra ofs_link)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pfreeframe *)
    assert (instr_valid (Pfreeframe sz ofs_ra ofs_link)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
    
  - (* Pjmp_l_rel *)
    unfold Asm.goto_ofs in H4.
    destruct (rs1 Asm.PC) eqn:PC1; inv H4.
    destruct (Globalenvs.Genv.find_funct_ptr ge b0); inv H3.
    generalize (RSINJ PC). rewrite PC1.
    intros INJ. inv INJ. eauto.
    eexists; eexists. split.
    unfold goto_ofs.
    rewrite <- H4. eauto.
    eapply match_states_intro; eauto.
    apply regset_inject_expand; auto.
    rewrite H in *. inv PC1. inv H.
    eapply Val.inject_ptr; eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    match goal with
    | [ |- _ = Ptrofs.add _ (Ptrofs.add ?b ?c) ] =>
      rewrite (Ptrofs.add_commut b c)
    end.
    match goal with
    | [ |- _ = Ptrofs.add ?a ?b ] =>
      rewrite (Ptrofs.add_commut a b)
    end.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    
  - (* Pjcc_rel *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_ofs_pres_mem; eauto. intros. subst.
    generalize (goto_ofs_inject _ _ _ _ _ m1' m2 _ _ RSINJ H4).
    intros (rs2' & GOTO & RINJ').
    exists rs2', m2. split; auto.
    eapply match_states_intro; eauto.

  - (* Pjcc2_rel *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c1 rs1 rs2); eauto.
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c2 rs1 rs2); eauto.
    intros ELF1 ELF2.
    destr_eval_testcond; try solve_match_states.
    exploit goto_ofs_pres_mem; eauto. intros. subst.
    generalize (goto_ofs_inject _ _ _ _ _ m1' m2 _ _ RSINJ H4).
    intros (rs2' & GOTO & RINJ').
    exists rs2', m2. split; auto.
    eapply match_states_intro; eauto.

  - (* Pjmptbl_rel *)
    assert (instr_valid (Pjmptbl_rel r tbl)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
(***** Remove Proofs By Chris Start ******)
(*       *)
(*     destruct (rs1 r) eqn:REQ; inv H4. *)
(*     destruct (list_nth_z tbl (Int.unsigned i)) eqn:LEQ; inv H3. *)
(*     assert (rs2 r = Vint i) by *)
(*         (generalize (RSINJ r); rewrite REQ; inversion 1; auto). *)
(*     exploit goto_ofs_pres_mem; eauto. intros. subst. *)
(*     generalize (goto_ofs_inject' _ _ _ _ _ m1' m2 _ _ RSINJ H4). *)
(*     intros (rs2' & GLBL & RSINJ'). *)
(*     exists rs2', m2. rewrite H2. rewrite LEQ. *)
(*     split; auto. *)
(*     eapply match_states_intro; eauto. *)
(* *)
(***** Remove Proofs By Chris End ******)
Qed.

(* copy from SSAsmproof.v *)
Lemma val_inject_undef_caller_save_regs:
  forall j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    r,
    Val.inject j (undef_caller_save_regs rs1 r) (undef_caller_save_regs rs2 r).
Proof.
  intros; eauto.
  unfold undef_caller_save_regs.
  destruct (preg_eq r SP); destruct (in_dec preg_eq r (map preg_of (filter Conventions1.is_callee_save Machregs.all_mregs))); simpl; try (apply RINJ).
  eauto.
Qed.

Let alloc_stack_pres_inject := alloc_stack_pres_inject instr_size instr_size_bound prog tprog TRANSF.
Let storev_pres_match_inj := storev_pres_match_inj instr_size prog tprog.

Lemma initial_state_gen_pres_inject: forall m0 m0' m1 rs0 rs
    (INIT: Genv.init_mem prog = Some m0)
    (INIT': init_mem instr_size tprog = Some m0'),
    magree (Mem.flat_inj (Mem.support m0)) m0 m0' ->
    RealAsmArchi.initial_stack_regset prog m0 m1 rs0 ->
    exists st, initial_state_gen instr_size tprog rs m0' st.
Proof.
  intros. inv H0.
  exploit (Mem.valid_new_block m0);eauto. unfold Mem.valid_block. intros VALIDSTK.
  caseEq (Mem.alloc m0' 0 (max_stacksize + align (size_chunk Mptr) 8)).
  intros m1'  stk'  H0'.
  exploit (alloc_stack_pres_inject  m0 m0');eauto.
  intros (MINJ1 &  STK &  MATINJ1). subst.  
  exploit (storev_pres_match_inj Mptr m2 m1);eauto.
  intros MATINJ2.
  edestruct storev_pres_inject as (m2' & ST & SMINJ). apply H2. apply MINJ1. econstructor. econstructor.
  (* stk' is valid *)
  unfold Mem.flat_inj. destruct (Mem.sup_dec stk' (Mem.support m2)).
  eauto. congruence.
  eapply eq_refl. constructor.
  (* regset *)
  set (rs0' := rs # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk' (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.

  (* instantiate the initial state*)
  exists (State rs0' m2').
  econstructor;eauto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.
