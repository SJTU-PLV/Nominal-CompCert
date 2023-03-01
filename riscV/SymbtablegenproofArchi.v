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


Lemma get0w_inject : forall rs1 rs2 r j,
    regset_inject j rs1 rs2 ->
    Val.inject j (get0w rs1 r) (get0w rs2 r).
Proof.
  intros. unfold get0w.
  destruct r;auto.
Qed.


Lemma get0l_inject : forall rs1 rs2 r j,
    regset_inject j rs1 rs2 ->
    Val.inject j (get0l rs1 r) (get0l rs2 r).
Proof.
  intros. unfold get0l.
  destruct r;auto.
Qed.

  
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
                                 


Lemma cmp_inject : forall v1 v2 v1' v2' c j,
    Val.inject j v1 v1' ->
    Val.inject j v2 v2' ->
    Val.inject j (Val.cmp c v1 v2) (Val.cmp c v1' v2').
Proof. 
  intros.
  unfold Val.cmp.
  unfold Val.of_optbool. destr.
  exploit Val.cmp_bool_inject. eapply H. eapply H0. eapply Heqo.
  intros.
  rewrite H1.
  unfold Vtrue, Vfalse.
  destruct b;eauto. eauto.
Qed.

(* Lemma cmpu_inject : forall v1 v2 v1' v2' c j, *)
(*     Val.inject j v1 v1' -> *)
(*     Val.inject j v2 v2' -> *)
(*     Val.inject j (Val.cmpu c v1 v2) (Val.cmpu c v1' v2'). *)
(* Proof.  *)
(*   intros. *)
(*   unfold Val.cmpu. *)
(*   unfold Val.of_optbool. destr. *)
(*   exploit Val.cmpu_bool_inject. eapply H. eapply H0. eapply Heqo. *)
(*   intros. *)
(*   rewrite H1. *)
(*   unfold Vtrue, Vfalse. *)
(*   destruct b;eauto with inject_db. eauto with inject_db. *)
(* Qed. *)


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
  cmp_inject cmpu_inject cmplu_lessdef
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef (* eval_testcond_inject *) Val.offset_ptr_inject
  get0w_inject get0l_inject
  Val.maketotal_inject : inject_db.


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
    try first [ solve_match_states].
  Val.opt_val_inject
  
  eapply regset_inject_expand. eapply regset_inject_expand. auto.
  unfold Val.cmpu.  unfold Val.of_optbool.
  destr.
  cmpu_inject
  Val.of_optbool_lessdef
    
  Val.cmp_bool_inject
  
  destruct i;simpl in *.
  do 2 eexists. split;eauto. inv H2.
  econstructor;eauto.

  eapply regset_inject_expand. eapply regset_inject_expand;auto.
  
