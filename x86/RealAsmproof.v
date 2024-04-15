Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import AsmFacts.
Require Import SSAsm RealAsm RealAsmgen.
Require Import AsmRegs.
Require Import Errors.
Require Import Linking.

  Section PRESERVATION.

  Variable prog: Asm.program.
  Variable instr_size: instruction -> Z.
  Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
  Let ge := Genv.globalenv prog.

  Definition pc_at (s: state): option ((function * instruction) + external_function) :=
    let '(State rs m) := s in
    match rs PC with
    | Vptr b o =>
      match Genv.find_funct_ptr ge b with
      | Some (Internal f) =>
        match find_instr instr_size (Ptrofs.unsigned o) (fn_code f) with
        | Some i => Some (inl (f,i))
        | None => None
        end
      | Some (External ef) => Some (inr ef)
      | None => None
      end
    | _ => None
    end.

  Inductive seq: state -> state -> Prop :=
  | seq_intro rs1 rs2 m (REQ: forall r, r <> RA -> rs1 r = rs2 r): seq (State rs1 m) (State rs2 m).

  Inductive match_states: state -> state -> Prop :=
  | match_states_call_alloc
      (rs1 rs2: regset) m1 m2
      (REQ: forall r : preg, r <> RSP -> r <> RA -> rs1 r = rs2 r)
      (RRSP: rs1 RSP = Val.offset_ptr (rs2 RSP) (Ptrofs.repr (size_chunk Mptr)))
      (MEQ: Mem.storev Mptr m1 (rs2 RSP) (rs1 RA) = Some m2)
      f ialloc
      (PC1: pc_at (State rs1 m1) = Some (inl (f,ialloc)))
      (ALLOC: is_alloc ialloc):
      match_states (State rs1 m1) (State rs2 m2)
  | match_states_call_external
      (rs1 rs2: regset) m1 m2
      (REQ: forall r : preg, r <> RSP -> r <> RA -> rs1 r = rs2 r)
      (RRSP: rs1 RSP = Val.offset_ptr (rs2 RSP) (Ptrofs.repr (size_chunk Mptr)))
      (MEQ: Mem.storev Mptr m1 (rs2 RSP) (rs1 RA) = Some m2)
      ef
      (PC1: pc_at (State rs1 m1) = Some (inr ef)):
      match_states (State rs1 m1) (State rs2 m2)
  | match_states_free_ret
      (rs1 rs2: regset) m
      (REQ: forall r : preg, r <> RSP -> r <> RA -> rs1 r = rs2 r)
      (RRSP: rs1 RSP = Val.offset_ptr (rs2 RSP) ((Ptrofs.repr (size_chunk Mptr))))
      (LOADRA: loadvv Mptr m (rs2 RSP) = Some (rs1 RA))
      f
      (PC1: pc_at (State rs1 m) = Some (inl (f,Pret))):
      match_states (State rs1 m) (State rs2 m)
  | match_states_free_jmp
      (rs1 rs2: regset) m
      (REQ: forall r: preg, r <> RSP -> r <> RA -> rs1 r = rs2 r)
      (RRSP: rs1 RSP = Val.offset_ptr (rs2 RSP) ((Ptrofs.repr (size_chunk Mptr))))
      (MEQ: loadvv Mptr m (rs2 RSP) = Some (rs1 RA))
      (RANU: rs1 RA <> Vundef)
      f ijmp
      (PC1: pc_at (State rs1 m) = Some (inl (f,ijmp)))
      (JMP: is_jmp ijmp):
      match_states (State rs1 m) (State rs2 m)
  | match_states_normal s1 s2
                        (SEQ: seq s1 s2)
                        (PC1: match pc_at s2 with
                              | Some (inl (f,i)) => ~ intermediate_instruction i
                              | Some (inr ef) => False
                              | None => True
                              end
                        ):
      match_states s1 s2
  | match_states_stuck s1 s2
                       (PCnone: pc_at s1 = None)
                       (PCeq: rs_state s1 PC = rs_state s2 PC)
                       (RAXeq: rs_state s1 RAX = rs_state s2 RAX)
    : match_states s1 s2.

  Lemma max_stacksize_range':
    size_chunk Mptr <= max_stacksize <= Ptrofs.max_unsigned.
  Proof.
    split. unfold max_stacksize.
    destruct Mptr; simpl; lia.
    vm_compute. congruence.
  Qed.

  Hypothesis WF: wf_asm_prog instr_size ge.

  Lemma max_stacksize_aligned : (8 | max_stacksize).
  Proof. unfold max_stacksize. exists 512. lia. Qed.

  Lemma max_stacksize_range : 0 <= max_stacksize <= Ptrofs.max_unsigned.
  Proof. unfold max_stacksize. vm_compute. split; congruence. Qed.

  Lemma max_stacksize'_range : 0 <= max_stacksize + align (size_chunk Mptr) 8 <= Ptrofs.max_unsigned.
  Proof. unfold max_stacksize. vm_compute. split; congruence. Qed.


  Lemma initial_states_match :
    forall s1 s2,
      SSAsm.initial_state prog s1 ->
      initial_state prog s2 ->
      exists s1', SSAsm.initial_state prog s1' /\ match_states s1' s2.
  Proof.
    simpl; intros s1 s2 IS1 IS2.
    exists s1; split; auto. inv IS1; inv IS2.
    unfold ge, ge0, ge1, rs0, rs1 in *. rewrite_hyps.
    apply Genv.init_mem_stack in H as STK.
    apply Mem.alloc_result in H0 as X. unfold Mem.nextblock in X. unfold fresh_block in X. rewrite STK in X.
    simpl in X. subst.
    destruct (Genv.find_funct_ptr ge bmain0) eqn:Fmain.
    - destruct f.
      + eapply match_states_call_alloc.
        * intros. simpl_regs. rewrite (Pregmap.gso _ _ H2). rewrite (Pregmap.gso _ _ H3). reflexivity.
        * simpl_regs. Opaque max_stacksize.  simpl. f_equal.
        * simpl_regs.
          simpl. rewrite <- Ptrofs.sub_add_opp.
          unfold Ptrofs.sub.
          rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)).
          rewrite (Ptrofs.unsigned_repr (max_stacksize + align (size_chunk Mptr) 8)).
          3: vm_compute; intuition congruence. unfold stkblock.
          simpl in H4. congruence.
          generalize max_stacksize'_range. lia.
        * simpl. simpl_regs. rewrite Fmain.
          erewrite wf_asm_alloc_at_beginning; eauto.
        * apply make_palloc_is_alloc.
      + eapply match_states_call_external.
        * intros. simpl_regs. rewrite (Pregmap.gso _ _ H2). rewrite (Pregmap.gso _ _ H3). auto.
        * simpl_regs. simpl. f_equal.
        * simpl_regs.
          simpl. rewrite <- Ptrofs.sub_add_opp.
          unfold Ptrofs.sub.
          rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)).
          rewrite (Ptrofs.unsigned_repr (max_stacksize + align (size_chunk Mptr) 8)).
          3: vm_compute; intuition congruence. unfold stkblock.
          simpl in H4. congruence.
          generalize max_stacksize'_range. lia.
        * simpl. simpl_regs. rewrite Fmain. eauto.
    - eapply match_states_stuck. simpl. rewrite Fmain. auto.
      simpl. simpl_regs. auto.
      simpl. simpl_regs. auto.
  Qed.

  Lemma match_states_PC:
    forall s1 s2,
      match_states s1 s2 ->
      rs_state s1 PC = rs_state s2 PC.
  Proof.
    intros s1 s2 MS; inv MS; try rewrite REQ by congruence; try reflexivity.
    inv SEQ. simpl; auto. apply REQ. congruence. auto.
  Qed.

  Inductive is_builtin: instruction -> Prop :=
  | is_builtin_intro ef args res: is_builtin (Pbuiltin ef args res).

  Lemma is_builtin_dec i: is_builtin i \/ ~ is_builtin i.
  Proof.
    destruct i; first [right; now inversion 1|now econstructor].
  Qed.

  Lemma step_internal:
    forall s t s'
      (STEP: SSAsm.step instr_size ge s t s')
      f i
      (PCAT: pc_at s = Some (inl (f,i)))
      (NB: ~ is_builtin i),
      SSAsm.exec_instr instr_size ge f i (rs_state s) (m_state s) = Next (rs_state s') (m_state s') /\ t = E0.
  Proof.
    unfold pc_at; intros s t s'  STEP; inv STEP.
    - rewrite H, H0. setoid_rewrite H1. inversion 1; subst. simpl. eauto.
    - rewrite H, H0. setoid_rewrite H1. intros f0 i A; inv A. intro NIB; exfalso; apply NIB. constructor.
    - rewrite H, H0. inversion 1.
  Qed.

  Lemma step_external_store:
    forall s t s'
      (STEP: SSAsm.step instr_size ge s t s')
      ef
      (PCAT: pc_at s = Some (inr ef)),
    exists m2,
      Mem.storev Mptr (m_state s) (Val.offset_ptr (rs_state s RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
                 (rs_state s RA) = Some m2.
  Proof.
    unfold pc_at; intros s t s'  STEP; inv STEP; rewrite H, H0; try now destr.
    inversion 1; simpl; eauto.
  Qed.

  Lemma internal_step:
    forall rs1 rs2 m1 m2 f i
      (PCAT: pc_at (State rs1 m1) = Some (inl (f,i)))
      (EI: SSAsm.exec_instr instr_size ge f i rs1 m1 = Next rs2 m2),
      SSAsm.step instr_size  ge (State rs1 m1) E0 (State rs2 m2).
  Proof.
    intros.
    simpl in PCAT. repeat destr_in PCAT.
    eapply SSAsm.exec_step_internal; eauto.
  Qed.

  Lemma offset_ptr_neg_sub a b ptr:
    (Val.offset_ptr (Val.offset_ptr ptr (Ptrofs.neg a)) (Ptrofs.sub a b)) = Val.offset_ptr ptr (Ptrofs.neg b).
  Proof.
    rewrite Val.offset_ptr_assoc. f_equal.
    rewrite Ptrofs.sub_add_opp. rewrite <- Ptrofs.add_assoc.
    rewrite (Ptrofs.add_commut (Ptrofs.neg _)). rewrite Ptrofs.add_neg_zero. apply Ptrofs.add_zero_l.
  Qed.

  Lemma offset_ptr_neg_sub' : forall sp sz,
      Val.offset_ptr (Val.offset_ptr sp (Ptrofs.repr (size_chunk Mptr))) (Ptrofs.neg sz) =
      Val.offset_ptr sp (Ptrofs.neg (Ptrofs.sub sz (Ptrofs.repr (size_chunk Mptr)))).
  Proof.
    intros. destruct sp; simpl; auto.
    f_equal.
    rewrite <- Ptrofs.sub_add_opp.
    rewrite <- Ptrofs.sub_add_opp.
    rewrite (Ptrofs.sub_add_opp sz _).
    rewrite Ptrofs.sub_add_r.
    rewrite Ptrofs.sub_add_opp.
    rewrite (Ptrofs.sub_add_opp i _).
    reflexivity.
  Qed.

  Lemma offset_ptr_cancel:
    forall ptr a,
      (exists b o, ptr = Vptr b o) ->
      Val.offset_ptr (Val.offset_ptr ptr a) (Ptrofs.neg a) = ptr.
  Proof.
    intros ptr a (b & o & EQ); subst. simpl.
    rewrite <- Ptrofs.sub_add_opp.
    rewrite Ptrofs.add_commut.
    rewrite Ptrofs.sub_add_l.
    rewrite Ptrofs.sub_idem. rewrite Ptrofs.add_zero_l. auto.
  Qed.

  Lemma eval_addrmode64_seq:
    forall (rs rs' : regset) (REQ: forall r, r <> RA -> rs r = rs' r) a,
      eval_addrmode64 ge a rs = eval_addrmode64 ge a rs'.
  Proof.
    intros.
    unfold eval_addrmode64.
    destr. f_equal. destr. apply REQ. congruence.
    f_equal. destr. destr. rewrite REQ by congruence. auto.
  Qed.

  Lemma eval_addrmode32_seq:
    forall (rs rs' : regset) (REQ: forall r, r <> RA -> rs r = rs' r) a,
      eval_addrmode32 ge a rs = eval_addrmode32 ge a rs'.
  Proof.
    intros.
    unfold eval_addrmode32.
    destr. f_equal. destr. apply REQ. congruence.
    f_equal. destr. destr. rewrite REQ by congruence. auto.
  Qed.

  Lemma eval_addrmode_seq:
    forall (rs rs' : regset) (REQ: forall r, r <> RA -> rs r = rs' r) a,
      eval_addrmode ge a rs = eval_addrmode ge a rs'.
  Proof.
    unfold eval_addrmode. intros.
    destr; eauto using eval_addrmode32_seq, eval_addrmode64_seq.
  Qed.

  Lemma eval_testcond_seq:
    forall (rs rs' : regset) (REQ: forall r, r <> RA -> rs r = rs' r) t,
      eval_testcond t rs = eval_testcond t rs'.
  Proof.
    unfold eval_testcond. intros.
    repeat rewrite REQ by congruence. repeat destr.
  Qed.

  Lemma exec_load_seq:
    forall chunk m a r r' rd r0 m0 sz,
      seq (State r m) (State r' m) ->
      exec_load ge sz chunk m a r rd = Next r0 m0 ->
      exists r1 m1,
        exec_load ge sz chunk m a r' rd = Next r1 m1.
  Proof.
    unfold exec_load; intros chunk m a r r' rd r0 m0 sz SEQ EL; repeat destr_in EL.
    erewrite eval_addrmode_seq in Heqo. rewrite Heqo. eauto. inv SEQ; auto.
  Qed.

  Lemma exec_store_seq:
    forall chunk m a r r' rd lrd r0 m0 sz,
      seq (State r m) (State r' m) ->
      exec_store ge sz chunk m a r rd lrd = Next r0 m0 ->
      rd <> RA ->
      exists r1 m1,
        exec_store ge sz chunk m a r' rd lrd = Next r1 m1.
  Proof.
    unfold exec_store; intros chunk m a r r' rd lrd r0 m0 sz SEQ EL NRA; repeat destr_in EL.
    inv SEQ.
    erewrite eval_addrmode_seq in Heqo. rewrite <- REQ. rewrite Heqo. eauto. auto. auto.
  Qed.

  Lemma goto_label_seq:
    forall f l rs1 rs2 m rs' m'
      (GL : goto_label instr_size ge f l rs1 m = Next rs' m')
      (SEQ: rs1 PC = rs2 PC),
    exists (rs2' : regset) (m2' : mem), goto_label instr_size ge f l rs2 m = Next rs2' m2'.
  Proof.
    unfold goto_label. intros. destr. rewrite <- SEQ. destr. destr. eauto.
  Qed.

  Ltac force_rewrite_match H :=
    match goal with
      H: ?b = _ |- context [ match ?a with _ => _ end ] =>
      cut (b = a);[ let A := fresh in intro A; rewrite <- A, H | ]
    end.

  Lemma eval_builtin_arg_eq_rs:
    forall (rs1 rs2: regset) (REQ: forall r, r <> RA -> rs1 r = rs2 r) sp m args vargs
      (NIN: ~ in_builtin_arg args RA),
      eval_builtin_arg ge rs1 sp m args vargs ->
      eval_builtin_arg ge rs2 sp m args vargs.
  Proof.
    induction 3; rewrite ? REQ; try econstructor; eauto.
    intro; subst. now simpl in NIN.
    simpl in NIN. apply IHeval_builtin_arg1. intuition.
    simpl in NIN. apply IHeval_builtin_arg2. intuition.
    simpl in NIN. apply IHeval_builtin_arg1. intuition.
    simpl in NIN. apply IHeval_builtin_arg2. intuition.
  Qed.

  Lemma eval_builtin_args_eq_rs:
    forall (rs1 rs2: regset) (REQ: forall r, r <> RA -> rs1 r = rs2 r) sp m args vargs
      (NIN: Forall (fun arg => ~ in_builtin_arg arg RA) args),
      eval_builtin_args ge rs1 sp m args vargs ->
      eval_builtin_args ge rs2 sp m args vargs.
  Proof.
    induction 3; constructor; eauto.
    eapply eval_builtin_arg_eq_rs. 3: apply H. auto. inv NIN; auto.
    inv NIN. apply IHlist_forall2. auto.
  Qed.

  Lemma preg_of_not_RA:
    forall r,
      preg_of r <> RA.
  Proof.
    unfold preg_of. intros.
    destr.
  Qed.

  Lemma extcall_arg_eq_rs:
    forall (rs1 rs2: regset)
      (REQ : forall r : preg, r <> RA -> rs1 r = rs2 r)
      m1 l arg
      (ARGS : extcall_arg rs1 m1 l arg),
      extcall_arg rs2 m1 l arg.
  Proof.
    intros rs1 rs2 REQ m1 l arg ARGS; inv ARGS.
    - rewrite REQ.
      econstructor. apply preg_of_not_RA.
    - econstructor; eauto. rewrite <- REQ; eauto. congruence.
  Qed.

  Lemma extcall_arg_pair_eq_rs:
    forall (rs1 rs2: regset)
      (REQ : forall r : preg, r <> RA -> rs1 r = rs2 r)
      m1 l arg
      (ARGS : extcall_arg_pair rs1 m1 l arg),
      extcall_arg_pair rs2 m1 l arg.
  Proof.
    intros; inv ARGS; econstructor; eauto using extcall_arg_eq_rs.
  Qed.

  Lemma extcall_arguments_eq_rs:
    forall (rs1 rs2: regset)
      (REQ : forall r : preg, r <> RA -> rs1 r = rs2 r)
      m1 sg args
      (ARGS : extcall_arguments rs1 m1 sg args),
      extcall_arguments rs2 m1 sg args.
  Proof.
    intros rs1 rs2 REQ m1. unfold extcall_arguments.
    induction 1; econstructor; eauto using extcall_arg_pair_eq_rs.
  Qed.

  Lemma extcall_progress:
    forall (rs1 rs2: regset)
      (REQ : forall r : preg, r <> RSP -> r <> RA -> rs1 r = rs2 r)
      (RRSP : rs1 RSP = Val.offset_ptr (rs2 RSP) (Ptrofs.repr (size_chunk Mptr)))
      m2
      b ef
      (FFP : Genv.find_funct_ptr ge b = Some (External ef))
      (PC1 : rs1 PC = Vptr b Ptrofs.zero)
      args res
      (ARGS : extcall_arguments rs1 m2 (ef_sig ef) args)
      ra (LOADRA: Mem.loadv Mptr m2 (rs2 RSP) = Some ra)
      (SP_TYPE : Val.has_type (rs1 RSP) Tptr)
      (SP_NOT_VUNDEF : rs1 RSP <> Vundef)
      (RA_NOT_VUNDEF : ra <> Vundef)
      m' t
      (EXTCALL : external_call ef ge args m2 t res m'),
    exists s2', (step instr_size) ge (State rs2 m2) t s2'.
  Proof.
    intros.
    eexists.
    eapply exec_step_external. rewrite <- REQ by congruence. eauto. eauto.
    eapply extcall_arguments_eq_rs. 2: eauto. intros. simpl_regs.
    setoid_rewrite Pregmap.gsspec. rewrite <- RRSP.
    destr. apply REQ. eauto. eauto.
    rewrite RRSP in SP_NOT_VUNDEF. unfold Val.offset_ptr in SP_NOT_VUNDEF. destr_in SP_NOT_VUNDEF. apply Val.Vptr_has_type.
    eauto.
    rewrite RRSP in SP_NOT_VUNDEF. unfold Val.offset_ptr in SP_NOT_VUNDEF. destr_in SP_NOT_VUNDEF.
    auto. eauto. eauto.
  Qed.

  Lemma find_instr_eq:
    forall sz f, find_instr instr_size sz f = Asm.find_instr instr_size sz f.
  Proof. intros.  reflexivity. Qed.

  Lemma real_asm_progress:
    forall s1 s2,
      match_states s1 s2 ->
      safe (SSAsm.semantics instr_size prog) s1 ->
      real_asm_inv s2 ->
      (exists r : int, final_state s2 r) \/ (exists (t : trace) (s2' : state), (step instr_size) (Genv.globalenv prog) s2 t s2').
  Proof.
    intros s1 s2 MS SAFE SPAL.
    destruct (SAFE _  (star_refl _ _ _)) as [(r & FS)|(t & s2' & STEP)].
    {
      simpl in FS. inv FS.
      assert (pc_at (State rs m) = None).
      - simpl. rewrite H. unfold Vnullptr. destruct ptr64; auto.
      - inv MS; try congruence. inv SEQ.
        left. eexists; constructor; rewrite <- REQ; eauto. congruence. congruence.
        destruct s2. left. eexists; simpl in *; econstructor. congruence. rewrite <- RAXeq; eauto.
    }
    simpl in *. fold ge in STEP |- *.
    inv MS.
    - exploit step_internal. apply STEP. eauto. intro IB; inv IB; inv ALLOC. intros (EI & T0).
      simpl in *. subst.
      inv ALLOC; simpl in EI. repeat destr_in EI.
      repeat destr_in PC1.
      exploit wf_asm_wf_allocframe; eauto. intro A; inv A.
      rewrite offset_ptr_neg_sub in Heqo.
      rewrite RRSP in Heqo.
      rewrite offset_ptr_cancel in Heqo.
      assert (m = m2) by congruence. subst.
      rewrite RRSP in Heqo0.
      rewrite offset_ptr_neg_sub' in Heqo0.
      right; do 2 eexists.
      eapply exec_step_internal.
      rewrite <- REQ by congruence. eauto. eauto. eauto.
      simpl. rewrite Heqo0. eauto.
      unfold Mem.storev in MEQ. destr_in MEQ. eauto.
    - simpl in PC1. repeat destr_in PC1.
      inv STEP; rewrite_hyps.
      right. exists t.
      assert (m2 = m0).
      {
        rewrite RRSP in H3.
        rewrite offset_ptr_cancel in H3. congruence.
        unfold Mem.storev in MEQ. destr_in MEQ. eauto.
      } subst.
      eapply extcall_progress; eauto.
      assert (exists b o, rs2 RSP = Vptr b o).
      {
        unfold Mem.storev, Mem.loadv in MEQ.
        destruct (rs2 RSP); simpl in *; try congruence. eauto.
      }
      unfold Mem.storev in H3.
      rewrite RRSP in H3. rewrite offset_ptr_cancel in H3; eauto.
      destr_in H3.
      simpl. erewrite Mem.load_store_same; eauto.
      change Mptr with (chunk_of_type Tptr).
      erewrite Val.load_result_same. auto. auto.
    - exploit step_internal. apply STEP. eauto. intro IB; inv IB. intros (EI & T0).
      simpl in EI. repeat destr_in EI.
      simpl in *.
      repeat destr_in PC1. unfold loadvv in LOADRA.
      unfold Mem.loadv in LOADRA. destr_in LOADRA. destr_in Heqo1.
      assert (v = rs1 RA). destr_in LOADRA. subst.
      inv SPAL. red in RSPPTR. simpl in RSPPTR. rewrite Heqv0 in RSPPTR.
      destruct RSPPTR as (o & EQRSP & AL);inv EQRSP; eauto.
      right; do 2 eexists.
      eapply exec_step_internal.
      rewrite <- REQ by congruence. eauto. eauto. eauto.
      simpl. rewrite Heqv0. unfold loadvv.
      simpl. rewrite Heqo1. rewrite LOADRA. eauto.
    - exploit step_internal. apply STEP. eauto. intro IB; inv IB; inv JMP. intros (EI & T0).
      simpl in *.
      repeat destr_in PC1.
      inv JMP.
      + (*Pjmp_s*)
      right; do 2 eexists.
      eapply exec_step_internal.
      rewrite <- REQ by congruence. eauto. eauto. eauto.
      simpl. simpl in EI; simpl; repeat destr_in EI.
      + (*Pjmp_r*)
      right; do 2 eexists.
      eapply exec_step_internal.
      rewrite <- REQ by congruence. eauto. eauto. eauto.
      simpl. simpl in EI; simpl; repeat destr_in EI. eauto.
      rewrite <- REQ. eauto. rewrite Heqo1. eauto.
      intro. subst. eapply wf_asm_jmp_no_rsp; eauto. auto.
      congruence. congruence.
    - inversion SEQ; subst.
      simpl in *. rewrite <- REQ in PC1 by congruence.
      repeat destr_in PC1; subst.
      repeat destr_in Heqo.
      +
        inversion STEP; subst; rewrite_hyps.
        destruct (is_call_dec i1).
        {
          destruct (SAFE _ (star_one _ _ _ _ _ STEP)) as [(r & FS)|(t & s2' & STEP2)].
          - inv FS.
            inv i; simpl in H6; repeat destr_in H6.
            +
            simpl_regs_in H1. unfold Genv.symbol_address in H1. destr_in H1.
            inversion H1. inversion H1.
            +
            simpl_regs_in H1. unfold Genv.symbol_address in H1. destr_in H1.
            unfold Genv.find_funct in Heqo. destr_in Heqo. inversion H0.
          - (* match_state *)
            assert (exists b f', Genv.find_funct_ptr ge b = Some f' /\
                            rs' PC = Vptr b Ptrofs.zero).
            {
              rename H6 into EI.
              inv i; simpl in EI; repeat destr_in EI.
              simpl_regs. unfold Genv.find_funct in Heqo; repeat destr_in Heqo. eauto.
              simpl_regs. unfold Genv.find_funct in Heqo; repeat destr_in Heqo. eauto.
            }
            destruct H as (b & f' & FFP & PC').
            destruct f'.
            + inv i.
              *
              exploit step_internal. apply STEP2. simpl. rewrite PC'. rewrite FFP.
              erewrite wf_asm_alloc_at_beginning; eauto. inversion 1. intros (EI & T0). subst.
              simpl in EI. repeat destr_in EI.
              right; do 2 eexists. eapply exec_step_internal. rewrite <- REQ; eauto. congruence. eauto. eauto.
              simpl in H6. destr_in H6. inv H6. simpl. force_rewrite_match Heqo. eauto.
              simpl_regs. rewrite <- ! REQ.
              f_equal.
              apply offset_ptr_neg_sub. congruence. congruence.

              *
              exploit step_internal. apply STEP2. simpl. rewrite PC'. rewrite FFP.
              erewrite wf_asm_alloc_at_beginning; eauto. inversion 1. intros (EI & T0). subst.
              simpl in EI. repeat destr_in EI.
              right; do 2 eexists. eapply exec_step_internal. rewrite <- REQ; eauto. congruence. eauto. eauto.
              simpl in H6. destr_in H6. inv H6. simpl. force_rewrite_match Heqo. eauto.
              simpl_regs. rewrite <- ! REQ.
              f_equal.
              apply offset_ptr_neg_sub. congruence. congruence.
            + generalize (step_external_store _ _ _ STEP2 e). simpl; rewrite PC' , FFP.
              intro STORE; trim STORE. auto. destruct STORE as (m2' & STORE).
              inv i.
              *
              simpl in H6. destr_in H6. inv H6. revert STORE. simpl_regs. intros.
              right; do 2 eexists. eapply exec_step_internal. rewrite <- REQ; eauto. congruence. eauto. eauto.
              simpl. rewrite <- ! REQ. setoid_rewrite STORE. eauto. congruence. congruence.
              *
              simpl in H6. destr_in H6. inv H6. revert STORE. simpl_regs. intros.
              right; do 2 eexists. eapply exec_step_internal. rewrite <- REQ; eauto. congruence. eauto. eauto.
              simpl. rewrite <- ! REQ. setoid_rewrite STORE. eauto. congruence. congruence. congruence.
        }

        cut (exists rs2' m2', exec_instr instr_size ge f0 i1 rs2 m = Next rs2' m2').
        intros (rs2' & m2' & EI'). right; exists E0, (State rs2' m2').
        eapply exec_step_internal. rewrite <- REQ by congruence; eauto. eauto. eauto. eauto.
        destruct i1; simpl in H6; simpl; eauto using exec_load_seq, exec_store_seq.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        repeat rewrite <- REQ by congruence. repeat destr_in H6. eauto.
        repeat rewrite <- REQ by congruence. repeat destr_in H6. eauto.
        repeat rewrite <- REQ by congruence. repeat destr_in H6. eauto.
        repeat rewrite <- REQ by congruence. repeat destr_in H6. eauto.
        repeat destr; eauto.
        eapply goto_label_seq; eauto. apply REQ; congruence.
        destr_in H6. inv H6. eauto. destr_in H6. do 2 eexists. rewrite <- REQ. rewrite Heqo.
        eauto. congruence.
        erewrite <- eval_testcond_seq by eauto. repeat destr_in H6; eauto. eapply goto_label_seq; eauto. apply REQ; congruence.
        erewrite <- eval_testcond_seq by eauto. destr_in H6.
        erewrite <- eval_testcond_seq by eauto. repeat destr_in H6; eauto. eapply goto_label_seq; eauto. apply REQ; congruence.
        rewrite <- REQ by congruence. destr. destr. eapply goto_label_seq. eauto. simpl_regs. apply REQ; congruence.
        exfalso; apply n; econstructor.
        exfalso; apply n; econstructor.
        exfalso; apply PC1. constructor 2. auto.
        eapply exec_store_seq; eauto. congruence.
        eapply exec_store_seq; eauto. congruence.
        exfalso; apply PC1. constructor 1. constructor.
        eapply eval_builtin_args_eq_rs in H4. rewrite REQ in H4.
        right; do 2 eexists. eapply exec_step_builtin. rewrite <- REQ; eauto. congruence. all: eauto. congruence.
        eapply wf_asm_builtin_not_PC; eauto.
      + inv STEP; repeat destr_in Heqo.
    - inv STEP; simpl in *; repeat destr_in PCnone.
  Qed.

  Lemma ptrofs_cancel i f s:
    i =
    Ptrofs.add
      (Ptrofs.add (Ptrofs.add i s) (Ptrofs.neg f))
      (Ptrofs.sub f s).
  Proof.
    rewrite ! Ptrofs.add_assoc.
    transitivity (Ptrofs.add i Ptrofs.zero). rewrite Ptrofs.add_zero. auto.
    f_equal.
    rewrite Ptrofs.sub_add_opp.
    rewrite (Ptrofs.add_commut f). rewrite <- (Ptrofs.add_assoc _ (Ptrofs.neg s)).
    rewrite (Ptrofs.add_commut _ (Ptrofs.neg s)). rewrite (Ptrofs.add_assoc (Ptrofs.neg s)).
    rewrite <- (Ptrofs.add_assoc _ (Ptrofs.neg s)).
    rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero_l.
    rewrite Ptrofs.add_commut.    rewrite Ptrofs.add_neg_zero. auto.
  Qed.

  Lemma offset_ptr_has_type:
    forall ptr o,
      Val.has_type (Val.offset_ptr ptr o) Tptr.
  Proof.
    intros. destruct ptr; now (simpl; auto).
  Qed.


  Lemma goto_label_match:
    forall f l rs2 m2 rs2' m2' rs1,
      (forall r: preg, r<>RA -> rs1 r = rs2 r) ->
      goto_label instr_size ge f l rs2 m2 = Next rs2' m2' ->
      exists rs1' m1', goto_label instr_size ge f l rs1 m2 = Next rs1' m1' /\ seq (State rs1' m1') (State rs2' m2').
  Proof.
    intros f l rs2 m2 rs2' m2' rs1 REQ GL2.
    edestruct goto_label_seq as (rs1' & m1' & GL). eauto. symmetry; apply REQ. congruence. rewrite GL.
    do 2 eexists; split; eauto.
    unfold goto_label in GL2, GL. destr_in GL. rewrite REQ in GL by congruence.
    repeat destr_in GL. inv GL2.
    constructor. intros. regs_eq.
  Qed.

  Lemma find_instr_same : forall c i1 i2 ofs1 ofs2,
      find_instr instr_size ofs1 c = i1 ->
      find_instr instr_size ofs2 c = i2 ->
      ofs1 = ofs2 ->
      i1 = i2.
  Proof.
    intros. congruence. Qed.


  Lemma goto_label_PC:
    forall f l r m r0 m0
      (GL: goto_label instr_size ge f l r m = Next r0 m0)
      b i
      (PCbef: r PC = Vptr b i)
      (FFP: Genv.find_funct_ptr ge b = Some (Internal f)) ,
      (forall f0 i2,
          pc_at (State r0 m0) = Some (inl (f0,i2)) ->
          ~ intermediate_instruction i2)
      /\ (forall ef,
            pc_at (State r0 m0) = Some (inr ef) ->
            False ).
  Proof.
    intros.
    simpl.
    unfold goto_label in GL.
    rewrite PCbef, FFP in GL. destr_in GL. inv GL. simpl_regs. rewrite FFP.
    destr. split. 2: inversion 1. intros f0 i2 EQ; inv EQ.
    assert (EQz: Ptrofs.unsigned (Ptrofs.repr z) = z).
    {
      replace z with (z-0) by lia.
      eapply label_pos_repr; eauto. rewrite Z.add_0_r. eapply wf_asm_code_bounded. eauto. lia.
    } rewrite EQz in *.
    generalize (label_pos_spec instr_size instr_size_bound l (fn_code f0) 0 z). intro LPS; trim LPS.
    rewrite Z.add_0_r. eapply wf_asm_code_bounded; eauto. trim LPS. lia. trim LPS; auto.
    generalize (find_instr_ofs_pos instr_size instr_size_bound _ _ _ LPS).
    intros POS II; inv II.
    {
      inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0. intro.
      generalize (instr_size_bound (Plabel l)). extlia.
    }
    {
      exploit wf_asm_ret_jmp_comes_after_freeframe. eauto. 2: apply H.
      rewrite EQz. eauto.
      intros (o' & ifree & FI & IFREE & RNG).
      generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ LPS FI). intros [H0|H0].
      inv IFREE. inv H1. destruct H0.
      replace (z-0) with z in H0 by lia.
      replace (z - instr_size (Plabel l) + instr_size (Plabel l)) with z in H0 by lia.
      generalize (instr_size_bound ifree). extlia.
      generalize (instr_size_bound (Plabel l) ). extlia.
    }
  Qed.

  Lemma exec_instr_normal:
    forall rs1 rs2 m1 m2 b ofs f i rs2' m2',
      seq (State rs1 m1) (State rs2 m2) ->
      rs2 PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr instr_size ge f i rs2 m2 = Next rs2' m2' ->
      ~ intermediate_instruction i ->
      ~ is_call i ->
      ~ is_free i ->
      (exists rs1' m1',
        SSAsm.exec_instr instr_size ge f i rs1 m1 = Next rs1' m1' /\
        seq (State rs1' m1') (State rs2' m2')) /\
        match pc_at (State rs2' m2') with
        | Some (inl (_, i)) => ~ intermediate_instruction i
        | Some (inr ef) => False
        | None => True
        end.
  Proof.
    intros rs1 rs2 m1 m2 b ofs f i rs2' m2' SEQ PC2 FFP FI EI NII NIC NIF.
    simpl.
    inv SEQ.
    assert (SSAsm.exec_instr instr_size ge f i rs2 m2 = Next rs2' m2').
    {
      rewrite <- EI.
      destruct i; auto.
      contradict NIC; constructor.
      contradict NIC; constructor.
      contradict NII. constructor 2. auto.
      contradict NII. constructor. constructor.
      contradict NIF. constructor.
    } clear EI; rename H into EI.
    split.
    {
          destruct i; simpl in *; unfold exec_load, exec_store in *;
          erewrite ? eval_addrmode_seq by eauto;
          repeat erewrite ?  eval_testcond_seq by eauto;
          erewrite ? REQ by congruence;
          repeat destr_in EI;
          try (do 2 eexists; split; [eauto|constructor; intros; simpl; regs_eq;
                                           try eapply eval_addrmode64_seq ;
                                           try eapply eval_addrmode32_seq; now eauto
                                    ]; fail).
        do 2 eexists; split; [eauto|constructor; intros; simpl; regs_eq; repeat destr; simpl; regs_eq].
        do 2 eexists; split; [eauto|constructor; intros; simpl; regs_eq; repeat destr; simpl; regs_eq].
        eapply goto_label_match; eauto.
        eapply goto_label_match; eauto.
        erewrite eval_testcond_seq by eauto. rewrite Heqo0. eapply goto_label_match; eauto.
        erewrite eval_testcond_seq by eauto. rewrite Heqo0.
        do 2 eexists; split; [eauto|constructor; intros; simpl; regs_eq; repeat destr; simpl; regs_eq].
        erewrite eval_testcond_seq by eauto. rewrite Heqo0.
        do 2 eexists; split; [eauto|constructor; intros; simpl; regs_eq; repeat destr; simpl; regs_eq].
        eapply goto_label_match. 2: eauto. intros; regs_eq.
        contradict NII. constructor 2; auto.
        contradict NII. constructor. constructor.
    }
    destruct (Val.eq (rs2' PC) (Val.offset_ptr (rs2 PC) (Ptrofs.repr (instr_size i)))).
    {
      rewrite e, PC2. simpl. rewrite FFP.
      destr. repeat destr_in Heqo. rename Heqo0 into FI'.
      intro A.
      inv A.
      {
        inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply FI'.
        erewrite wf_asm_pc_repr; eauto.
        generalize (Ptrofs.unsigned_range ofs).  generalize (instr_size_bound i). lia.
      }
      {
        exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
        intros (o' & ifree & FI2 & IFREE & RNG).
        generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ FI FI2).
        erewrite wf_asm_pc_repr in RNG; eauto.
        rewrite RNG.
        intros [EQ|NOOV]. subst. congruence.
        generalize (instr_size_bound i) (instr_size_bound ifree). lia.
      }
    }
    destruct i; simpl in *; unfold exec_load, exec_store in EI; repeat destr_in EI;
      unfold compare_ints, compare_longs, compare_floats, compare_floats32 in n;
      repeat destr_in n;
      simpl_regs_in n; try congruence.
    generalize (goto_label_PC _ _ _ _ _ _ H0 _ _ PC2 FFP). simpl. intros (A & B); repeat destr; eauto.
    contradict NII. econstructor 2. right. econstructor.
    contradict NII. econstructor 2. right. econstructor.
    generalize (goto_label_PC _ _ _ _ _ _ H0 _ _ PC2 FFP). simpl. intros (A & B); repeat destr; eauto.
    generalize (goto_label_PC _ _ _ _ _ _ H0 _ _ PC2 FFP). simpl. intros (A & B); repeat destr; eauto.
    generalize (goto_label_PC _ _ _ _ _ _ H0 _ _ PC2 FFP). simpl. intros (A & B); repeat destr; eauto.
    contradict NIC. constructor.
    contradict NIC. constructor.
    contradict NII. constructor 2. auto.
  Qed.

  Lemma offsets_after_call_correct:
    forall c pos o,
      0 <= pos ->
      In o (offsets_after_call instr_size c pos) ->
      exists oc icall, find_instr instr_size oc c = Some icall /\  is_call icall /\ oc + instr_size icall = o - pos.
  Proof.
    induction c; simpl; intros; eauto.
    easy.
    destr_in H0.
    - destruct H0.
      + subst.
        exists 0, a. rewrite zeq_true. split; auto. split; auto. lia.
      + destruct (fun pos => IHc _ _ pos H0) as (oc & icall & INSTR & ICALL & EQ).
        generalize (instr_size_bound a). lia.
        exists (oc + instr_size a).
        rewrite pred_dec_false.
        replace (oc + instr_size a - instr_size a) with oc by lia. rewrite INSTR.
        eexists; split; eauto. split; auto. lia.
        generalize (instr_size_bound a) (find_instr_ofs_pos instr_size instr_size_bound _ _ _ INSTR). lia.
    - destruct (fun pos => IHc _ _ pos H0) as (oc & icall & INSTR & ICALL & EQ).
      generalize (instr_size_bound a). lia.
      exists (oc + instr_size a).
      rewrite pred_dec_false.
      replace (oc + instr_size a - instr_size a) with oc by lia. rewrite INSTR.
      eexists; split; eauto. split; auto. lia.
      generalize (instr_size_bound a) (find_instr_ofs_pos instr_size instr_size_bound _ _ _ INSTR). lia.
  Qed.

  Lemma loadvv_bastck_storev:
    forall rs m v ,
      rsp_ptr (State rs m) -> bstack_perm (State rs m) ->
      loadvv Mptr m (rs RSP) = Some v ->
      Mem.storev Mptr m (rs RSP) v = Some m.
  Proof.
    intros. destruct H as (ofs & SP & ALIGN).
    simpl in SP. rewrite SP in *. unfold loadvv in H1. destr_in H1.
    assert (v0 = v). destr_in H1. subst.
    eapply Mem.loadv_val_storev; eauto. destr_in H1.
  Qed.

  Lemma real_asm_step:
    forall s2 t s2',
      step instr_size (Genv.globalenv prog) s2 t s2' ->
      forall s1 : state,
        match_states s1 s2 ->
        real_asm_inv s2 ->
        safe (SSAsm.semantics instr_size prog) s1 ->
        exists s1', SSAsm.step instr_size (Genv.globalenv prog) s1 t s1' /\ match_states s1' s2'.
  Proof.
    intros s2 t s2' STEP s1 MS INV SAFE. inv INV.
    fold ge in STEP.
    inv MS.
    - (*Pallocframe*)
      simpl in PC1. repeat destr_in PC1.
      rewrite REQ in Heqv by congruence.
      inv STEP; rewrite_hyps. 2: inv ALLOC.
      inv ALLOC. simpl in H6. destr_in H6. inv H6.
      eexists; split. eapply SSAsm.exec_step_internal. rewrite REQ by congruence; eauto.
      eauto. eauto.
      simpl. (* force_rewrite_match MEQ.*)
      cut (Mem.storev Mptr m1 (rs2 RSP) (rs1 RA) = Mem.storev Mptr m1 (Val.offset_ptr (Val.offset_ptr (rs1 RSP) (Ptrofs.neg (Ptrofs.repr (align sz 8)))) ora) (rs1 RA)); [let A := fresh in intro A; rewrite <- A,H|]. rewrite <- H. rewrite MEQ.
      rewrite <- offset_ptr_neg_sub' in Heqo1. rewrite <- RRSP in Heqo1. rewrite Heqo1.
      eauto. f_equal.
      rewrite RRSP.
      eapply wf_asm_wf_allocframe in Heqo0; eauto. inv Heqo0.
      unfold Mem.storev, Mem.loadv in MEQ.
      destruct (rs2 RSP); simpl in *; try congruence.
      f_equal. apply ptrofs_cancel.
      eapply match_states_normal.
      constructor. intros. apply nextinstr_nf_eq.
      intros; apply set_reg_eq. intros. apply set_reg_eq. eauto.
      auto.
      rewrite RRSP. rewrite Val.offset_ptr_assoc. f_equal.
      rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.neg_add_distr. rewrite Ptrofs.add_commut.
      rewrite Ptrofs.neg_involutive. auto.
      simpl. simpl_regs. rewrite Heqv. simpl. rewrite Heqo.
      destr. destr_in Heqo2. inv Heqo2.
      intro A.
      generalize instr_size_bound. intros POS.
      inv A.
      {
        inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0. intro I0.
        exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo3.
        rewrite Ptrofs.add_unsigned. rewrite I0.
        generalize (POS (Pallocframe sz ora olink)). intro POSP.
        rewrite Ptrofs.unsigned_repr; eauto. simpl. rewrite Ptrofs.unsigned_repr; eauto.
        lia. lia.
        rewrite Ptrofs.unsigned_repr; lia.
      }
      {
        exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
        intros (o' & ifree & FI & IFREE & RNG).
        exploit wf_asm_alloc_only_at_beginning; eauto.
        generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ FI Heqo0).
        erewrite wf_asm_pc_repr in RNG; eauto.
        rewrite RNG.
        intros [EQ|NOOV]. subst; inv IFREE.
        generalize (instr_size_bound (Pallocframe sz ora olink)) (instr_size_bound ifree). lia.
      }
    - (* external call *)
      simpl in PC1. repeat destr_in PC1.
      rewrite REQ in Heqv by congruence.
      inv STEP; rewrite_hyps.
      assert (RAC : ra_after_call instr_size ge (rs1 RA)).
      {
        destruct (SAFE _ (star_refl _ _ _)) as [(rr & FS)|(tt & s' & STEP)].
        simpl in FS. inv FS. contradict H1. rewrite REQ by congruence. rewrite Heqv. inversion 1.
        simpl in STEP.
        rewrite <- REQ in Heqv by congruence.
        fold ge in STEP.
        inv STEP; rewrite_hyps; auto.
      }
      unfold Mem.storev in MEQ; destr_in MEQ.
      assert (rs1 RA = ra /\ ra <> Vundef /\ Val.has_type ra Tptr).
      {
        simpl in *. split.
        erewrite Mem.load_store_same in LOADRA; eauto. inv LOADRA.
        change Mptr with (chunk_of_type Tptr).
        symmetry.  apply Val.load_result_same.
        revert RA_NOT_VUNDEF. unfold Val.load_result, Mptr, Tptr.
        destruct ptr64 eqn:PTR.
        destruct (rs1 RA); simpl; try congruence; auto.
        destruct (rs1 RA); simpl; try congruence; auto.
        eapply Mem.load_type in LOADRA.
        change Tptr with (type_of_chunk Mptr). auto.
      } destruct H as (RA1 & RA1U & RATYP); subst.
      eexists; split. eapply SSAsm.exec_step_external. rewrite REQ by congruence; eauto.
      eauto.
      rewrite <- MEQ.
      rewrite RRSP. rewrite offset_ptr_cancel. reflexivity. eauto.
      eapply extcall_arguments_eq_rs. 2: apply H3.
      intros. setoid_rewrite Pregmap.gsspec. rewrite <- RRSP.
      destr. symmetry; apply REQ. auto. auto.
      rewrite RRSP. apply offset_ptr_has_type.
      auto.
      rewrite RRSP. simpl; congruence.
      auto.
      eauto. eauto. reflexivity.
      eapply match_states_normal.
      constructor. intros.
      destruct (preg_eq r RSP). subst. simpl_regs.
      rewrite set_pair_no_rsp.
      unfold undef_caller_save_regs. simpl.
      auto.
      apply no_rsp_loc_external_result.
      rewrite (Pregmap.gso _ _ n).
      intros; apply set_reg_eq.
      intros. apply set_reg_eq.
      intros. apply set_pair_eq.
      intros.
      unfold undef_caller_save_regs. destr; auto.
      auto. auto.
      simpl. simpl_regs.
      destr. destr_in Heqo0. destr_in Heqo0.
      destruct RAC as (RAU & RAC).
      specialize (RAC _ _ eq_refl _ Heqo1). red in RAC. destr_in RAC. destr_in Heqo0. inv Heqo0.
      destruct (offsets_after_call_correct _ _ _ (Z.le_refl _) RAC) as (oc & icall & ICALL & ISCALL & EQofs).
      intro II; inv II.
      {
        inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo2.
        generalize (find_instr_ofs_pos instr_size instr_size_bound _ _ _ ICALL) (instr_size_bound icall). lia.
      }
      {
        exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
        intros (o' & ifree & FI & IFREE & RNG).
        generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ FI ICALL).
        rewrite Z.sub_0_r in EQofs. rewrite <- EQofs in RNG.
        rewrite RNG.
        rewrite <- RNG at 2.
        intros [EQ|NOOV]. subst; inv IFREE; inv ISCALL.
        generalize (instr_size_bound icall) (instr_size_bound ifree). lia.
      }
    - (*Pret*)
      simpl in PC1. repeat destr_in PC1.
      rewrite REQ in Heqv by congruence. inv STEP; rewrite_hyps.
      assert (RAC : ra_after_call instr_size ge (rs1 RA)).
      {
        destruct (SAFE _ (star_refl _ _ _)) as [(rr & FS)|(tt & s' & STEP)].
        simpl in FS. inv FS. contradict H1. rewrite REQ by congruence. rewrite Heqv. inversion 1.
        simpl in STEP.
        rewrite <- REQ in Heqv by congruence.
        fold ge in STEP.
        inv STEP; rewrite_hyps; auto.
        simpl in H7. destr_in H7.
      }
      simpl in H6. destr_in H6. inv H6.
      assert (RAV: rs1 RA = v).
      {
        unfold loadvv in Heqo1. destr_in Heqo1.
      }
      eexists; split. eapply SSAsm.exec_step_internal. rewrite REQ by congruence; eauto. eauto. eauto.
      simpl. rewrite pred_dec_true. eauto. eauto.
      apply match_states_normal.
      + constructor. intros. rewrite ! (Pregmap.gso _ _ H). apply set_reg_eq; auto.
        intros.
        setoid_rewrite Pregmap.gsspec. destr. apply REQ. auto. auto.
      + simpl. simpl_regs.
        destr. destr_in Heqo2. destr_in Heqo2.
        destruct RAC as (RAU & RAC).
        specialize (RAC _ _ RAV _ Heqo3). red in RAC. destr_in RAC. destr_in Heqo2. inv Heqo2.
        destruct (offsets_after_call_correct _ _ _ (Z.le_refl _) RAC) as (oc & icall & ICALL & ISCALL & EQofs).
        intro II; inv II.
        {
          inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo4.
          generalize (find_instr_ofs_pos instr_size instr_size_bound _ _ _ ICALL) (instr_size_bound icall). lia.
        }
        {
          exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
          intros (o' & ifree & FI & IFREE & RNG).
          generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ FI ICALL).
          rewrite Z.sub_0_r in EQofs. rewrite <- EQofs in RNG.
          rewrite RNG.
          rewrite <- RNG at 2.
          intros [EQ|NOOV]. subst; inv IFREE; inv ISCALL.
          generalize (instr_size_bound icall) (instr_size_bound ifree). lia.
        }
    -  (* Pjmp *)
      simpl in PC1. repeat destr_in PC1.
      rewrite REQ in Heqv by congruence. inv STEP; rewrite_hyps. 2: now (inv JMP).
      inv JMP.
      + (* Pjmp_s *)
        simpl in H6. inv H6.
        eexists; split. eapply SSAsm.exec_step_internal. rewrite REQ by congruence; eauto. eauto. eauto.
        simpl. eauto.
        fold ge.
        destr_in H0.
        destr_in H0. inv H0.
        destruct f.
        * (*jmp to the begin of an internal function*)
        eapply match_states_call_alloc.
        intros. apply set_reg_eq; auto.
        simpl_regs. auto.
        simpl_regs.
        eapply loadvv_bastck_storev; eauto.
        simpl. simpl_regs.
        unfold Genv.find_funct in Heqo1. destr.
        unfold Genv.symbol_address in Heqv0. destr_in Heqv0. inv Heqv0.
        rewrite pred_dec_true in Heqo1 by auto. rewrite Heqo1.
        erewrite wf_asm_alloc_at_beginning; eauto. constructor.
        *(*jmp to an external function*)
        eapply match_states_call_external.
        intros. apply set_reg_eq; auto. simpl_regs. auto.
        simpl_regs.        eapply loadvv_bastck_storev; eauto.
        simpl. simpl_regs. unfold Genv.find_funct in Heqo1. destr.
        unfold Genv.symbol_address in Heqv0. destr_in Heqv0. inv Heqv0.
        rewrite pred_dec_true in Heqo1 by auto. rewrite Heqo1. eauto.
      + (*Pjmp_r*)
        simpl in H6. inv H6.
        eexists; split. eapply SSAsm.exec_step_internal. rewrite REQ by congruence; eauto. eauto. eauto.
        simpl. eauto.
        fold ge. rewrite REQ.
        destr_in H0. intro. subst. eapply wf_asm_jmp_no_rsp; eauto. congruence. congruence.
        destr_in H0. inv H0.
        destruct f.
        * (*jmp to the begin of an internal function*)
        eapply match_states_call_alloc.
        intros. apply set_reg_eq; auto.
        simpl_regs. auto.
        simpl_regs.
        unfold Mem.loadv in MEQ.
        eapply loadvv_bastck_storev; eauto.
        simpl. simpl_regs.
        unfold Genv.find_funct in Heqo1. destr.
        unfold Genv.symbol_address in Heqv0. destr_in Heqo1. subst.
        rewrite Heqo1.
        erewrite wf_asm_alloc_at_beginning; eauto. constructor.
        * (*jmp to an external function*)
        eapply match_states_call_external.
        intros. apply set_reg_eq; auto. simpl_regs. auto.
        simpl_regs.
        eapply loadvv_bastck_storev; eauto.
        simpl. simpl_regs. unfold Genv.find_funct in Heqo1. destr. destr_in Heqo1.
        subst. rewrite Heqo1. eauto.
    - (*common case*)
      inv STEP; simpl in *; rewrite H, H0, ? H1 in PC1.
      + destruct (is_call_dec i).
        {
          inv i0.
          +(* Pcall_s *)
          simpl in H2.
          destruct (SAFE _ (star_refl _ _ _)) as [(rr & FS)|(t & s' & STEP)].
          simpl in FS. inv FS. contradict H3. inv SEQ. rewrite REQ by congruence. rewrite H. inversion 1.
          simpl in STEP. fold ge in STEP.
          assert (t = E0).
          {
            inv SEQ. rewrite <- REQ in H by congruence.
            inv STEP; rewrite_hyps; auto.
          } subst.
          eexists; split. eauto.
          edestruct step_internal; eauto. inv SEQ. simpl. rewrite REQ, H, H0. setoid_rewrite  H1. eauto. congruence. inversion 1.
          simpl in H3. destr_in H3. inv H3.
          unfold Genv.find_funct in Heqo. repeat destr_in Heqo.
          inv SEQ. simpl in *. subst. destruct s'. simpl in *. subst.
          destr_in H2. inv H2.
          destruct f0.
          eapply match_states_call_alloc.
          intros. rewrite (Pregmap.gso _ _ H2). apply set_reg_eq; auto. intros; apply set_reg_eq. auto.
          rewrite REQ by congruence; auto.
          simpl_regs. rewrite REQ by congruence.
          symmetry; apply offset_ptr_cancel.
          unfold Mem.storev, Mem.loadv in Heqo. destruct (rs RSP); simpl in *; try congruence; eauto.
          rewrite <- Heqo.
          f_equal. simpl_regs.
          rewrite REQ by congruence; auto.
          simpl. rewrite H5.
          erewrite wf_asm_alloc_at_beginning; eauto. constructor.
          eapply match_states_call_external.
          intros. rewrite (Pregmap.gso _ _ H2). apply set_reg_eq; auto. intros; apply set_reg_eq. auto.
          rewrite REQ by congruence; auto.
          simpl_regs. rewrite REQ by congruence.
          symmetry; apply offset_ptr_cancel.
          unfold Mem.storev, Mem.loadv in Heqo. destruct (rs RSP); simpl in *; try congruence; eauto.
          rewrite <- Heqo.
          rewrite REQ by congruence; auto.
          simpl. rewrite H5. eauto.
          + (*Pcall_r*)
          simpl in H2.
          destruct (SAFE _ (star_refl _ _ _)) as [(rr & FS)|(t & s' & STEP)].
          simpl in FS. inv FS. contradict H3. inv SEQ. rewrite REQ by congruence. rewrite H. inversion 1.
          simpl in STEP. fold ge in STEP.
          assert (t = E0).
          {
            inv SEQ. rewrite <- REQ in H by congruence.
            inv STEP; rewrite_hyps; auto.
          } subst.
          eexists; split. eauto.
          edestruct step_internal; eauto. inv SEQ. simpl. rewrite REQ, H, H0. setoid_rewrite H1. eauto. congruence. inversion 1.
          simpl in H3. destr_in H3. inv H3.
          unfold Genv.find_funct in Heqo. repeat destr_in Heqo.
          inv SEQ. simpl in *. subst. destruct s'. simpl in *. subst.
          destr_in H2. inv H2.
          destruct f0.
          eapply match_states_call_alloc.
          intros. rewrite (Pregmap.gso _ _ H2). apply set_reg_eq; auto. intros; apply set_reg_eq. auto.
          rewrite REQ by congruence; auto. rewrite <- REQ. auto. congruence.
          simpl_regs. rewrite REQ by congruence.
          symmetry; apply offset_ptr_cancel.
          unfold Mem.storev, Mem.loadv in Heqo. destruct (rs RSP); simpl in *; try congruence; eauto.
          rewrite <- Heqo.
          f_equal. simpl_regs.
          rewrite REQ by congruence; auto.
          simpl. rewrite H5.
          erewrite wf_asm_alloc_at_beginning; eauto. constructor.
          eapply match_states_call_external.
          intros. rewrite (Pregmap.gso _ _ H2). apply set_reg_eq; auto. intros; apply set_reg_eq. auto.
          rewrite REQ by congruence; auto. rewrite <- REQ. auto. congruence.
          simpl_regs. rewrite REQ by congruence.
          symmetry; apply offset_ptr_cancel.
          unfold Mem.storev, Mem.loadv in Heqo. destruct (rs RSP); simpl in *; try congruence; eauto.
          rewrite <- Heqo.
          rewrite REQ by congruence; auto.
          simpl. rewrite H5. eauto.
        }
        destruct (is_free_dec i).
        {
          inv i0.
          (*Pfreeframe*)
          simpl in H2.
          destruct (SAFE _ (star_refl _ _ _)) as [(rr & FS)|(t & s' & STEP)].
          simpl in FS. inv FS. contradict H3. inv SEQ. rewrite REQ by congruence. rewrite H. inversion 1.
          simpl in STEP. fold ge in STEP.
          assert (t = E0).
          {
            inv SEQ. rewrite <- REQ in H by congruence.
            inv STEP; rewrite_hyps; auto.
          } subst.
          eexists; split. eauto.
          edestruct step_internal; eauto. inv SEQ. simpl. rewrite REQ, H, H0, H1 by congruence. eauto. inversion 1.
          simpl in H3. destr_in H3. inv H3.
          inv SEQ. simpl in *. subst. destruct s'. simpl in *. subst.
          inv H2.
          edestruct wf_asm_after_freeframe as (i' & FI & RJ); eauto. constructor.
          destruct RJ as [RET|JMP].
          - (*Pfree -> Pret*)
            eapply match_states_free_ret.
            intros.
            apply nextinstr_eq.
            rewrite (Pregmap.gso _ _ H3). simpl_regs. auto.
            rewrite REQ by congruence; auto. simpl_regs.
            rewrite Val.offset_ptr_assoc. f_equal.
            generalize (Ptrofs.repr (align sz 8)).
            generalize (Ptrofs.repr (size_chunk Mptr)).
            intros. rewrite <- Ptrofs.sub_add_l.
            rewrite Ptrofs.sub_add_opp.
            rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero; auto.
            simpl_regs.
            rewrite <- Heqo. f_equal.
            rewrite <- REQ by congruence; auto.
            eapply wf_asm_free_spec in H1; eauto. f_equal. destruct H1 as (SZ & ORA); subst. auto.
            simpl. simpl_regs. rewrite REQ, H by congruence. simpl. rewrite H0. setoid_rewrite FI. subst; eauto.
          - (*Pfree -> jmp *)
            eapply match_states_free_jmp.
            intros.
            apply nextinstr_eq.
            rewrite (Pregmap.gso _ _ H3). simpl_regs. auto.
            rewrite REQ by congruence; auto. simpl_regs.
            rewrite Val.offset_ptr_assoc. f_equal.
            generalize (Ptrofs.repr (align sz 8)).
            generalize (Ptrofs.repr (size_chunk Mptr)).
            intros. rewrite <- Ptrofs.sub_add_l.
            rewrite Ptrofs.sub_add_opp.
            rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero; auto.
            simpl_regs.
            rewrite <- Heqo. f_equal.
            rewrite <- REQ by congruence; auto.
            eapply wf_asm_free_spec in H1; eauto. f_equal. destruct H1 as (SZ & ORA); subst. auto.
            simpl_regs.
            unfold loadvv in Heqo. destr_in Heqo. destr_in Heqo.
            simpl. simpl_regs. rewrite REQ, H by congruence. simpl. rewrite H0. setoid_rewrite FI. subst; eauto.
            auto.
        }
        destruct s1. simpl in *. fold ge.
        edestruct exec_instr_normal as ((rs1' & m1' & EI & SEQ') & NEXT); eauto.
        eexists; split.
        inv SEQ.
        eapply SSAsm.exec_step_internal; eauto.
        rewrite REQ by congruence; eauto.
        apply match_states_normal. auto. auto.
      + inv SEQ. eexists; split. eapply SSAsm.exec_step_builtin; eauto.
        rewrite REQ by congruence; eauto.
        eapply eval_builtin_args_eq_rs. 3: rewrite REQ by congruence; apply H2. intros; symmetry; apply REQ; auto.
        eapply wf_asm_builtin_not_PC; eauto.
        apply match_states_normal.
        constructor. intros. apply nextinstr_nf_eq.
        apply set_res_eq. apply undef_regs_eq. intros; auto.
        simpl. simpl_regs. rewrite set_res_other.
        rewrite Asmgenproof0.undef_regs_other_2. rewrite H; simpl. rewrite H0.
        2: apply pc_not_destroyed_builtin.
        2: eapply wf_asm_builtin_not_PC; eauto.
        destr. destr_in Heqo. inv Heqo.
        intro II; inv II.
        {
          inv H4. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0.
          erewrite wf_asm_pc_repr; eauto.
          apply not_eq_sym. apply Z.lt_neq.
          generalize (Ptrofs.unsigned_range ofs) (instr_size_bound (Pbuiltin ef args res)). lia.
        }
        {
          exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
          intros (o' & ifree & FI & IFREE & RNG).
          erewrite wf_asm_pc_repr in RNG; eauto.
          erewrite wf_asm_pc_repr in Heqo0; eauto.
          generalize (find_instr_no_overlap' instr_size instr_size_bound _ _ _ _ _ FI H1).
          rewrite RNG.
          intros [EQ|NOOV]. subst; inv IFREE.
          generalize (instr_size_bound (Pbuiltin ef args res)) (instr_size_bound ifree). lia.
        }
      + easy.
    - destruct s1. simpl in *. rewrite PCeq in PCnone.
      inv STEP; simpl in *; repeat destr_in PCnone.
  Qed.

  Hypothesis prog_no_rsp: asm_prog_no_rsp instr_size ge.

  Theorem real_asm_correct:
    backward_simulation (SSAsm.semantics instr_size prog) (RealAsm.semantics instr_size prog).
  Proof.
    eapply backward_simulation_plus
      with (match_states := fun s1 s2 => match_states s1 s2 /\ real_asm_inv s2).
    - reflexivity.
    - simpl; intros s1 IS1. inv IS1.
      apply Genv.init_mem_stack in H as STK. apply Mem.alloc_result in H0 as STK'.
      unfold Mem.nextblock in STK'. unfold fresh_block in STK'. rewrite STK in STK'.
      simpl in STK'. subst.
      edestruct (Mem.valid_access_store m1 Mptr stkblock (max_stacksize + align (size_chunk Mptr) 8 - size_chunk Mptr) Vnullptr).
      split.
      red; intros. exploit Mem.perm_alloc_2; eauto. instantiate (1:= ofs).
      split.
      cut (size_chunk Mptr <=  max_stacksize).
      intro.
      assert (0 <= align (size_chunk Mptr) 8). unfold Mptr. destr.
      lia. unfold Mptr. destr; vm_compute; congruence.
      lia. intro. eapply Mem.perm_implies; eauto. apply perm_F_any.
      apply Z.divide_sub_r.
      apply Z.divide_add_r.
      apply align_Mptr_stack_limit.
      apply align_Mptr_align8.
      apply align_size_chunk_divides.
      eexists; econstructor. eauto. eauto.
      simpl.
      rewrite Ptrofs.unsigned_repr. eauto.
      generalize max_stacksize_range. generalize max_stacksize'_range. generalize (size_chunk_pos Mptr).
      generalize (align_le (size_chunk Mptr) 8).
      lia. eauto.
    - simpl; intros s1 s2 IS1 IS2.
      edestruct initial_states_match as (s1' & IS1' & MS); eauto.
      eexists; split; eauto. split; auto. eapply real_initial_inv; eauto.
    - simpl; intros s1 s2 r (MS & INV) FS; inv FS.
      assert (pc_at s1 = None).
      {
        generalize (match_states_PC _ _ MS). intros PCeq.
        unfold pc_at. destr.  simpl in *. rewrite PCeq.
        rewrite H. unfold Vnullptr. destruct ptr64; simpl; auto.
      }
      inv MS; try congruence.
      inv SEQ. simpl in *.
      constructor. rewrite REQ by congruence. auto. rewrite REQ; auto. congruence.
      destruct s1; simpl in *. constructor. congruence. congruence.
    - simpl. intros s1 s2 (MS & INV) SAFE; eapply real_asm_progress; eauto.
    - simpl. intros s2 t s2' STEP s1 (MS & INV) SAFE.
      edestruct real_asm_step as (s1' & STEP' & MS'); eauto.
      exists s1'; split; eauto. apply plus_one; auto. split; auto.
      eapply real_asm_inv_inv; eauto.
Qed.


  Definition match_prog (p: Asm.program) (tp: Asm.program) :=
    match_program (fun _ f tf => transf_fundef instr_size f = OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transf_program instr_size p = OK tp -> match_prog p tp.
  Proof.
    intros. eapply match_transform_partial_program; eauto.
  Qed.

  Lemma match_prog_inv: forall t tp,
    match_prog t tp -> t = tp.
  Proof.
    intros t tp MT. red in MT. red in MT. red in MT.
    destruct MT as (MT & EQ1 & EQ2).
    set (P :=
           (match_ident_globdef (fun (_ : program Asm.fundef unit) (f tf : Asm.fundef) => transf_fundef instr_size f = OK tf)
                                       (@eq unit) t)) in *.
    destruct t, tp. simpl in *. subst.
    apply list_forall2_ind with (P:=P) (l:= prog_defs) (l0:= prog_defs0).
    - auto.
    - intros a1 al b1 bl Pab LP EQ1. inv EQ1.
      f_equal.
      f_equal. red in Pab. red in Pab. destruct Pab as [Pab1 Pab2].
      destruct a1, b1. simpl in *. subst. f_equal.
      destruct g. inv Pab2.
      destruct f. inv H0.
      monadInv H1. unfold transf_function in EQ.
      destr_in EQ; inv EQ.
      simpl in *. inv H1. auto. inv Pab2. inv H0. auto.
    - auto.
Qed.

End PRESERVATION.

  Section PRESERVATION2.

  Variable prog: Asm.program.
  Variable tprog: Asm.program.
  Variable instr_size: instruction -> Z.
  Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
  Hypothesis TRANSF: match_prog instr_size prog tprog.
  Let ge := Genv.globalenv prog.

(*  Hypothesis WF: wf_asm_prog ge. *)
  Hypothesis prog_no_rsp: asm_prog_no_rsp instr_size ge.

  Theorem real_asm_correct':
    backward_simulation (SSAsm.semantics instr_size prog) (RealAsm.semantics instr_size tprog).
  Proof.
    red in TRANSF.
    unfold transf_program in TRANSF.
    exploit match_prog_inv; eauto. intro EQ. subst tprog.
    apply real_asm_correct; auto.
    intros. red. intros. exploit (Genv.find_funct_ptr_transf_partial TRANSF); eauto.
    intros (tf & FFP & TF).
    simpl in TF; monadInv  TF. unfold transf_function in EQ. destr_in EQ.
    eapply wf_asm_function_check_correct; eauto.
  Qed.

  End PRESERVATION2.

