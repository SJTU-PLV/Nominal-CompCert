(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for constant propagation. *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Builtins Events Memory Globalenvs Smallstep Invariant.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp ConstpropOpproof Constprop.
Require Import LanguageInterface Inject InjectFootprint.

Definition match_prog (prog tprog: program) :=
  match_program (fun _ f tf => tf = transf_fundef (romem_for prog) f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transf_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Variable w: CKLR.world injp.
Hypothesis TRANSL: match_prog prog tprog.
Hypothesis GE: CKLR.match_stbls injp w se tse.
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.

Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse tprog.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma functions_translated (j: meminj):
  Genv.match_stbls j se tse ->
  forall (v tv: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Val.inject j v tv ->
  Genv.find_funct tge tv = Some (transf_fundef (romem_for prog) f).
Proof.
  intros.
  eapply Genv.find_funct_transf; eauto.
Qed.

Lemma sig_function_translated:
  forall rm f,
  funsig (transf_fundef rm f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto.
Qed.

Lemma ros_address_translated:
  forall j ros bc rs ae rs',
  Genv.match_stbls j se tse ->
  genv_match bc ge ->
  ematch bc rs ae ->
  regset_inject j rs rs' ->
  Val.inject j (ros_address ge ros rs) (ros_address tge (transf_ros ae ros) rs').
Proof.
  intros until rs'; intros MSYM GEM EM RLD. destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r); fold (areg ae r); intro VM. generalize (RLD r); intro LD.
  destruct (areg ae r); auto. destruct p; auto.
  predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero; intros; auto.
  subst ofs. exploit vmatch_ptr_gl; eauto.
  intro. eapply Mem.val_lessdef_inject_compose; eauto. simpl.
  eapply symbol_address_inject; eauto.
- (* function symbol *)
  eapply symbol_address_inject; eauto.
Qed.

Lemma const_for_result_correct:
  forall a op bc v sp m,
  const_for_result a = Some op ->
  vmatch bc v a ->
  bc sp = BCstack ->
  genv_match bc ge ->
  exists v', eval_operation ge (Vptr sp Ptrofs.zero) op nil m = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit ConstpropOpproof.const_for_result_correct; eauto.
Qed.

Inductive match_pc (f: function) (rs: regset) (m: mem): nat -> node -> node -> Prop :=
  | match_pc_base: forall n pc,
      match_pc f rs m n pc pc
  | match_pc_nop: forall n pc s pcx,
      f.(fn_code)!pc = Some (Inop s) ->
      match_pc f rs m n s pcx ->
      match_pc f rs m (S n) pc pcx
  | match_pc_cond: forall n pc cond args s1 s2 pcx,
      f.(fn_code)!pc = Some (Icond cond args s1 s2) ->
      (forall b,
        eval_condition cond rs##args m = Some b ->
        match_pc f rs m n (if b then s1 else s2) pcx) ->
      match_pc f rs m (S n) pc pcx.

Lemma match_successor_rec:
  forall f rs m bc ae,
  ematch bc rs ae ->
  forall n pc,
  match_pc f rs m n pc (successor_rec n f ae pc).
Proof.
  induction n; simpl; intros.
- apply match_pc_base.
- destruct (fn_code f)!pc as [[]|] eqn:INSTR; try apply match_pc_base.
+ eapply match_pc_nop; eauto.
+ destruct (resolve_branch (eval_static_condition c (aregs ae l))) as [b|] eqn:STATIC;
  try apply match_pc_base.
  eapply match_pc_cond; eauto. intros b' DYNAMIC.
  assert (b = b').
  { eapply resolve_branch_sound; eauto.
    rewrite <- DYNAMIC. apply eval_static_condition_sound with bc.
    apply aregs_sound; auto. }
  subst b'. apply IHn.
Qed.

Lemma match_successor:
  forall f rs m bc ae pc,
  ematch bc rs ae -> match_pc f rs m num_iter pc (successor f ae pc).
Proof.
  intros. eapply match_successor_rec; eauto.
Qed.

Lemma builtin_arg_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) sp m a v ->
  eval_builtin_arg ge (fun r => rs#r) sp m (builtin_arg_reduction ae a) v.
Proof.
  induction 2; simpl; eauto with barg.
- specialize (H x). unfold areg. destruct (AE.get x ae); try constructor.
  + inv H. constructor.
  + inv H. constructor.
  + destruct (Compopts.generate_float_constants tt); [inv H|idtac]; constructor.
  + destruct (Compopts.generate_float_constants tt); [inv H|idtac]; constructor.
- destruct (builtin_arg_reduction ae hi); auto with barg.
  destruct (builtin_arg_reduction ae lo); auto with barg.
  inv IHeval_builtin_arg1; inv IHeval_builtin_arg2. constructor.
Qed.

Lemma builtin_arg_strength_reduction_correct:
  forall bc sp m rs ae a v c,
  ematch bc rs ae ->
  eval_builtin_arg ge (fun r => rs#r) sp m a v ->
  eval_builtin_arg ge (fun r => rs#r) sp m (builtin_arg_strength_reduction ae a c) v.
Proof.
  intros. unfold builtin_arg_strength_reduction.
  destruct (builtin_arg_ok (builtin_arg_reduction ae a) c).
  eapply builtin_arg_reduction_correct; eauto.
  auto.
Qed.

Lemma builtin_args_strength_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) sp m al vl ->
  forall cl,
  eval_builtin_args ge (fun r => rs#r) sp m (builtin_args_strength_reduction ae al cl) vl.
Proof.
  induction 2; simpl; constructor.
  eapply builtin_arg_strength_reduction_correct; eauto.
  apply IHlist_forall2.
Qed.

Lemma debug_strength_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) sp m al vl ->
  exists vl', eval_builtin_args ge (fun r => rs#r) sp m (debug_strength_reduction ae al) vl'.
Proof.
  induction 2; simpl.
- exists (@nil val); constructor.
- destruct IHlist_forall2 as (vl' & A).
  assert (eval_builtin_args ge (fun r => rs#r) sp m
             (a1 :: debug_strength_reduction ae al) (b1 :: vl'))
  by (constructor; eauto).
  destruct a1; try (econstructor; eassumption).
  destruct (builtin_arg_reduction ae (BA x)); repeat (eauto; econstructor).
Qed.

Lemma builtin_strength_reduction_correct:
  forall sp bc ae rs ef args vargs m t vres m',
  ematch bc rs ae ->
  eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
  external_call ef ge vargs m t vres m' ->
  exists vargs',
     eval_builtin_args ge (fun r => rs#r) sp m (builtin_strength_reduction ae ef args) vargs'
  /\ external_call ef ge vargs' m t vres m'.
Proof.
  intros.
  assert (DEFAULT: forall cl,
    exists vargs',
       eval_builtin_args ge (fun r => rs#r) sp m (builtin_args_strength_reduction ae args cl) vargs'
    /\ external_call ef ge vargs' m t vres m').
  { exists vargs; split; auto. eapply builtin_args_strength_reduction_correct; eauto. }
  unfold builtin_strength_reduction.
  destruct ef; auto.
  exploit debug_strength_reduction_correct; eauto. intros (vargs' & P).
  exists vargs'; split; auto.
  inv H1; constructor.
Qed.

Lemma tr_builtin_arg:
  forall j rs rs' sp sp' m m',
  Genv.match_stbls j se tse ->
  regset_inject j rs rs' ->
  j sp = Some(sp', 0) ->
  Mem.inject j m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
          /\ Val.inject j v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#x; split. constructor; eauto. eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add Ptrofs.zero ofs)).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  rewrite Ptrofs.add_zero. auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. eauto.
- econstructor; split. constructor. simpl. econstructor; eauto.
  rewrite Ptrofs.add_zero_l; rewrite Ptrofs.add_zero. auto.
- assert (Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs)).
  { unfold Genv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
    edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
    econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
  edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
  econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall j rs rs' sp sp' m m',
  Genv.match_stbls j se tse ->
  regset_inject j rs rs' ->
  j sp = Some(sp', 0) ->
  Mem.inject j m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
          /\ Val.inject_list j vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on "option" diagrams of the following form:
<<
                 n
       st1 --------------- st2
        |                   |
       t|                   |t or (? and n' < n)
        |                   |
        v                   v
       st1'--------------- st2'
                 n'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the state [st1] must match its compile-time
  approximations at the current program point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes (j: meminj): stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
    forall res sp pc rs f rs' sp',
        regset_inject j rs rs' ->
        j sp = Some (sp',0) ->
    match_stackframes j
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs)
        (Stackframe res (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) pc rs').

Definition m01 := match w with
                 | injpw f m1 m2 Hm => m1
                 end.

Inductive match_states: nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp sp' pc rs m f s' pc' rs' m' n j MEM
           (STACKS: list_forall2 (match_stackframes j) s s')
           (PC: match_pc f rs m n pc pc')
           (REGS: regset_inject j rs rs')
           (SP: j sp = Some (sp',0))
           (INCR: injp_acc w (injpw j m m' MEM))
           (RO: ro_acc m01 m),
      match_states n (State s f (Vptr sp Ptrofs.zero) pc rs m)
                    (State s' (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) pc' rs' m')
  | match_states_call:
      forall s vf args m s' vf' args' m' j MEM
           (STACKS: list_forall2 (match_stackframes j) s s')
           (VF: Val.inject j vf vf')
           (ARGS: Val.inject_list j args args')
           (INCR: injp_acc w (injpw j m m' MEM))
           (RO: ro_acc m01 m),
      match_states O (Callstate s vf args m)
                     (Callstate s' vf' args' m')
  | match_states_return:
      forall s v m s' v' m' j MEM
           (STACKS: list_forall2 (match_stackframes j) s s')
           (RES: Val.inject j v v')
           (INCR: injp_acc w (injpw j m m' MEM))
           (RO: ro_acc m01 m),
      match_states O (Returnstate s v m)
                     (Returnstate s' v' m').

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' sp' m' j MEM,
  list_forall2 (match_stackframes j) s s' ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  j sp = Some (sp',0) ->
  injp_acc w (injpw j m m' MEM) ->
  ro_acc m01 m ->
  match_states O (State s f (Vptr sp Ptrofs.zero) pc rs m)
                 (State s' (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) pc rs' m').
Proof.
  intros. eapply match_states_intro; eauto. econstructor.
Qed.

Lemma transf_instr_at:
  forall rm f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Lemma match_stbls_incr : forall j m1 m2 MEM,
    injp_acc w (injpw j m1 m2 MEM) ->
    Genv.match_stbls j ge tge.
Proof.
  intros.
  exploit CKLR.match_stbls_acc. 2: apply GE.
  simpl. eauto. intro. simpl in H0. inv H0. eauto.
Qed.

Lemma match_stackframes_incr : forall j j' s s',
    list_forall2 (match_stackframes j) s s' ->
    inject_incr j j' ->
    list_forall2 (match_stackframes j') s s'.
Proof.
  induction 1; intros.
  - constructor.
  - constructor; eauto. inv H.
    constructor; eauto. eapply regset_inject_incr; eauto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      generalize (transf_instr_at rm _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS: sound_state prog se s1) (MS: match_states n1 s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ match_states n2 s2 s2')
  \/ (exists n2, n2 < n1 /\ t = E0 /\ match_states n2 s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; try InvSoundState; try (inv PC; try congruence).

- (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intros.
  left; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Inop, skipped over *)
  assert (s0 = pc') by congruence. subst s0.
  right; exists n; split. lia. split. auto.
  eapply match_states_intro; eauto.

- (* Iop *)
  rename pc'0 into pc. TransfInstr.
  set (a := eval_static_operation op (aregs ae args)).
  set (ae' := AE.set res a ae).
  assert (VMATCH: vmatch bc v a) by (eapply eval_static_operation_sound; eauto with va).
  assert (MATCH': ematch bc (rs#res <- v) ae') by (eapply ematch_update; eauto).
  destruct (const_for_result a) as [cop|] eqn:?; intros.
+ (* constant is propagated *)
  exploit const_for_result_correct; eauto.
  intros (v' & A & B).
  exploit eval_operation_inject; eauto.
  eapply match_stbls_incr; eauto.
  intros (v'' & A' & B').
  rewrite eval_shift_stack_operation in A'.
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto. simpl.
  eapply match_states_intro; eauto.
  eapply match_successor; eauto.
  apply set_reg_inject; auto.
  eapply Mem.val_lessdef_inject_compose; eauto.
+ (* operator is strength-reduced *)
  assert(OP:
     let (op', args') := op_strength_reduction op args (aregs ae args) in
     exists v',
        eval_operation ge (Vptr (fresh_block sps) Ptrofs.zero) op' rs ## args' m = Some v' /\
        Val.lessdef v v').
  { eapply op_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (op_strength_reduction op args (aregs ae args)) as [op' args'].
  destruct OP as [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation tge (Vptr sp' Ptrofs.zero) op' rs'##args' m' = Some v'' /\ Val.inject j v' v'').
  {
    unfold Ptrofs.zero. rewrite <- eval_shift_stack_operation.
    eapply eval_operation_inject; eauto. eapply match_stbls_incr; eauto.
    eapply regs_inject; eauto.
  }
  destruct EV'' as [v'' [EV'' LD'']].
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_intro; eauto.
  eapply match_successor; eauto.
  apply set_reg_inject; auto. eapply Mem.val_lessdef_inject_compose; eauto.

- (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk (romem_for prog) am aa).
  eapply romatch_symtbl_prog in SEVALID as RO'; eauto.
  assert (VM2: vmatch bc v av) by (eapply loadv_sound;  eauto).
  destruct (const_for_result av) as [cop|] eqn:?; intros.
+ (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  exploit eval_operation_inject; eauto.
  eapply match_stbls_incr; eauto.
  intros (v'' & A' & B').
  rewrite eval_shift_stack_operation in A'.
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_inject; auto. eapply Mem.val_lessdef_inject_compose; eauto.
+ (* strength-reduced *)
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr (fresh_block sps) Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_inject. eapply match_stbls_incr; eauto. eauto.
  eapply regs_inject; eauto. eexact P.
  intros (a'' & U & V). rewrite eval_shift_stack_addressing in U.
  exploit Mem.loadv_inject. eauto. eauto. eapply Mem.val_lessdef_inject_compose; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  eapply match_states_succ; eauto. apply set_reg_inject; auto.

- (* Istore *)
  rename pc'0 into pc. TransfInstr.
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr (fresh_block sps) Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_inject. eapply match_stbls_incr; eauto. eauto.
  eapply regs_inject; eauto. eexact P.
  intros (a'' & U & V). rewrite eval_shift_stack_addressing in U.
  exploit Mem.storev_mapped_inject. eauto. eauto.
  eapply Mem.val_lessdef_inject_compose; eauto. apply REGS.
  intros (m2' & X & Y).
  assert (INCR0: injp_acc (injpw j m m'0 MEM) (injpw j m' m2' Y)).
  eapply injp_acc_storev; eauto.
  eapply Mem.val_lessdef_inject_compose; eauto.
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.
  etransitivity. eauto. instantiate (1:= Y).
  eapply injp_acc_storev; eauto.
  eapply Mem.val_lessdef_inject_compose; eauto.
  eapply ro_acc_trans; eauto.
  unfold Mem.storev in H1. destruct a; try congruence.
  eapply ro_acc_store; eauto.
    
- (* Icall *)
  rename pc'0 into pc. exploit match_stbls_incr; eauto. intro MSTB.
  exploit (ros_address_translated j ros); eauto.
  exploit functions_translated; eauto.
  eapply ros_address_translated; eauto.
  intro FIND. TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  econstructor; eauto. constructor; auto.
  econstructor; eauto.
  apply regs_inject; auto.

  - (* Itailcall *)
  exploit match_stbls_incr; eauto. intro MSTB.
  exploit Mem.free_parallel_inject; eauto. intros [m2' [A B]]. simpl in A. rewrite Z.add_0_r in A.
  exploit (ros_address_translated j ros); eauto. intros FEXT.
  exploit functions_translated; eauto using ros_address_translated. intro FIND.
  TransfInstr; intro.
  assert (INCR0 : injp_acc (injpw j m m'0 MEM) (injpw j m' m2' B)).
  eapply injp_acc_free with (lo1 := 0); eauto.
  replace (0+0) with 0 by lia.
  replace (0 + fn_stacksize f + 0) with (fn_stacksize f) by lia. eauto.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  econstructor; eauto.
  apply regs_inject; auto. instantiate (1:= B).
  etransitivity; eauto. inv INCR0.
  eapply ro_acc_trans; eauto. eapply ro_acc_free; eauto.

- (* Ibuiltin *)
  rename pc'0 into pc. TransfInstr; intros.
Opaque builtin_strength_reduction.
  set (dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res pc') in *.
  set (rm := romem_for prog) in *.
  exploit match_stbls_incr; eauto. intro MSTB.
  eapply romatch_symtbl_prog in SEVALID as RO'; eauto.
  assert (DFL: (fn_code (transf_function rm f))!pc = Some dfl ->
          exists (n2 : nat) (s2' : state),
            step tge
             (State s' (transf_function rm f) (Vptr sp' Ptrofs.zero) pc rs' m'0) t s2' /\
            match_states n2
             (State s f (Vptr (fresh_block sps) Ptrofs.zero) pc' (regmap_setres res vres rs) m') s2').
  {
    exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
    exploit tr_builtin_args; eauto.
    intros (vargs'' & U & V).
    exploit external_call_mem_inject; eauto.
    intros (f' & v' & m2' & A & B & C & D & E & F & G).
    econstructor; econstructor; split.
    eapply exec_Ibuiltin; eauto.
    eapply match_states_succ. 3: eauto.
    eapply match_stackframes_incr; eauto.
    apply set_res_inject; auto. red. intros. eauto.
    eauto.
    etransitivity. eauto. instantiate (1:= C).
    constructor; eauto.
    red. eauto using external_call_readonly.
    red. eauto using external_call_readonly.
    red. intros. eapply external_call_max_perm; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    unfold m01 in *. inv INCR. eapply ro_acc_trans. eauto.
    eapply ro_acc_external; eauto.
  }
  destruct ef; auto.
  destruct res; auto.
  destruct (lookup_builtin_function name sg) as [bf|] eqn:LK; auto.
  destruct (eval_static_builtin_function ae am rm bf args) as [a|] eqn:ES; auto.
  destruct (const_for_result a) as [cop|] eqn:CR; auto.
  clear DFL. simpl in H1; red in H1; rewrite LK in H1; inv H1.
  exploit const_for_result_correct; eauto.
  eapply eval_static_builtin_function_sound; eauto.
  intros (v' & A & B).
  exploit eval_operation_inject; eauto.
  intros (v'' & A' & B').
  rewrite eval_shift_stack_operation in A'.
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_inject; auto. eapply Mem.val_lessdef_inject_compose; eauto.
- (* Icond, preserved *)
  rename pc'0 into pc. TransfInstr.
  set (ac := eval_static_condition cond (aregs ae args)).
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  generalize (cond_strength_reduction_correct bc ae rs m EM cond args (aregs ae args) (eq_refl _)).
  destruct (cond_strength_reduction cond args (aregs ae args)) as [cond' args'].
  intros EV1 TCODE.
  left; exists O; exists (State s' (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  destruct (resolve_branch ac) eqn: RB.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0.
  destruct b; eapply exec_Inop; eauto.
  eapply exec_Icond; eauto.
  eapply eval_condition_inject with (vl1 := rs##args'); eauto. eapply regs_inject; eauto. congruence.
  eapply match_states_succ; eauto.

- (* Icond, skipped over *)
  rewrite H1 in H; inv H.
  right; exists n; split. lia. split. auto.
  econstructor; eauto.

- (* Ijumptable *)
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function (romem_for prog) f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function (romem_for prog) f))!pc = Some(Inop pc')).
  { TransfInstr.
    destruct (areg ae arg) eqn:A; auto.
    generalize (EM arg). fold (areg ae arg); rewrite A.
    intros V; inv V. replace n0 with n by congruence.
    rewrite H1. auto. }
  assert (rs'#arg = Vint n).
  { generalize (REGS arg). rewrite H0. intros LD; inv LD; auto. }
  left; exists O; exists (State s' (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Ireturn *)
  exploit Mem.free_parallel_inject; eauto. intros [m2' [A B]]. simpl in A. rewrite Z.add_0_r in A.
  assert (INCR0 : injp_acc (injpw j m m'0 MEM) (injpw j m' m2' B)).
  eapply injp_acc_free with (lo1 := 0); eauto.
  replace (0+0) with 0 by lia.
  replace (0 + fn_stacksize f + 0) with (fn_stacksize f) by lia. eauto.
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  econstructor; eauto.
  destruct or; simpl; auto. instantiate (1:= B).
  etransitivity; eauto. eapply ro_acc_trans; eauto.
  eapply ro_acc_free; eauto.

  - (* internal function *)
  exploit match_stbls_incr; eauto. intro MSTB.  
  exploit functions_translated; eauto. intro FIND'.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (f' & m2' & b2 & A & B & C & D & E).
  simpl. unfold transf_function.
  assert (INCR0 :injp_acc (injpw j m m'0 MEM) (injpw f' m' m2' B)).
  eapply injp_acc_alloc; eauto.
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor. 4: eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  constructor.
  apply init_regs_inject; auto. eauto. instantiate (1:= B).
  etransitivity; eauto. eapply ro_acc_trans; eauto.
  eapply ro_acc_alloc; eauto.

  - (* external function *)
  exploit match_stbls_incr; eauto. intro MSTB.  
  exploit functions_translated; eauto. intro FIND'.
  exploit external_call_mem_inject; eauto.
  intros [f' [v' [m2' [A [B [C [D [E [F G]]]]]]]]].
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  econstructor. 2: eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  etransitivity. eauto. instantiate (1:= C). constructor; eauto.
  red. eauto using external_call_readonly.
  red. eauto using external_call_readonly.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  eapply ro_acc_trans. eauto. constructor.
  red. intros. eapply external_call_readonly; eauto.
  eapply external_call_support; eauto.
  red. intros. eapply external_call_max_perm; eauto.

- (* return *)
  inv STACKS. inv H1.
  left; exists O; econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto. constructor. apply set_reg_inject; auto.
Qed.

Definition ro_w := (se, (row ge m01), w).

Lemma transf_initial_states:
  forall q1 q2 st1, match_query  (ro @ cc_c injp) ro_w q1 q2 -> initial_state ge q1 st1 ->
  exists n, exists st2, initial_state tge q2 st2 /\ match_states n st1 st2 /\ sound_state prog ge st1.
Proof.
  intros. destruct H as [x [H1 H2]]. inv H0. inv H1. inv H2. cbn in *. inv H0. inv H9.
  cbn in *. clear Hm1 Hm0.
  exploit functions_translated; eauto. inversion GE. eauto.
  intros FIND.
  exists O; exists (Callstate nil vf2 vargs2 m2); repeat apply conj.
  - setoid_rewrite <- (sig_function_translated (romem_for prog) (Internal f)).
    constructor; auto.
  - cbn in *. econstructor; eauto. constructor.  rewrite H0. reflexivity.
    eapply ro_acc_refl.
  - eapply sound_memory_ro_sound_state; eauto.
    inversion GE. eauto.
Qed.

Lemma transf_final_states:
  forall n st1 st2 r1,
  match_states n st1 st2 -> final_state st1 r1 ->
  exists r2, final_state st2 r2 /\ match_reply (ro @ cc_c injp) ro_w r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  exists (cr v' m'). split. constructor; eauto.  
  eexists; split. constructor; eauto.
  constructor; eauto.
  eexists ; split; eauto. econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma transf_external_states:
  forall n st1 st2 q1, match_states n st1 st2 -> sound_state prog ge st1 -> at_external ge st1 q1 ->
  exists w' q2, at_external tge st2 q2 /\ match_query (ro @ cc_c injp) w' q1 q2 /\ match_senv (ro @ cc_c injp) w' se tse /\
  forall r1 r2 st1', match_reply (ro @ cc_c injp) w' r1 r2 -> after_external st1 r1 st1' ->
  exists n' st2', after_external st2 r2 st2' /\ match_states n' st1' st2' /\ sound_state prog ge st1'.
Proof.
  intros n st1 st2 q1 Hst Hs Hq1. destruct Hq1. inv Hst.
  exploit match_stbls_incr; eauto. intro MSTB.
  exploit functions_translated; eauto. simpl.
  intro FIND'.
  inv Hs. exploit mmatch_inj; eauto. eapply mmatch_below; eauto.
  intro.
  exploit Mem.inject_compose. apply H0. apply MEM.
  intro MEM'.
  set (jbc := fun b => match bc b with
                    | BCinvalid => None
                    | _ => j b end).
  assert (JBC_COMPOSE: forall b, compose_meminj (inj_of_bc bc) j b = jbc b).
  {
    intro b. unfold compose_meminj,inj_of_bc, jbc.
    destruct (bc b); simpl; eauto;
    destruct (j b) as [[x y]|]; eauto.
  }
  eexists (se,(row se m),(injpw _ _ _ MEM')). eexists. cbn. intuition idtac.
  - econstructor; eauto.
  - assert (sound_memory_ro ge m).
    {
      red. split. eapply romatch_exten; eauto.
      intros.
      clear -RO GE0. destruct GE0.
      unfold ValueAnalysis.bc_of_symtbl. simpl.
      destruct (Genv.invert_symbol se b) eqn:Hinv.
      apply Genv.invert_find_symbol in Hinv. split.
      intro. inv H1. eapply H; eauto.
      intro. apply  H in Hinv. congruence.
      split. intro. congruence. intro. apply H in H1.
      apply Genv.find_invert_symbol in H1. cbn in *. congruence.
      inv GE. inversion INCR. inversion H15. eauto.
    }
    eexists. split. constructor. constructor; eauto.
    econstructor; eauto.
    + cbn. destruct VF; try discriminate. cbn.
      eapply val_inject_compose.
      exploit vmatch_inj; eauto. eauto.
    + cbn.
      eapply CKLRAlgebra.val_inject_list_compose.
      econstructor; eauto. split; eauto.
      revert ARGS0. generalize vargs.
      induction vargs0; simpl; intros; constructor.
      eapply vmatch_inj; eauto. auto.
    + constructor; eauto.
    + unfold Genv.find_funct in H. destruct vf; try congruence; eauto.
  - constructor; eauto.
  - inv GE. inversion INCR. constructor.
    eapply Genv.match_stbls_compose.
    eapply inj_of_bc_preserves_globals; eauto.
    apply MSTB. inversion H15. eauto. inversion H16. eauto.
  - inv H2. destruct H1 as (r3 & Hr1& Hr2). inv Hr1. inv H1. rename H3 into ROACC.
    destruct Hr2 as ([j' s1 s2 MEM''] & Hw' & Hr).
    inv Hw'.
    inv Hr. cbn in *. inv H5. simpl in *.
    eexists _, (Returnstate s' vres2 m2'); split.
    econstructor; eauto. split.
    + (*match_states*)
      set (j'' := fun b => match bc b with
                        |BCinvalid =>
                           if j b then j b else j' b
                        |_ => j' b
                        end
          ).
      assert (INCR1 : inject_incr j j'').
      { red. intros. destruct (block_class_eq (bc b) BCinvalid).
        unfold j''; rewrite e; eauto. rewrite H1.
        reflexivity.
        unfold j''. destruct (bc b) eqn:BC; try congruence; apply H13;
        unfold compose_meminj, inj_of_bc;
        rewrite BC, H1; reflexivity.
      }
      assert (INCR2: inject_incr j' j'').
      { red. intros.
        destruct (bc b) eqn:BC;
          unfold j''; rewrite BC; eauto.
        destruct (j b) as [[b'' d']|] eqn :Hj.
        exploit H14; eauto. unfold compose_meminj, inj_of_bc.
        rewrite BC. reflexivity. intros [A B].
        inversion MEM. exploit mi_freeblocks; eauto. intro. congruence.
        eauto.
      }
      assert(MEM''' : Mem.inject j'' m'0 m2').
      {
       clear - JBC_COMPOSE MEM MEM'' INCR1 INCR2 H7 H8 H9 H10 H11 H12 H13 H14.
        assert (j''_INV: forall b b' d, j'' b = Some (b',d) -> (j' b = Some (b',d)) \/
                                                           (j b = Some (b',d) /\ bc b = BCinvalid)).
        {
          intros. unfold j'' in H. destruct (bc b) eqn:BC; eauto.
             destruct (j b) as [[bb dd]|] eqn:Hj; eauto.
        }
        assert (j'_INV: forall b b' d, j' b = Some (b',d) -> (~Mem.valid_block m' b') \/
                                                         (j b = Some (b',d) /\ bc b <> BCinvalid)).
        {
          intros. destruct (jbc b) as [[b'' d']|] eqn:Hjbc.
          right.
          rewrite <- JBC_COMPOSE in Hjbc. erewrite H13 in H; eauto. inv H.
          rewrite JBC_COMPOSE in Hjbc.  unfold jbc in Hjbc.
          destruct (bc b); try congruence; split; try congruence; eauto.
          left. exploit H14; eauto. rewrite JBC_COMPOSE. eauto.
          intros [A B]. eauto.
        }
        inv MEM''.
        assert (RANGE1 : forall b ofs, bc b = BCinvalid -> loc_unmapped (compose_meminj (inj_of_bc bc) j) b ofs).
        {
          intros. red. unfold compose_meminj, inj_of_bc. rewrite H. reflexivity.
        }
        assert (RANGE2: forall b1 b2 delta ofs k p,
                   bc b1 = BCinvalid -> j b1 = Some (b2, delta) ->
                   Mem.perm m b1 ofs k p ->
                   loc_out_of_reach (compose_meminj (inj_of_bc bc) j) m b2 (ofs + delta)).          
        {
          intros. red. intros b1' delta' MAP P'.
          assert (b1 <> b1' /\ j b1' = Some (b2, delta')).
          {
            rewrite JBC_COMPOSE in MAP. unfold jbc in MAP.
            destruct (bc b1') eqn: BC'; simpl in MAP; try congruence; split; try congruence;
              eauto.
          }
          destruct H2 as [A B]. inv MEM. exploit mi_no_overlap0; eauto with mem.
          intros [C|C]. congruence. extlia.
        }
        constructor; eauto.
        -- inv mi_inj. constructor; eauto.
           ++ intros. destruct (bc b1) eqn:BC;
              unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              assert (P1: Mem.perm m b1 ofs k p).
              {
                inversion H11. apply unchanged_on_perm; eauto.
                inv MEM. destruct (Mem.sup_dec b1 (Mem.support m)).
                eauto. exploit mi_freeblocks0; eauto. congruence.
              }
              inv H. inversion H12. eapply unchanged_on_perm; eauto.
              inv MEM. eauto.
              eapply Mem.perm_inject; eauto.
           ++ intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H. inversion MEM. inv mi_inj. eapply mi_align0; eauto.
              red. intros. exploit H0; eauto.
              intro. inv H11. eapply unchanged_on_perm; eauto with mem.
              eapply Mem.valid_block_inject_1; eauto.
           ++ intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H.
              assert (P1: Mem.perm m b1 ofs Cur Readable).
              {
                inversion H11. apply unchanged_on_perm; eauto.
                inv MEM. destruct (Mem.sup_dec b1 (Mem.support m)).
                eauto. exploit mi_freeblocks0; eauto. congruence.
              }
              erewrite Mem.unchanged_on_contents; eauto.
              inv H12.
              rewrite unchanged_on_contents; eauto.
              2: eapply Mem.perm_inject; eauto. inv MEM. inv mi_inj.
              all: (eapply memval_inject_incr; eauto).
        -- (* source_range *)
          intros. unfold j''. destruct (bc b); eauto.
          destruct (j b) as [[b' d']|] eqn:Hjb; eauto.
          inv H11. exploit Mem.valid_block_inject_1; eauto. intro.
          exfalso. apply H. eapply unchanged_on_support; eauto.
        -- intros. unfold j'' in H. destruct (bc b); eauto.
           destruct (j b) as [[b'' d']|] eqn:Hjb; eauto. inv H.
           inv H12. exploit Mem.valid_block_inject_2; eauto. intro.
           eapply unchanged_on_support; eauto.
        -- red. intros.
           destruct (j''_INV _ _ _ H0) as [A|[A1 A2]];
             destruct (j''_INV _ _ _ H1) as [B|[B1 B2]]; eauto.
           ++ destruct (j'_INV _ _ _ A) as [C|[C1 C2]]; eauto.
              left. exploit Mem.valid_block_inject_2; eauto. intro. congruence.
              inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ destruct (j'_INV _ _ _ B) as [C|[C1 C2]]; eauto.
              left. exploit Mem.valid_block_inject_2. apply A1. eauto. intro. congruence.
              inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           inversion MEM. eapply mi_representable0; eauto.
           destruct H0. left. eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           right. eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           destruct (Mem.perm_dec m'0 b1 ofs Max Nonempty); eauto.
           apply H9 in p0. left.
           inversion MEM. exploit mi_perm_inv0; eauto.
           inv H12. eapply unchanged_on_perm; eauto.
           intros [A|B].
           inv H11. eapply unchanged_on_perm; eauto with mem. congruence.
           eapply Mem.valid_block_inject_1; eauto. 
      }
      econstructor.
      instantiate (1:= j'').
      * eapply match_stackframes_incr; eauto.
      * eauto.
      * etransitivity; eauto. instantiate (1:= MEM'''). econstructor; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. unfold compose_meminj, inj_of_bc.
        destruct (bc b); simpl; try (rewrite H1); eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. intros. eapply H1; eauto.
        unfold compose_meminj,inj_of_bc in H4.
        destruct (bc b0); simpl in H4; try congruence;
        destruct (j b0) as [[b1 d1]|]; eauto.
        red. intros.
        eapply H14; eauto. unfold compose_meminj, inj_of_bc.
        destruct (bc b1) eqn:BC; try (rewrite H1; reflexivity). reflexivity.
        unfold j'' in H2.
        destruct (bc b1) eqn:BC; eauto. rewrite H1 in H2. eauto.
      * eapply ro_acc_trans; eauto.
    + (* sound_state *)
      (* Part 2: constructing bc' from j' *)
      assert (JBELOW: forall b, sup_In b (Mem.support m) -> j' b = jbc b).
      {
        intros. destruct (jbc b) as [[b' delta] | ] eqn:EQ.
        rewrite <- JBC_COMPOSE in EQ.
        eapply H13; eauto.
        destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
        exploit H14; eauto. rewrite JBC_COMPOSE. eauto.
        intros [A B]. exfalso. eauto.
      }
      set (f := fun b => if Mem.sup_dec b (Mem.support m)
                      then bc b
                      else match j' b with None => BCinvalid | Some _ => BCother end).
      assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
      {
        assert (forall b, f b = BCstack -> bc b = BCstack).
        { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
        intros. apply (bc_stack bc); auto.
      }
      assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
      {
        assert (forall b id, f b = BCglob id -> bc b = BCglob id).
        { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
        intros. eapply (bc_glob bc); eauto.
      }
      set (bc' := BC f F_stack F_glob). unfold f in bc'.
      assert (BCINCR: bc_incr bc bc').
      {
        red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
      }
      assert (BC'INV: forall b, bc' b <> BCinvalid -> (exists b' delta, j' b = Some(b', delta)) \/
                                                 (bc b <> BCinvalid /\ j b = None /\ Mem.valid_block m b)).
      {
        simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        rewrite JBELOW by auto. unfold jbc.
        destruct (j b) as [[b' delta]|] eqn : Hjb.
        left.
        exists b', delta. destruct (bc b); try congruence.
        right. eauto.
        destruct (j' b) as [[b' delta] | ]. left.
        exists b', delta; auto.
        congruence.
      }
  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f.
    destruct (Mem.sup_dec b (Mem.support m)).
    rewrite JBELOW in H1 by auto.
    unfold jbc in H1. destruct (bc b); try congruence; eauto.
    rewrite H1; congruence.
  }
  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H1; constructor. eapply PMTOP; eauto.
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m'0 b Ptop).
  {
    intros; split; intros.
    - 
      exploit BC'INV; eauto. intros [(b' & delta & J') | [A [B C]]].
      exploit Mem.load_inject. eexact Hm3. eauto. eauto. intros (v' & A & B).
      eapply VMTOP; eauto.
      eapply vmatch_incr; eauto.
      eapply vmatch_top.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply D; eauto.
      erewrite Mem.load_unchanged_on_1 in H2; eauto.
      intros. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity.
    - exploit BC'INV; eauto. intros [(b'' & delta & J') | [A [B C]]].
      exploit Mem.loadbytes_inject. eexact Hm3. eauto. eauto. intros (bytes & A & B).
      inv B. inv H6. inv H18. eapply PMTOP; eauto.
      eapply pmatch_incr; eauto.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply E; eauto.
      erewrite Mem.loadbytes_unchanged_on_1 in H2; eauto.
      intros. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity.
  }
      econstructor; eauto.
      * (*sound_stack*)
        eapply sound_stack_new_bound.
        2: inversion H11; eauto.
        eapply sound_stack_exten.
        instantiate (1:= bc).
        eapply sound_stack_inv; eauto. intros.
        eapply Mem.loadbytes_unchanged_on_1; eauto.
        intros. red. rewrite JBC_COMPOSE.
        unfold jbc. rewrite H2. reflexivity.
        intros.
        unfold bc'.  simpl. rewrite pred_dec_true; eauto.
      * (*romatch*)
        red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        -- 
        exploit RO0; eauto. intros (R & P & Q).
        split; auto.
        split.
        (*bmatch*)
        apply bmatch_incr with bc; auto. apply bmatch_ext with m; auto.
        intros. inv ROACC. intro. eapply Q; eauto.
        -- destruct (j' b); congruence.
      * (*mmatch*)
        constructor; simpl; intros.
        -- apply ablock_init_sound. apply SMTOP. simpl; congruence.
        -- rewrite PTree.gempty in H2; discriminate.
        -- apply SMTOP; auto.
        -- apply SMTOP; auto.
        -- red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
           inv H11. eauto.
           destruct (j' b) as [[bx deltax] | ] eqn:J'.
           eapply Mem.valid_block_inject_1; eauto.
           congruence.
      * (*genv_match*)
        apply genv_match_exten with bc; auto.
        simpl; intros; split; intros.
        rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
        destruct (Mem.sup_dec b (Mem.support m)). auto. destruct (j' b); congruence.
        simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
      * (*bc_nostack*)
        red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        apply NOSTK; auto.
        destruct (j' b); congruence.
Qed.

End PRESERVATION.

(** The preservation of the observable behavior of the program then
  follows. *)


Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (ro @ cc_c injp) (ro @ cc_c injp)
    (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  fsim (eapply Build_fsim_properties with (order := lt)
                                          (match_states := fun i s1 s2 => match_states prog (snd w) i s1 s2
                                                                       /\ sound_state prog se1 s1
                                                                       /\ ro_mem (snd (fst w)) = m01 (snd w) )).
- destruct w as [[se rw] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser. inv Hse. 
  destruct 1. cbn in *. destruct H3. inv H3. destruct rw. inv H4. cbn in *. inv H7.
  destruct H3; try congruence; eauto.
  eapply (Genv.is_internal_match MATCH); eauto.
  unfold transf_fundef, transf_partial_fundef.
  intros ? [|] [|]; cbn -[transf_function]; inversion 1; auto.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros q1' q2 s1 [q1 [Hqr Hq]] Hs1. inv Hqr. inv Hq. cbn in *. inv H2.
  inv H. cbn in *. inv Hse. cbn in *. clear Hm Hm1.
  exploit transf_initial_states; eauto.
  instantiate (2:= injpw f m1 m2 Hm0).
  econstructor; eauto.
  eexists. split.
  econstructor; eauto. econstructor. eauto.
  econstructor; eauto. econstructor; eauto.
  intros (n & st2 & A & B & C).
  exists n,st2. repeat apply conj; eauto.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros n s1 s2 r1 (Hs & SOUND & M0) Hr1.
  exploit transf_final_states; eauto. instantiate (1:= se).
  intros [r2 [Hf [r3 [Ha Hb]]]].
  exists r2. split; eauto. exists r3. split; eauto. inv Ha.
  inv H. econstructor; eauto. constructor; eauto.
- destruct w as [[se [se' rwm]] w]. destruct Hse as [Hser Hse].
  inv Hser.
  intros n s1 s2 q1 (Hs & SOUND & M0) Hq1.
  edestruct transf_external_states as (w' & q2 & Hq2 & Hq & Hse' & Hk); eauto.
  exists w', q2. repeat apply conj; eauto.
  intros. exploit Hk; eauto. intros (n' & st2 & A & B & C).
  exists n',st2. repeat apply conj; eauto.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros s1 t s1' STEP n s2 (Hs & SOUND & M0). subst. cbn in *.
  exploit transf_step_correct; eauto.
  intros [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
  exists n2; exists s2'; split; auto. left; apply plus_one; auto. split. eauto. split.
  eapply sound_step; eauto. auto.
  exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl.
  split; eauto. split. eapply sound_step; eauto. auto.
- apply lt_wf.
Qed.
