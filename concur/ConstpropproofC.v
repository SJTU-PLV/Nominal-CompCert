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
Require Import CallconvBig VCompBig.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp ConstpropOpproof Constprop.
Require Import LanguageInterface Inject InjectFootprint.

Require Import InvariantC.

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

Inductive gw_j_internal : injp_world -> meminj -> Prop :=
| gw_j_internal_intro :
  forall f m tm Hm j
    (INCRLOCAL: forall b b' d, f b = None -> j b = Some (b', d) ->
                          fst b = Mem.tid(Mem.support m)),
    gw_j_internal (injpw f m tm Hm) j.

Lemma acci_tid1 : forall f m tm Hm f' m' tm' Hm',
    injp_acci (injpw f m tm Hm) (injpw f' m' tm' Hm') ->
    Mem.tid (Mem.support m') = Mem.tid (Mem.support m).
Proof.
  intros. inv H. destruct H10 as [[_ X]_]. congruence.
Qed.
   
Inductive match_states: nat -> injp_world -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp sp' pc rs m f s' pc' rs' m' n j Hm wp
           (STACKS: list_forall2 (match_stackframes j) s s')
           (PC: match_pc f rs m n pc pc')
           (REGS: regset_inject j rs rs')
           (SP: j sp = Some (sp',0))
           (ACCE: injp_acce w (injpw j m m' Hm))
           (ACCI: injp_acci wp (injpw j m m' Hm))
           (GWJ: gw_j_internal wp j)
           (RO: ro_acc m01 m),
      match_states n wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
                    (State s' (transf_function (romem_for prog) f) (Vptr sp' Ptrofs.zero) pc' rs' m')
  | match_states_call:
      forall s vf args m s' vf' args' m' j Hm wp
           (STACKS: list_forall2 (match_stackframes j) s s')
           (VF: Val.inject j vf vf')
           (ARGS: Val.inject_list j args args')
           (ACCE: injp_acce w (injpw j m m' Hm))
           (ACCI: injp_acci wp (injpw j m m' Hm))
           (GWJ: gw_j_internal wp j)
           (RO: ro_acc m01 m),
      match_states O wp (Callstate s vf args m)
                     (Callstate s' vf' args' m')
  | match_states_return:
      forall s v m s' v' m' j Hm wp
           (STACKS: list_forall2 (match_stackframes j) s s')
           (RES: Val.inject j v v')
           (ACCE: injp_acce w (injpw j m m' Hm))
           (ACCI: injp_acci wp (injpw j m m' Hm))
           (GWJ: gw_j_internal wp j)
           (RO: ro_acc m01 m),
      match_states O wp (Returnstate s v m)
                     (Returnstate s' v' m').

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' sp' m' j Hm wp,
  list_forall2 (match_stackframes j) s s' ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  j sp = Some (sp',0) ->
  injp_acce w (injpw j m m' Hm) ->
  injp_acci wp (injpw j m m' Hm) ->
  gw_j_internal wp j ->
  ro_acc m01 m ->
  match_states O wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
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
    injp_acce w (injpw j m1 m2 MEM) ->
    Genv.match_stbls j ge tge.
Proof.
  intros.
  inv H. inv GE. eapply Genv.match_stbls_incr_noglobal; eauto.
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
  forall s1 wp t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS: sound_state prog se s1) (MS: match_states n1 wp s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ match_states n2 wp s2 s2')
  \/ (exists n2, n2 < n1 /\ t = E0 /\ match_states n2 wp s2 s1')%nat.
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
  assert (ACCTL: injp_acc_tl (injpw j m m'0 Hm) (injpw j m' m2' Y)).
  eapply injp_acc_tl_storev; eauto.
  eapply Mem.val_lessdef_inject_compose; eauto.
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
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
  assert (ACCTL : injp_acc_tl (injpw j m m'0 Hm) (injpw j m' m2' B)).
  eapply injp_acc_tl_free with (lo1 := 0); eauto.
  replace (0+0) with 0 by lia.
  replace (0 + fn_stacksize f + 0) with (fn_stacksize f) by lia. eauto.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  econstructor; eauto.
  apply regs_inject; auto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
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
            match_states n2 wp
             (State s f (Vptr (fresh_block sps) Ptrofs.zero) pc' (regmap_setres res vres rs) m') s2').
  {
    exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
    exploit tr_builtin_args; eauto.
    intros (vargs'' & U & V).
    exploit external_call_mem_inject; eauto.
    intros (j' & v' & m2' & A & B & C & D & E & F & G & I & J & K & L).
    assert (ACCTL: injp_acc_tl (injpw j m m'0 Hm) (injpw j' m' m2' C)).
    econstructor; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    econstructor; econstructor; split.
    eapply exec_Ibuiltin; eauto.
    eapply match_states_succ. 3: eauto.
    eapply match_stackframes_incr; eauto.
    apply set_res_inject; auto. red. intros. eauto.
    eauto.
    etransitivity. eauto. eapply injp_acc_tl_e; eauto.
    etransitivity. eauto. eapply injp_acc_tl_i; eauto.
    inv GWJ. constructor. intros. destruct (j b) as [[b'' d']|] eqn :Hjb.
    apply F in Hjb as Heq. rewrite H5 in Heq. inv Heq. eauto.
    exploit I; eauto. intro.
    erewrite <- acci_tid1. eauto. eauto.
    unfold m01 in *. inv ACCE. eapply ro_acc_trans. eauto.
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
  assert (ACCTL : injp_acc_tl (injpw j m m'0 Hm) (injpw j m' m2' B)).
  eapply injp_acc_tl_free_0; eauto. lia.
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  econstructor; eauto.
  destruct or; simpl; auto. instantiate (1:= B).
  etransitivity; eauto. eapply injp_acc_tl_e; eauto.
  etransitivity; eauto. eapply injp_acc_tl_i; eauto.
  eapply ro_acc_trans; eauto.
  eapply ro_acc_free; eauto.

  - (* internal function *)
  exploit match_stbls_incr; eauto. intro MSTB.  
  exploit functions_translated; eauto. intro FIND'.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (f' & m2' & b2 & A & B & C & D & E).
  simpl. unfold transf_function.
  assert (INCR0 :injp_acc_tl (injpw j m m'0 Hm) (injpw f' m' m2' B)).
  eapply injp_acc_tl_alloc; eauto.
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor. 4: eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  constructor.
  apply init_regs_inject; auto. eauto. instantiate (1:= B).
  etransitivity; eauto. eapply injp_acc_tl_e; eauto.
  etransitivity; eauto. eapply injp_acc_tl_i; eauto.
  inv GWJ. constructor. intros. destruct (eq_block b stk).
  subst. apply Mem.alloc_result in H. rewrite H.
  erewrite <- acci_tid1. 2: eauto. eauto. erewrite E in H1. eauto. eauto.
  eapply ro_acc_trans; eauto. eapply ro_acc_alloc; eauto.

  - (* external function *)
  exploit match_stbls_incr; eauto. intro MSTB.  
  exploit functions_translated; eauto. intro FIND'.
  exploit external_call_mem_inject; eauto.
  intros [j' [v' [m2' [A [B [C [D [E [F [G [I [J [K L]]]]]]]]]]]]].
  assert (ACCTL: injp_acc_tl (injpw j m m'0 Hm) (injpw j' m' m2' C)).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  econstructor. 2: eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  inv GWJ. constructor. intros. destruct (j b) as [[b'' d']|] eqn :Hjb.
  apply F in Hjb as Heq. rewrite H1 in Heq. inv Heq. eauto.
  exploit I; eauto. intro.
  erewrite <- acci_tid1. eauto. eauto.
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

Definition ro_w : GS.ccworld (ro @ c_injp) := (se, ((row ge m01), w)).
Infix "@" := GS.cc_compose (at level 30, right associativity).

Lemma transf_initial_states:
  forall q1 q2 st1, GS.match_query  (ro @ c_injp) ro_w q1 q2 -> initial_state ge q1 st1 ->
  exists n, exists st2, initial_state tge q2 st2 /\ match_states n (get w) st1 st2 /\ sound_state prog ge st1.
Proof.
  intros. destruct H as [x [H1 H2]]. inv H0. inv H1. inv H2. cbn in *.
  inv H0. destruct w eqn: Hw. inv H9. clear Hm1 Hm2 Hm3. cbn in *.
  exploit functions_translated; eauto. inversion GE. eauto.
  intros FIND.
  exists O; exists (Callstate nil vf2 vargs2 m2); repeat apply conj.
  - setoid_rewrite <- (sig_function_translated (romem_for prog) (Internal f)).
    constructor; auto.
  - cbn in *. econstructor. 
    all : eauto. constructor. rewrite Hw. reflexivity.
    reflexivity. constructor. intros. congruence.
    eapply ro_acc_refl.
  - cbn in *. eapply sound_memory_ro_sound_state; eauto.
    inversion GE. eauto.
Qed.

Lemma transf_final_states:
  forall gw n st1 st2 r1,
  match_states n gw st1 st2 -> final_state st1 r1 ->
  exists r2 (gw': injp_world), final_state st2 r2 /\ (get w) o-> gw' /\ gw *-> gw' /\ GS.match_reply (ro @ c_injp) (set ro_w (tt,gw')) r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  exists (cr v' m'). exists (injpw j m m' Hm). split. constructor; eauto.
  split. auto. split. auto.
  eexists. split. econstructor; eauto. simpl. constructor. auto.
  eexists. simpl. auto. constructor; eauto.
Qed.

Inductive sound_bc_gw : block_classification -> injp_world -> Prop :=
|sound_bc_gw_intro: forall (bc : block_classification) j m tm Hm
                      (INVALID: forall b, bc b = BCinvalid -> j b = None),
    sound_bc_gw bc (injpw j m tm Hm).

(** The invariant need to be added in ValueAnalysis, can be preserved in local steps (free), builtin
    functions and external functions here *)
Lemma sound_state_extend : forall bc gw, sound_bc_gw bc gw.
Admitted.

Lemma sound_stack_ext1: 
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n bytes,
       sup_In b bound -> bc b = BCinvalid -> fst b = Mem.tid (Mem.support m) -> n >= 0 ->
       Mem.loadbytes m' b ofs n = Some bytes ->
       Mem.loadbytes m b ofs n = Some bytes) ->
  sound_stack bc stk m' bound.
Proof. Admitted.

Lemma sound_stack_exten1:
  forall bc stk m bound (bc1: block_classification),
  sound_stack bc stk m bound ->
  (forall b, sup_In b bound -> fst b = Mem.tid (Mem.support m) -> bc1 b = bc b) ->
  sound_stack bc1 stk m bound.
Proof. Admitted.

(*maybe we cannot increase bound and bc separately? *)
  
Lemma transf_external_states:
  forall n gw st1 st2 q1, match_states n gw st1 st2 -> sound_state prog ge st1 -> at_external ge st1 q1 ->
  exists (wx: GS.ccworld (ro @ c_injp)) q2, at_external tge st2 q2 /\ gw *-> (snd (get wx)) /\ GS.match_query (ro @ c_injp) wx q1 q2 /\ GS.match_senv (ro @ c_injp) wx se tse /\
  forall r1 r2 st1' (gw'': injp_world), (snd (get wx)) o-> gw'' -> GS.match_reply (ro @ c_injp) (set wx (tt,gw'')) r1 r2 -> after_external st1 r1 st1' ->
  exists n' st2', after_external st2 r2 st2' /\ match_states n' gw'' st1' st2' /\ sound_state prog ge st1'.
Proof.
  intros n gw st1 st2 q1 Hst Hs Hq1. destruct Hq1. inv Hst.
  exploit match_stbls_incr; eauto. intro MSTB.
  exploit functions_translated; eauto. simpl.
  intro FIND'.
  inv Hs. exploit mmatch_inj; eauto. eapply mmatch_below; eauto.
  intro.
  exploit Mem.inject_compose. apply H0. apply Hm.
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
  assert (SOUNDBC: sound_bc_gw bc gw).
  eapply sound_state_extend. 
  eexists (se,((row se m),(injpw _ _ _ MEM'))). eexists. cbn. intuition idtac.
  - econstructor; eauto.
  - clear - ACCI jbc JBC_COMPOSE SOUNDBC.
    inv ACCI. econstructor; eauto.
    + 
      red. intros. rewrite JBC_COMPOSE.
      exploit H8; eauto. intro. unfold jbc.
      destruct (bc b) eqn: Hbc; simpl; eauto.
      inv SOUNDBC. exploit INVALID; eauto. intro. congruence.
    + red. intros. rewrite JBC_COMPOSE in H0. eapply H10; eauto.
      unfold jbc in H0.
      destruct (bc b1) eqn: Hbc; simpl in H0; inv H0; eauto.
    + red. intros. rewrite JBC_COMPOSE in H0. eapply H11; eauto.
      unfold jbc in H0.
      destruct (bc b1) eqn: Hbc; simpl in H0; inv H0; eauto.
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
      inv GE. rewrite <- H4 in ACCE.
      inversion ACCE. destruct H15 as [_ H15]. inversion H15. eauto.
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
  - inv GE. rewrite <- H4 in ACCE. inv ACCE. constructor.
    eapply Genv.match_stbls_compose.
    eapply inj_of_bc_preserves_globals; eauto.
    apply MSTB.
    destruct H15 as [X Y]. inversion Y. eauto.
    destruct H16 as [_ Y]. inversion Y. eauto.
  - inv H3. destruct H2 as (r3 & Hr1& Hr2). inv Hr1. inv H2. rename H4 into ROACC.
    inv H1.
    inv Hr2. cbn in *. inv H12. simpl in *. rename f' into j'.
    eexists _, (Returnstate s' vres2 m2'0); split.
    econstructor; eauto. split.
    + (*match_states*)
      destruct H9 as [S9 H9]. destruct H10 as [S10 H10].
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
        unfold j''. destruct (bc b) eqn:BC; try congruence; apply H11;
        unfold compose_meminj, inj_of_bc;
        rewrite BC, H1; reflexivity.
      }
      assert (INCR2: inject_incr j' j'').
      { red. intros.
        destruct (bc b) eqn:BC;
          unfold j''; rewrite BC; eauto.
        destruct (j b) as [[b'' d']|] eqn :Hj.
        -
        exploit H13; eauto. unfold compose_meminj, inj_of_bc.
        rewrite BC. reflexivity.
        inv GWJ. inv SOUNDBC. exploit INVALID; eauto.
        intro. exploit INCRLOCAL; eauto.
        intro. erewrite acci_tid1; eauto.
        intros [A B].
        inversion Hm. exploit mi_freeblocks; eauto. intro. congruence.
        - eauto.
      }
      assert(MEM''' : Mem.inject j'' m'0 m2'0).
      {
        assert (INVALID_LOCAL1 : forall b1 b2 d, bc b1 = BCinvalid -> j b1 = Some (b2, d) ->
                                           fst b1 = Mem.tid (Mem.support m)).
        {
          intros. inv GWJ. inv SOUNDBC. exploit INVALID; eauto.
          intro. exploit INCRLOCAL; eauto. intro.
          erewrite acci_tid1. eauto. eauto.
        }
        assert (INVALID_LOCAL2 : forall b1 b2 d, bc b1 = BCinvalid -> j b1 = Some (b2, d) ->
                                           fst b2 = Mem.tid (Mem.support m')).
        {
          intros. exploit INVALID_LOCAL1; eauto.
          intro. erewrite <- inject_tid. 2: eauto.
          erewrite <- inject_block_tid. apply H4. 2: eauto. eauto.
        }
       clear - INVALID_LOCAL1 INVALID_LOCAL2 JBC_COMPOSE Hm Hm' INCR1 INCR2 H7 H8 H9 H10 H11 H13 H14.
        assert (j''_INV: forall b b' d, j'' b = Some (b',d) -> (j' b = Some (b',d)) \/
                                                           (j b = Some (b',d) /\ bc b = BCinvalid)).
        {
          intros. unfold j'' in H. destruct (bc b) eqn:BC; eauto.
             destruct (j b) as [[bb dd]|] eqn:Hj; eauto.
        }
        assert (j'_INV: forall b b' d, j' b = Some (b',d) -> (~Mem.valid_block m' b' \/ fst b <> Mem.tid (Mem.support m)) \/
                                                         (j b = Some (b',d) /\ bc b <> BCinvalid)).
        {
          intros. destruct (jbc b) as [[b'' d']|] eqn:Hjbc.
          - right.
          rewrite <- JBC_COMPOSE in Hjbc. erewrite H11 in H; eauto. inv H.
          rewrite JBC_COMPOSE in Hjbc.  unfold jbc in Hjbc.
          destruct (bc b); try congruence; split; try congruence; eauto.
          - left. destruct (Nat.eq_dec (fst b) (Mem.tid (Mem.support m))).
            exploit H13; eauto. rewrite JBC_COMPOSE. eauto.
            intros [A B]. eauto. right. auto.
        }
        inv Hm'.
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
          destruct H2 as [A B]. inv Hm. exploit mi_no_overlap0; eauto with mem.
          intros [C|C]. congruence. extlia.
        }
        constructor; eauto.
        -- inv mi_thread. constructor; eauto. red. intros.
           subst j''. simpl in H. destruct (bc b); simpl in H; eauto.
           destruct (j b) eqn: Hj; simpl in H; eauto. inv H. inv Hm.
           inv mi_thread. eapply Hjs0; eauto.
        -- inv mi_inj. constructor; eauto.
           ++ intros. destruct (bc b1) eqn:BC;
              unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              assert (P1: Mem.perm m b1 ofs k p).
              {
                inversion H9. eapply Mem.unchanged_on_perm; eauto.
                red. split; eauto.
                inv Hm. destruct (Mem.sup_dec b1 (Mem.support m)). eauto.
                exploit mi_freeblocks0; eauto. congruence.
              }
              inv H.  inversion H10. eapply unchanged_on_perm; eauto.
              red. split; eauto.
              inv Hm. eauto.
              eapply Mem.perm_inject; eauto.
           ++ intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H. inversion Hm. inv mi_inj. eapply mi_align0; eauto.
              red. intros. exploit H0; eauto.
              intro. inv H9. eapply unchanged_on_perm; eauto with mem.
              red. split; eauto.
              eapply Mem.valid_block_inject_1; eauto.
           ++ 
              intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H.
              assert (P1: Mem.perm m b1 ofs Cur Readable).
              {
                inversion H9. eapply unchanged_on_perm; eauto. split; eauto.
                inv Hm. destruct (Mem.sup_dec b1 (Mem.support m)).
                eauto. exploit mi_freeblocks0; eauto. congruence.
              }
              erewrite Mem.unchanged_on_contents; eauto.
              inv H10.
              erewrite unchanged_on_contents; eauto.
              3: eapply Mem.perm_inject; eauto. inv Hm. inv mi_inj.
              all: (try (eapply memval_inject_incr; eauto)).
              split; eauto. split; eauto.
        -- (* source_range *)
          intros. unfold j''. destruct (bc b); eauto.
          destruct (j b) as [[b' d']|] eqn:Hjb; eauto.
          inv H9. exploit Mem.valid_block_inject_1; eauto. intro.
          exfalso. apply H. eapply unchanged_on_support; eauto.
        -- intros. unfold j'' in H. destruct (bc b); eauto.
           destruct (j b) as [[b'' d']|] eqn:Hjb; eauto. inv H.
           inv H10. exploit Mem.valid_block_inject_2; eauto. intro.
           eapply unchanged_on_support; eauto.
        -- red. intros.
           destruct (j''_INV _ _ _ H0) as [A|[A1 A2]];
             destruct (j''_INV _ _ _ H1) as [B|[B1 B2]]; eauto.
           ++ destruct (j'_INV _ _ _ A) as [C|[C1 C2]]; eauto.
              *
              left. exploit Mem.valid_block_inject_2; eauto. intro.
              destruct C. congruence. exploit INVALID_LOCAL2; eauto.
              intro. erewrite inject_block_tid in H5. 3: eauto.
              erewrite inject_tid in H5; eauto. congruence.
              constructor; eauto.
              * inversion Hm. eapply mi_no_overlap0; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ destruct (j'_INV _ _ _ B) as [C|[C1 C2]]; eauto.
              left. exploit Mem.valid_block_inject_2. apply A1. eauto. intro.
              destruct C. congruence.  exploit INVALID_LOCAL2; eauto.
              intro. erewrite inject_block_tid in H5. 3: eauto.
              erewrite inject_tid in H5; eauto. congruence.
              constructor; eauto.
              inversion Hm. eapply mi_no_overlap0; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ inversion Hm. eapply mi_no_overlap0; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           inversion Hm. eapply mi_representable0; eauto.
           destruct H0. left. eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
           right. eapply H7; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           destruct (Mem.perm_dec m'0 b1 ofs Max Nonempty); eauto.
           apply H7 in p0. left.
           inversion Hm. exploit mi_perm_inv0; eauto.
           inv H10. eapply unchanged_on_perm; eauto. split; eauto. 
           intros [A|B].
           inv H9. eapply unchanged_on_perm; eauto with mem. split; eauto.
           congruence.
           eapply Mem.valid_block_inject_1; eauto. 
      }
      econstructor.
      instantiate (1:= j'').
      * eapply match_stackframes_incr; eauto.
      * eauto.
      * etransitivity; eauto. instantiate (1:= MEM'''). econstructor; eauto.
        split. eauto. eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H1 as [H1 X]. split; auto. red. unfold compose_meminj, inj_of_bc.
        destruct (bc b); simpl; try (rewrite H1); eauto.
        split. eauto. eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H1 as [H1 X]. split; eauto. red. intros. eapply H1; eauto.
        unfold compose_meminj,inj_of_bc in H4.
        destruct (bc b0); simpl in H4; try congruence;
        destruct (j b0) as [[b1 d1]|]; eauto.
        red. intros.
        eapply H13; eauto. unfold compose_meminj, inj_of_bc.
        destruct (bc b1) eqn:BC; try (rewrite H1; reflexivity). reflexivity.
        unfold j'' in H2.
        destruct (bc b1) eqn:BC; eauto. rewrite H1 in H2. eauto.
        red. intros.
        eapply H14; eauto. unfold compose_meminj, inj_of_bc.
        destruct (bc b1) eqn:BC; try (rewrite H1; reflexivity). reflexivity.
        unfold j'' in H2.
        destruct (bc b1) eqn:BC; eauto. rewrite H1 in H2. eauto.
      * econstructor; eauto; try (red; intros; congruence).
        split; eauto with mem. split; eauto with mem.
        -- red. intros. unfold j'' in H2.
           destruct (bc b1) eqn: Hbc; simpl in H2; try congruence.
           destruct (j b1) as [[b2' d]|] eqn:Hjb1; inv H2; try congruence.
           inv GWJ. inv SOUNDBC. exploit INCRLOCAL; eauto.
           intro. exfalso. apply H4. destruct S9. rewrite <- H15.
           erewrite acci_tid1; eauto.
        -- red. intros. unfold j'' in H2.
           destruct (bc b1) eqn: Hbc; simpl in H2; try congruence.
           destruct (j b1) as [[b2' d]|] eqn:Hjb1; inv H2; try congruence.
           inv GWJ. inv SOUNDBC. exploit INCRLOCAL; eauto.
           intro. apply Genv.thread_noglobal in H2. split.
           auto. intro. apply H2. red. red in H4.
           erewrite inject_block_tid. 3: eauto. auto. eauto.
      * constructor.
        intros. unfold j'' in H2.
        destruct (bc b) eqn: Hbc; simpl in H2; try congruence.
        destruct (j b) as [[b2' d']|] eqn:Hjb1; inv H2; try congruence.
        inv GWJ. inv SOUNDBC. exploit INCRLOCAL; eauto.
        intro. destruct S9. rewrite <- H12. erewrite acci_tid1; eauto.
      * eapply ro_acc_trans; eauto.
    + (* sound_state *)
      (* assert (LOCAL: forall b, bc b <> BCinvalid -> fst b = Mem.tid (Mem.support m)). admit. *)
      (* Part 2: constructing bc' from j' *)
      assert (JBELOW: forall b, sup_In b (Mem.support m) -> fst b = Mem.tid (Mem.support m) -> j' b = jbc b).
      {
        intros. destruct (jbc b) as [[b' delta] | ] eqn:EQ.
        rewrite <- JBC_COMPOSE in EQ.
        eapply H11; eauto.
        destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
        exploit H13; eauto. rewrite JBC_COMPOSE. eauto.
        intros [A B]. exfalso. eauto.
      }
      set (f := fun b => if Mem.sup_dec b (Mem.support m)
                        then
                          (if (Nat.eq_dec (fst b) (Mem.tid (Mem.support m))) then bc b else
                             match j' b with
                           | None => BCinvalid
                           | Some _ => BCother end
                          )
                      else match j' b with
                           | None => BCinvalid
                           | Some _ => BCother end).
      assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
      {
        assert (forall b, f b = BCstack -> bc b = BCstack).
        { unfold f; intros. destruct (Mem.sup_dec); auto. destruct (j' b); congruence. }
        intros. apply (bc_stack bc); auto.
      }
      assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
      {
        assert (forall b id, f b = BCglob id -> bc b = BCglob id).
        { unfold f; intros. destruct (Mem.sup_dec); auto. destruct (j' b); try discriminate. }
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
        - destruct (j b) as [[b' delta]|] eqn : Hjb.
          + left. assert (jbc b = Some (b', delta)).
            unfold jbc. destruct (bc b); try congruence.
            rewrite <- JBC_COMPOSE in H2. apply H11 in H2. eauto.
          + right. eauto.
        - destruct (j' b) as [[b' delta] | ].
          left.
          exists b', delta; auto.
          congruence.
      }
      (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  destruct H9 as [S9 H9]. destruct H10 as [S10 H10].
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f.
    destruct (Mem.sup_dec b (Mem.support m)).
    - 
        
    admit.
    rewrite H1. destruct Nat.eq_dec. congruence. admit.
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
      exploit Mem.load_inject. eexact Hm4. eauto. eauto. intros (v' & A & B).
      eapply VMTOP; eauto.
      eapply vmatch_incr; eauto.
      eapply vmatch_top.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply D; eauto.
      erewrite Mem.load_unchanged_on_1 in H2; eauto.
      intros. split. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity. admit.
    - exploit BC'INV; eauto. intros [(b'' & delta & J') | [A [B C]]].
      exploit Mem.loadbytes_inject. eexact Hm4. eauto. eauto. intros (bytes & A & B).
      inv B. inv H15. inv H19. eapply PMTOP; eauto.
      eapply pmatch_incr; eauto.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply E; eauto.
      erewrite Mem.loadbytes_unchanged_on_1 in H2; eauto.
      intros. split. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity. admit.
  }*)
      econstructor; eauto.
      * (*sound_stack*)
        eapply sound_stack_new_bound.
        2: inversion H9; eauto.
        eapply sound_stack_exten.
        instantiate (1:= bc).
        eapply sound_stack_inv; eauto. intros.
        eapply Mem.loadbytes_unchanged_on_1; eauto.
        intros. split. red. rewrite JBC_COMPOSE.
        unfold jbc. rewrite H2. reflexivity. admit.
        intros. auto.
      (* unfold bc'.  simpl. rewrite pred_dec_true; eauto. *)
      * admit.
      * (*romatch*)
        red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        -- 
        exploit RO0; eauto. intros (R & P & Q).
        split; auto.
        split.
        (*bmatch*)
        apply bmatch_incr with bc; auto. rapply bmatch_ext with m; auto.
        intros. inv ROACC. intro. eapply Q; eauto.
        -- destruct (j' b); congruence.
      * (*mmatch*)
        constructor; simpl; intros.
        -- apply ablock_init_sound. apply SMTOP. simpl; congruence.
        -- rewrite PTree.gempty in H2; discriminate.
        -- apply SMTOP; auto.
        -- apply SMTOP; auto.
        -- red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
           inv H9. eauto.
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
  Admitted.

End PRESERVATION.

(** The preservation of the observable behavior of the program then
  follows. *)


Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  GS.forward_simulation (ro @ c_injp)
    (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros MATCH; constructor.
  eapply GS.Forward_simulation.
  - try fsim_skel MATCH.
  - intros se1 se2 w Hse Hse1.
    eapply GS.Build_fsim_properties with (order := lt)
                                       (match_states := fun gw i s1 s2 => match_states prog (snd (snd w)) i (snd gw)  s1 s2
                                                                       /\ sound_state prog se1 s1
                                                                       /\ ro_mem (fst (snd w)) = m01 (snd (snd w)) ).
    + destruct w as [se [rw w]]. cbn in *. destruct Hse as [Hser Hse].
      inv Hser. inv Hse. 
      destruct 1. cbn in *. destruct H3. inv H3. destruct rw. inv H4. cbn in *. inv H7.
      destruct H3; try congruence; eauto.
      eapply (Genv.is_internal_match MATCH); eauto.
      unfold transf_fundef, transf_partial_fundef.
      intros ? [|] [|]; cbn -[transf_function]; inversion 1; auto.
  + destruct w as [se [rw w]]. destruct rw. cbn in *. destruct Hse as [Hser Hse].
    inv Hser.
    intros q1' q2 s1 [q1 [Hqr Hq]] Hs1. inv Hqr. inv Hq. cbn in *. inv H2. simpl in *.
    inv H. cbn in *. inv Hse. cbn in *. clear Hm Hm1.
    exploit transf_initial_states; eauto.
    instantiate (2:= injpw f m1 m2 Hm0).
    econstructor; eauto.
    eexists. split.
    econstructor; eauto. econstructor. eauto.
    econstructor; eauto. econstructor; eauto.
    intros (n & st2 & A & B & C).
    exists n,st2. repeat apply conj; eauto.
  + destruct w as [se [[se' rwm] w]]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros gw n s1 s2 r1 (Hs & SOUND & M0) Hr1.
  exploit transf_final_states; eauto. instantiate (1:= se).
  intros [r2 [gw' [Hr2 [Ha [Hb [r3 [Hc Hd]]]]]]].
  exists r2. exists (tt, gw'). split; eauto. split. simpl. constructor; eauto.
  split. constructor; eauto.
  exists r3. split; eauto. inv Hc.
  inv H. econstructor; eauto. constructor; eauto.
  + destruct w as [se [[se' rwm] w]]. destruct Hse as [Hser Hse].
  inv Hser.
  intros [tt gw] n s1 s2 q1 (Hs & SOUND & M0) Hq1. simpl in gw, tt, M0.
  edestruct transf_external_states as (w' & q2 & Hq2 & ACCI & Hq & Hse' & Hk); eauto.
  destruct w' as [se'' [tt' w']]. simpl in ACCI, tt'.
  exists (se'', (tt', w') ), q2. repeat apply conj; eauto. constructor.
  intros. destruct gw'' as [tt'' gw'']. simpl in gw'', tt'', H0.
  destruct H0. simpl in H3.
  exploit Hk; eauto. 
  intros (n' & st2 & A & B & C).
  exists n',st2. repeat apply conj; eauto.
  + destruct w as [se [[se' rwm] w]]. cbn in *. destruct Hse as [Hser Hse].
    inv Hser.
    intros s1 t s1' STEP gw n s2 (Hs & SOUND & M0). subst. cbn in *.
    exploit transf_step_correct; eauto.
    intros [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
    exists n2; exists s2'; split; auto. left; apply plus_one; auto. split. eauto. split.
    eapply sound_step; eauto. auto.
    exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl.
    split; eauto. split. eapply sound_step; eauto. auto.
  - apply lt_wf.
Qed.
