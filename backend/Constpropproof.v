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
Require Import Values Builtins Events Memory Globalenvs Smallstep.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp ConstpropOpproof Constprop.
Require Import LanguageInterface cklr.Extends.

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
Hypothesis TRANSL: match_prog prog tprog.
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv se tprog.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma functions_translated:
  forall (v tv: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v tv ->
  Genv.find_funct tge tv = Some (transf_fundef (romem_for prog) f).
Proof.
  intros v tv f Hf Hv. apply (Genv.find_funct_transf_id TRANSL).
  unfold Genv.find_funct in *. destruct v; try discriminate. inv Hv. auto.
Qed.

Lemma sig_function_translated:
  forall rm f,
  funsig (transf_fundef rm f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma ros_address_translated:
  forall ros bc rs ae rs',
  genv_match bc ge ->
  ematch bc rs ae ->
  regs_lessdef rs rs' ->
  Val.lessdef (ros_address ge ros rs) (ros_address tge (transf_ros ae ros) rs').
Proof.
  intros until rs'; intros GE EM RLD. destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r); fold (areg ae r); intro VM. generalize (RLD r); intro LD.
  destruct (areg ae r); auto. destruct p; auto.
  predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero; intros; auto.
  subst ofs. exploit vmatch_ptr_gl; eauto.
- (* function symbol *)
  apply Val.lessdef_refl.
Qed.

Lemma const_for_result_correct:
  forall a op bc v sp m,
  const_for_result a = Some op ->
  vmatch bc v a ->
  bc sp = BCstack ->
  genv_match bc ge ->
  exists v', eval_operation tge (Vptr sp Ptrofs.zero) op nil m = Some v' /\ Val.lessdef v v'.
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

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs',
      regs_lessdef rs rs' ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function (romem_for prog) f) sp pc rs').

Inductive match_states: nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' n
           (STACKS: list_forall2 match_stackframes s s')
           (PC: match_pc f rs m n pc pc')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states n (State s f sp pc rs m)
                    (State s' (transf_function (romem_for prog) f) sp pc' rs' m')
  | match_states_call:
      forall s vf args m s' vf' args' m'
           (STACKS: list_forall2 match_stackframes s s')
           (VF: Val.lessdef vf vf')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states O (Callstate s vf args m)
                     (Callstate s' vf' args' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states O (Returnstate s v m)
                     (Returnstate s' v' m').

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' m',
  list_forall2 match_stackframes s s' ->
  regs_lessdef rs rs' ->
  Mem.extends m m' ->
  match_states O (State s f sp pc rs m)
                 (State s' (transf_function (romem_for prog) f) sp pc rs' m').
Proof.
  intros. apply match_states_intro; auto. constructor.
Qed.

Lemma transf_instr_at:
  forall rm f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      generalize (transf_instr_at rm _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct m0 bc0:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS: sound_state prog se m0 bc0 s1) (MS: match_states n1 s1 s1'),
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
  apply match_states_intro; auto.

- (* Iop *)
  rename pc'0 into pc. TransfInstr.
  set (a := eval_static_operation op (aregs ae args)).
  set (ae' := AE.set res a ae).
  assert (VMATCH: vmatch bc v a) by (eapply eval_static_operation_sound; eauto with va).
  assert (MATCH': ematch bc (rs#res <- v) ae') by (eapply ematch_update; eauto).
  destruct (const_for_result a) as [cop|] eqn:?; intros.
+ (* constant is propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto.
+ (* operator is strength-reduced *)
  assert(OP:
     let (op', args') := op_strength_reduction op args (aregs ae args) in
     exists v',
        eval_operation ge (Vptr (fresh_block sps) Ptrofs.zero) op' rs ## args' m = Some v' /\
        Val.lessdef v v').
  { eapply op_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (op_strength_reduction op args (aregs ae args)) as [op' args'].
  destruct OP as [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation ge (Vptr (fresh_block sps) Ptrofs.zero) op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
  { eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto. }
  destruct EV'' as [v'' [EV'' LD'']].
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

- (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk (romem_for prog) am aa).
  assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto).
  destruct (const_for_result av) as [cop|] eqn:?; intros.
+ (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
+ (* strength-reduced *)
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr (fresh_block sps) Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  eapply match_states_succ; eauto. apply set_reg_lessdef; auto.

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
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS.
  intros (m2' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.

- (* Icall *)
  rename pc'0 into pc.
  exploit (ros_address_translated ros); eauto. intros FEXT.
  exploit functions_translated; eauto using ros_address_translated. intro FIND.
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit (ros_address_translated ros); eauto. intros FEXT.
  exploit functions_translated; eauto using ros_address_translated. intro FIND.
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  rename pc'0 into pc. TransfInstr; intros.
Opaque builtin_strength_reduction.
  set (dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res pc') in *.
  set (rm := romem_for prog) in *.
  assert (DFL: (fn_code (transf_function rm f))!pc = Some dfl ->
          exists (n2 : nat) (s2' : state),
            step tge
             (State s' (transf_function rm f) (Vptr (fresh_block sps) Ptrofs.zero) pc rs' m'0) t s2' /\
            match_states n2
             (State s f (Vptr (fresh_block sps) Ptrofs.zero) pc' (regmap_setres res vres rs) m') s2').
  {
    exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
    exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)).
    apply REGS. eauto. eexact P.
    intros (vargs'' & U & V).
    exploit external_call_mem_extends; eauto.
    intros (v' & m2' & A & B & C & D).
    econstructor; econstructor; split.
    eapply exec_Ibuiltin; eauto.
    eapply match_states_succ; eauto.
    apply set_res_lessdef; auto.
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
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
- (* Icond, preserved *)
  rename pc'0 into pc. TransfInstr.
  set (ac := eval_static_condition cond (aregs ae args)).
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  generalize (cond_strength_reduction_correct bc ae rs m EM cond args (aregs ae args) (eq_refl _)).
  destruct (cond_strength_reduction cond args (aregs ae args)) as [cond' args'].
  intros EV1 TCODE.
  left; exists O; exists (State s' (transf_function (romem_for prog) f) (Vptr (fresh_block sps) Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  destruct (resolve_branch ac) eqn: RB.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0.
  destruct b; eapply exec_Inop; eauto.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
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
  left; exists O; exists (State s' (transf_function (romem_for prog) f) (Vptr (fresh_block sps) Ptrofs.zero) pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto.

- (* internal function *)
  exploit functions_translated; eauto. intro FIND'.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  constructor.
  apply init_regs_lessdef; auto.

- (* external function *)
  exploit functions_translated; eauto. intro FIND'.
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  constructor; auto.

- (* return *)
  inv H4. inv H1.
  left; exists O; econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto. constructor. apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall w q1 q2 st1, match_query (cc_c ext) w q1 q2 -> initial_state ge q1 st1 ->
  exists n, exists st2, initial_state tge q2 st2 /\ match_states n st1 st2.
Proof.
  intros. destruct H. CKLR.uncklr. inv H0. destruct H as [vf | ]; try discriminate.
  exploit functions_translated; eauto. intros FIND.
  exists O; exists (Callstate nil vf vargs2 m2); split.
  - setoid_rewrite <- (sig_function_translated (romem_for prog) (Internal f)).
    constructor; auto.
  - constructor; auto. constructor.
Qed.

Lemma transf_final_states:
  forall n st1 st2 r1,
  match_states n st1 st2 -> final_state st1 r1 ->
  exists r2, final_state st2 r2 /\ match_reply (cc_c ext) tt r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  eexists; split. constructor; eauto.
  exists tt; split; constructor; CKLR.uncklr; eauto.
Qed.

Lemma transf_external_states:
  forall n st1 st2 q1, match_states n st1 st2 -> at_external ge st1 q1 ->
  exists q2, at_external tge st2 q2 /\ match_query (cc_c ext) tt q1 q2 /\ match_senv (cc_c ext) tt se se /\
  forall r1 r2 st1', match_reply (cc_c ext) tt r1 r2 -> after_external st1 r1 st1' ->
  exists n' st2', after_external st2 r2 st2' /\ match_states n' st1' st2'.
Proof.
  intros n st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst.
  exploit functions_translated; eauto. intro FIND'.
  eexists. cbn. intuition idtac.
  - econstructor; eauto.
  - destruct VF; try discriminate.
    constructor; CKLR.uncklr; auto.
    destruct v; cbn in *; congruence.
  - inv H1. destruct H0 as ([ ] & _ & H0). inv H0. CKLR.uncklr.
    eexists _, (Returnstate s' vres2 m2'); split; constructor; eauto.
Qed.

End PRESERVATION.

(** The preservation of the observable behavior of the program then
  follows. *)

Require Import Invariant.

Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (vamatch @ cc_c ext) (vamatch @ cc_c ext) (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros MATCH. eapply source_invariant_fsim; eauto using rtl_vamatch. revert MATCH.
  fsim (eapply Build_fsim_properties with (order := lt) (match_states := match_states prog));
    try destruct Hse; cbn.
- destruct 1. cbn. CKLR.uncklr. destruct H; try congruence.
  eapply (Genv.is_internal_transf_id MATCH). intros [|]; auto.
- intros q1 q2 s1 Hq (Hs1 & _).
  eapply transf_initial_states; eauto.
- intros n s1 s2 r1 Hs (Hr1 & _).
  eapply transf_final_states; eauto.
- intros n s1 s2 q1 Hs (Hq1 & _).
  edestruct transf_external_states as (q2 & Hq2 & Hq & _ & Hk); eauto.
  exists tt, q2. repeat apply conj; eauto.
  intros r1 r2 s1' Hr (Hs1' & _). eauto.
- intros s1 t s1' (STEP & [se bc0 m0] & Hse & Hs1 & Hs1') n s2 Hs. subst. cbn in *.
  exploit transf_step_correct; eauto.
  intros [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
  exists n2; exists s2'; split; auto. left; apply plus_one; auto.
  exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl.
- apply lt_wf.
Qed.
