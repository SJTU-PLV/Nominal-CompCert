Require Import Coqlib Mapsrel.
Require Import AST Integers Valuesrel Eventsrel CKLR LanguageInterface Smallstep.
Require Import Op Registersrel.
Require Export RTL.

Require Import CallConv CallconvBig Injp.
Require Import CallconvBig InjectFootprint Injp Extends Ext.

(* Require Import RTLrel. *)

(** ext *)
Section EXT.

Variable prog: program.
Variable w: ext_world.
Variable se: Genv.symtbl.
Let ge := Genv.globalenv se prog.

Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
|match_stackframes_nil:
  match_stackframes nil nil
|match_stackframes_cons: forall stk stk' res f sp pc rs rs',
    match_stackframes stk stk' ->
    regs_lessdef rs rs' ->
    match_stackframes (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
      (Stackframe res f (Vptr sp Ptrofs.zero) pc rs' :: stk').

Inductive match_states : ext_world -> state -> state -> Prop :=
|match_states_normal:
  forall s sp rs m s' rs' m' f pc wp Hm
    (STACKS: match_stackframes s s')
    (RLD: regs_lessdef rs rs')
    (ACI: ext_acci wp (extw m m' Hm))
    (ACE: ext_acce w (extw m m' Hm)),
  match_states wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
               (State s' f (Vptr sp Ptrofs.zero) pc rs' m')
|match_states_call:
    forall s vf args m s' vf' args' m' wp Hm
    (STACKS: match_stackframes s s')
    (VFLD: Val.lessdef vf vf')
    (ARGSLD: Val.lessdef_list args args')
    (ACI: ext_acci wp (extw m m' Hm))
    (ACE: ext_acce w (extw m m' Hm)),
  match_states wp (Callstate s vf args m)
               (Callstate s' vf' args' m')
|match_states_return:
    forall s v m s' v' m' wp Hm
    (STACKS: match_stackframes s s')
    (RETLD: Val.lessdef v v')
    (ACI: ext_acci wp (extw m m' Hm))
    (ACE: ext_acce w (extw m m' Hm)),
  match_states wp (Returnstate s v m)
               (Returnstate s' v' m').


Lemma ros_address_lessdef:
  forall ros rs rs',
  regs_lessdef rs rs' ->
  Val.lessdef (ros_address ge ros rs) (ros_address ge ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
Qed.

Lemma find_funct_lessdef: forall vf vf' fd,
    Genv.find_funct ge vf = Some fd ->
    Val.lessdef vf vf' ->
    Genv.find_funct ge vf' = Some fd.
Proof.
  intros. unfold Genv.find_funct in *. inv H0; simpl in *; try congruence.
Qed.

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

Lemma step_correct :
  forall s1 t s2, step ge s1 t s2 ->
  forall wp s1' (MS : match_states wp s1 s1'),
  exists s2', step ge s1' t s2' /\ match_states wp s2 s2'. 
Proof.
  induction 1; intros; inv MS.
  - eexists; split; econstructor; eauto.
  - edestruct eval_operation_lessdef as [v' [OP LD]]. 3: eauto.
    apply regs_lessdef_regs. eauto. eauto. eexists. split.
    eapply exec_Iop; eauto.
    econstructor; eauto.
    eapply set_reg_lessdef; eauto.
  - edestruct eval_addressing_lessdef as [a' [OP LDa]]. 2: eauto.
    apply regs_lessdef_regs. eauto.
    edestruct Mem.loadv_extends as [v' [LD LDv]]; eauto.
    eexists. split.
    eapply exec_Iload; eauto.
    econstructor; eauto.
    eapply set_reg_lessdef; eauto.
  - edestruct eval_addressing_lessdef as [a' [OP LDa]]. 2: eauto.
    apply regs_lessdef_regs. eauto.
    edestruct Mem.storev_extends as [v' [ST Hm']]; eauto.
    exploit ext_acci_storev. apply H1. apply ST. eauto. 
    eexists. split.
    eapply exec_Istore; eauto.
    econstructor; eauto. instantiate (1:= Hm'). etransitivity; eauto.
    etransitivity; eauto.
  - exploit ros_address_lessdef. eauto. instantiate (1:= ros). fold vf.
    intro.
    eexists.
    split. eapply exec_Icall; eauto. eapply find_funct_lessdef; eauto.
    econstructor; eauto. constructor; eauto. eapply regs_lessdef_regs. eauto.
  - exploit ros_address_lessdef. eauto. instantiate (1:= ros). fold vf.
    intro. exploit Mem.free_parallel_extends; eauto.
    intros [tm' [FREE Hm']]. exploit ext_acci_free. apply H2. apply FREE.  intro AI.
    eexists.
    split. eapply exec_Itailcall; eauto. eapply find_funct_lessdef; eauto.
    econstructor; eauto. eapply regs_lessdef_regs. eauto. instantiate (1:= Hm').
    etransitivity; eauto. etransitivity; eauto.
  - edestruct eval_builtin_args_lessdef as [vargs' [EV ARGSLD]]. apply RLD. eauto. eauto.
    exploit external_call_mem_extends; eauto. intros (vres' & m'1 & A & B & C & D & E).
    assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'1 C)).
    econstructor; eauto using external_call_tid, external_call_support.
    red. intros. eauto using external_call_max_perm.
    red. intros. eauto using external_call_max_perm.
    eexists. split. eapply exec_Ibuiltin; eauto. econstructor; eauto.
    apply set_res_lessdef; eauto. instantiate (1:= C).
    etransitivity; eauto. etransitivity; eauto.
  - exploit eval_condition_lessdef. apply regs_lessdef_regs. eauto. eauto. eauto.
    intro. eexists. split. eapply exec_Icond; eauto. econstructor; eauto.
  - specialize (RLD arg) as ARGLD. rewrite H0 in ARGLD. inv ARGLD.
    eexists. split.
    eapply exec_Ijumptable; eauto. econstructor; eauto.
  - exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE Hm1]].
    exploit ext_acci_free. apply H0. apply FREE. intro.
    eexists. split. eapply exec_Ireturn; eauto. econstructor; eauto.
    destruct or;  eauto. instantiate (1:= Hm1). etransitivity; eauto. etransitivity; eauto.
  - exploit Mem.alloc_extends; eauto. reflexivity. reflexivity.
    intros [m'1 [ALLOC Hm1]]. exploit ext_acci_alloc. apply H. eauto. intro.
    eexists. split. eapply exec_function_internal; eauto. eapply find_funct_lessdef; eauto.
    econstructor; eauto. apply regs_lessdef_init_regs. eauto. instantiate (1:= Hm1).
    etransitivity; eauto. etransitivity; eauto.
  - exploit external_call_mem_extends; eauto. intros (vres' & m'1 & A & B & C & D & E).
    assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'1 C)).
    econstructor; eauto using external_call_tid, external_call_support.
    red. intros. eauto using external_call_max_perm.
    red. intros. eauto using external_call_max_perm.
    eexists. split. eapply exec_function_external; eauto. eapply find_funct_lessdef; eauto.
    econstructor; eauto. instantiate (1:= C).
    etransitivity; eauto. etransitivity; eauto.
  - inv STACKS. eexists. split. eapply exec_return; eauto. econstructor; eauto.
    apply set_reg_lessdef; eauto.
Qed.
      
Lemma initial_correct:
  forall q1 q2 st1, GS.match_query c_ext w q1 q2 -> initial_state ge q1 st1 ->
               exists st2, initial_state ge q2 st2 /\ match_states (get w) st1 st2.
Proof.
  intros. destruct H. inv H2. clear Hm1. inv H0. CKLR.uncklr. 
  eexists. split. econstructor; eauto. eapply find_funct_lessdef; eauto.
  econstructor; eauto. constructor. instantiate (1:= Hm).
  constructor; eauto; red; intros; eauto. rewrite <- H4. reflexivity.
Qed.

Lemma final_correct:
  forall wp st1 st2 r1, match_states wp st1 st2 -> final_state st1 r1 ->
                   exists r2 wp', final_state st2 r2 /\ (get w) o-> wp' /\ ext_acci wp wp' /\
                                                               GS.match_reply (c_ext) (CallconvBig.set w wp') r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  eexists. exists (extw m m' Hm). split.
  - constructor.
  - split. auto. split. auto. constructor; CKLR.uncklr; cbn; auto. constructor.
Qed.

Lemma external_correct:
  forall wp st1 st2 q1, match_states wp st1 st2 -> at_external ge st1 q1 ->
  exists wx q2, at_external ge st2 q2 /\ ext_acci wp (get wx) /\  GS.match_query (c_ext) wx q1 q2 /\ se = se /\
  forall r1 r2 st1' wp'', (get wx) o-> wp'' -> GS.match_reply (c_ext) (CallconvBig.set w wp'') r1 r2 -> after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states wp'' st1' st2'.
Proof.
  intros wp st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst.
  exists (extw m m' Hm). eexists. intuition idtac.
  - econstructor; eauto. eapply find_funct_lessdef; eauto.
  - constructor; CKLR.uncklr; auto. constructor.
    destruct vf; cbn in *; congruence.
  - inv H1. inv H2. inv H4. CKLR.uncklr.
    exists (Returnstate s' vres2 m2'). split. econstructor; eauto. simpl in H1. inv H1.
    econstructor; eauto. reflexivity. etransitivity. eauto. simpl in H0. eauto.
Qed.

End EXT.

Theorem RTL_ext_selfsim prog :
  GS.forward_simulation (c_ext) (RTL.semantics prog) (RTL.semantics prog).
Proof.
  constructor.
  eapply GS.Forward_simulation.
  + reflexivity.
  + intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  eapply GS.forward_simulation_step; subst.
  - destruct 1. CKLR.uncklr. destruct H; cbn; try congruence.
  - eapply initial_correct; eauto.
  - eapply final_correct; eauto.
  - eapply external_correct; eauto.
  - intros. eapply step_correct; eauto.
  + auto using well_founded_ltof.
Qed.


Section INJP.

Variable prog: program.
Variable w: injp_world.
Variable se: Genv.symtbl.
Variable tse : Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse prog.

Hypothesis GE: CKLR.match_stbls injp w se tse.

Inductive match_stackframes_injp (j: meminj): list stackframe -> list stackframe -> Prop :=
|match_stackframes_injp_nil:
  match_stackframes_injp j nil nil
|match_stackframes_injp_cons: forall stk stk' res f sp tsp pc rs rs',
    match_stackframes_injp j stk stk' ->
    j sp = Some (tsp,0) ->
    regset_inject j rs rs' ->
    match_stackframes_injp j
      (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
      (Stackframe res f (Vptr tsp Ptrofs.zero) pc rs' :: stk').

Inductive match_states_injp : injp_world -> state -> state -> Prop :=
|match_states_normal':
  forall s sp rs m s' rs' m' tsp f pc wp j Hm 
    (STACKS: match_stackframes_injp j s s')
    (RLD: regset_inject j rs rs')
    (JSP: j sp = Some (tsp,0))
    (ACI: injp_acci wp (injpw j m m' Hm))
    (ACE: injp_acce w (injpw j m m' Hm)),
  match_states_injp wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
               (State s' f (Vptr tsp Ptrofs.zero) pc rs' m')
|match_states_call':
    forall s vf args m s' vf' args' m' wp j Hm
    (STACKS: match_stackframes_injp j s s')
    (VFLD: Val.inject j vf vf')
    (ARGSLD: Val.inject_list j args args')
    (ACI: injp_acci wp (injpw j m m' Hm))
    (ACE: injp_acce w (injpw j m m' Hm)),
  match_states_injp wp (Callstate s vf args m)
               (Callstate s' vf' args' m')
|match_states_return':
    forall s v m s' v' m' wp j Hm
    (STACKS: match_stackframes_injp j s s')
    (RETLD: Val.inject j v v')
    (ACI: injp_acci wp (injpw j m m' Hm))
    (ACE: injp_acce w (injpw j m m' Hm)),
  match_states_injp wp (Returnstate s v m)
               (Returnstate s' v' m').

Lemma match_stackframes_incr : forall j j' s s',
    match_stackframes_injp j s s' ->
    inject_incr j j' ->
    match_stackframes_injp j' s s'.
Proof.
  induction 1; intros.
  - constructor.
  - constructor; eauto. red. intros. red in H1. exploit H1; eauto.
Qed.

Lemma ros_address_inject:
  forall ros rs rs' j ge tge,
  Genv.match_stbls j ge tge ->
  regset_inject j rs rs' ->
  Val.inject j (ros_address ge ros rs) (ros_address tge ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
  eapply symbol_address_inject; eauto.
Qed.

Lemma find_funct_inject: forall vf vf' fd j,
    Genv.match_stbls j ge tge ->
    Genv.find_funct ge vf = Some fd ->
    Val.inject j vf vf' ->
    Genv.find_funct tge vf' = Some fd.
Proof.
  intros. inv H1; simpl in *; try congruence.
  destr_in H0. unfold Genv.find_funct_ptr in H0.
  inv H. destr_in H0.
  unfold ge in Heqo. rewrite Genv.find_def_spec in Heqo.
  destr_in Heqo. apply Genv.invert_find_symbol in Heqo0. exploit Genv.genv_symb_range; eauto. intro Hsup.
  exploit mge_dom; eauto. intros [b2' X]. rewrite H2 in X. inv X.
  exploit mge_symb; eauto. intro HFIND. apply HFIND in Heqo0 as FIND'.
  rewrite pred_dec_true. unfold Genv.find_funct_ptr. unfold tge. rewrite Genv.find_def_spec.
  apply Genv.find_invert_symbol in FIND'. rewrite FIND'. rewrite Heqo. eauto. eauto.
Qed.


Lemma find_funct_inject': forall j b1 ofs1 b2 ofs2,
    Genv.match_stbls j ge tge ->
    Val.inject j (Vptr b1 ofs1) (Vptr b2 ofs2)->
    Genv.find_funct ge  (Vptr b1 ofs1) = Genv.find_funct tge  (Vptr b2 ofs2).
Proof.
  intros. destruct (Genv.find_funct ge (Vptr b1 ofs1)) eqn: Hf.
  symmetry. eapply find_funct_inject; eauto.
  symmetry. inv H0.
  destruct (Mem.sup_dec b1 se.(Genv.genv_sup)).
  - edestruct Genv.mge_dom; eauto. rewrite H4 in H0. inv H0.
    rewrite Ptrofs.add_zero.
    unfold Genv.find_funct, Genv.find_funct_ptr in *. destr.
    unfold tge. rewrite Genv.find_def_spec.
    destruct (Genv.invert_symbol tse x) eqn: Hi; eauto.
    inv H. apply Genv.invert_find_symbol in Hi. eapply mge_symb in Hi; eauto.
    unfold ge in Hf. rewrite Genv.find_def_spec in Hf.
    apply Genv.find_invert_symbol in Hi. simpl in Hi. setoid_rewrite Hi in Hf. eauto.
  - unfold Genv.find_funct, Genv.find_funct_ptr. destr.
    unfold tge. rewrite Genv.find_def_spec.
    destruct (Genv.invert_symbol tse b2) eqn: Hi; eauto.
    exfalso. apply n. inv H. 
    eapply Genv.genv_symb_range; eauto. eapply mge_symb; eauto. 
    eapply Genv.invert_find_symbol; eauto. 
Qed.

Lemma injp_acce_stbl: forall w w' se tse,
    match_stbls injp w se tse ->
    injp_acce w w' ->
    match_stbls injp w' se tse.
Proof.
  intros. inv H. inv H0.
  constructor; eauto.
  eapply Genv.match_stbls_incr_noglobal; eauto.
  destruct H10 as [_ [A _]]. eauto.
  destruct H11 as [_ [B _]]. eauto.
Qed.

Hint Resolve injp_acc_tl_i injp_acc_tl_e: core.

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto.
Qed.

Lemma step_correct_injp :
  forall s1 t s2, step ge s1 t s2 ->
  forall wp s1' (MS : match_states_injp wp s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states_injp wp s2 s2'. 
Proof.
  induction 1; intros; inv MS; exploit injp_acce_stbl; eauto; intro Hse.
  - eexists; split; econstructor; eauto.
  - inv Hse. edestruct eval_operation_inject as [v' [OP LD]]. 5: eauto.
    eauto. eauto. eapply regs_inject; eauto.  eauto.
    rewrite eval_shift_stack_operation in OP.
    eexists. split.
    eapply exec_Iop; eauto. econstructor; eauto.
    eapply set_reg_inject; eauto.
  - inv Hse.
    edestruct eval_addressing_inject as [a' [OP LDa]]. 4: eauto.
    eauto. eauto. eapply regs_inject; eauto.
    rewrite eval_shift_stack_addressing in OP.
    edestruct Mem.loadv_inject as [v' [LD INJv]]; eauto.
    eexists. split.
    eapply exec_Iload; eauto.
    econstructor; eauto.
    eapply set_reg_inject; eauto.
  - inv Hse.
    edestruct eval_addressing_inject as [a' [OP LDa]]. 2: eauto.
    eauto. eapply regs_inject; eauto. eauto.
    rewrite eval_shift_stack_addressing in OP.
    edestruct Mem.storev_mapped_inject as [v' [ST Hm']]; eauto.
    exploit injp_acc_tl_storev. apply H1. apply ST. eauto. intro.
    eexists. split.
    eapply exec_Istore; eauto.
    econstructor; eauto. instantiate (1:= Hm').
    etransitivity; eauto.
    etransitivity; eauto.
  - inv Hse.
    exploit ros_address_inject; eauto. instantiate (1:= ros).
    simpl in vf. fold vf. intro.
    eexists.
    split. eapply exec_Icall; eauto. eapply find_funct_inject; eauto.
    econstructor; eauto. constructor; eauto. eapply regs_inject. eauto.
  - inv Hse.
    exploit ros_address_inject; eauto. instantiate (1:= ros).
    simpl in vf. fold vf. intro.
    exploit Mem.free_parallel_inject; eauto.
    intros [tm' [FREE Hm']]. simpl in FREE. rewrite Z.add_0_r in FREE.
    exploit injp_acc_tl_free_0. apply H2.
    apply FREE. eauto. lia. intro.
    eexists.
    split. eapply exec_Itailcall; eauto. eapply find_funct_inject; eauto.
    econstructor; eauto. eapply regs_inject; eauto.
    instantiate (1:= Hm').
    etransitivity; eauto. etransitivity; eauto.
  - inv Hse. generalize (eval_builtin_args_rel injp (injpw j m m'0 Hm)).
    intro. red in H2. exploit H2. 5: eauto. simpl. eauto. red. simpl. apply RLD. simpl. eauto.
    constructor. intros [vargs' [EV INJb]]. simpl in INJb.
    exploit external_call_mem_inject; eauto. intros (j' & vres' & m'1 & A & B & C & D & E & F & G & I & J & K & L).
    assert (ACC: injp_acc_tl (injpw j m m'0 Hm) (injpw j' m' m'1 C)).
    econstructor; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    eexists. split. eapply exec_Ibuiltin; eauto. econstructor.
    eapply match_stackframes_incr; eauto.
    eapply set_res_inject; eauto. 
    eapply regset_inject_incr; eauto. eauto.
    instantiate (1:= C).
    etransitivity; eauto. etransitivity; eauto.
  - exploit eval_condition_inject. apply regs_inject. eauto. eauto. eauto.
    intro. eexists. split. eapply exec_Icond; eauto. econstructor; eauto.
  - specialize (RLD arg) as ARGLD. rewrite H0 in ARGLD. inv ARGLD.
    eexists. split.
    eapply exec_Ijumptable; eauto. econstructor; eauto.
  - exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE Hm1]]. simpl in FREE. rewrite Z.add_0_r in FREE.
    exploit injp_acc_tl_free_0. apply H0. apply FREE. eauto. lia. intro.
    eexists. split. eapply exec_Ireturn; eauto. econstructor; eauto.
    destruct or;  eauto. instantiate (1:= Hm1). etransitivity; eauto. etransitivity; eauto.
  - inv Hse. exploit Mem.alloc_parallel_inject; eauto. reflexivity. reflexivity.
    intros [f' [m'1 [stk' [ALLOC [Hm' [INCR [JSP DIFF]]]]]]]. exploit injp_acc_tl_alloc. apply H. eauto. eauto.
    eauto. eauto. intro.
    eexists. split. eapply exec_function_internal; eauto. eapply find_funct_inject; eauto.
    econstructor. 3: eauto. eapply match_stackframes_incr; eauto.
    eapply init_regs_inject. eauto.
    instantiate (1:= Hm').
    etransitivity; eauto. etransitivity; eauto.
  - inv Hse. exploit external_call_mem_inject; eauto.
    intros (f' & vres' & m'1 & A & B & C & D & E & F & G & I & J & K & L).
    assert (ACCTL: injp_acc_tl (injpw j m m'0 Hm) (injpw f' m' m'1 C)).
    econstructor; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intro. eauto using external_call_readonly; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    red. intros. eapply external_call_max_perm; eauto.
    eexists. split. eapply exec_function_external; eauto. eapply find_funct_inject; eauto.
    econstructor. eapply match_stackframes_incr; eauto. eauto. instantiate (1:= C).
    etransitivity; eauto. etransitivity; eauto.
  - inv STACKS. eexists. split. eapply exec_return; eauto. econstructor; eauto.
    apply set_reg_inject; eauto.
Qed.
      
Lemma initial_correct':
  forall q1 q2 st1, GS.match_query c_injp w q1 q2 -> initial_state ge q1 st1 ->
               exists st2, initial_state tge q2 st2 /\ match_states_injp (get w) st1 st2.
Proof.
  intros. destruct H. inv H2. clear Hm1 . inv H0. rewrite <- H4 in H, H1. simpl in *.
  eexists. split. econstructor; eauto. eapply find_funct_inject; eauto. rewrite <- H4 in GE. inv GE. auto.
  econstructor; eauto. constructor. instantiate (1:= Hm).
  constructor; eauto; try red; intros; try congruence; eauto.
  split; eauto with mem. split; eauto with mem.
  rewrite <- H4. reflexivity.
Qed.

Lemma final_correct':
  forall wp st1 st2 r1, match_states_injp wp st1 st2 -> final_state st1 r1 ->
                   exists r2 wp', final_state st2 r2 /\ (get w) o-> wp' /\ injp_acci wp wp' /\
                                                               GS.match_reply (c_injp) (CallconvBig.set w wp') r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  eexists. exists (injpw j m m' Hm). split.
  - constructor.
  - split. auto. split. auto. constructor; cbn; auto.
Qed.

Lemma external_correct':
  forall wp st1 st2 q1, match_states_injp wp st1 st2 -> at_external ge st1 q1 ->
  exists wx q2, at_external tge st2 q2 /\ injp_acci wp (get wx) /\  GS.match_query (c_injp) wx q1 q2 /\  GS.match_senv c_injp wx ge tge /\
  forall r1 r2 st1' wp'', (get wx) o-> wp'' -> GS.match_reply (c_injp) (CallconvBig.set w wp'') r1 r2 -> after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states_injp wp'' st1' st2'.
Proof.
  intros wp st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst. exploit injp_acce_stbl; eauto. intro Hse.
  exists (injpw j m m' Hm). eexists. intuition idtac.
  - econstructor; eauto. eapply find_funct_inject; eauto. inv Hse. eauto.
  - constructor; auto. constructor.
    destruct vf; cbn in *; congruence.
  - inv H1. inv H2. inv H4. simpl in *. rewrite <- H1 in H3. simpl in H3.
    exists (Returnstate s' vres2 m2'). split. econstructor; eauto. simpl in H1. inv H1.
    econstructor. 2: eauto. eapply match_stackframes_incr; eauto. inv H0. eauto.
    reflexivity.  etransitivity; eauto.
Qed.

End INJP.

Theorem RTL_injp_selfsim prog :
  GS.forward_simulation (c_injp) (RTL.semantics prog) (RTL.semantics prog).
Proof.
  constructor.
  eapply GS.Forward_simulation.
  + reflexivity.
  + intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  eapply GS.forward_simulation_step; subst.
  - destruct 1. destruct H; cbn; try congruence.
    inv H1. simpl in *. inv Hse.
    unfold Genv.is_internal. erewrite <- find_funct_inject'; eauto.
  - eapply initial_correct'; eauto.
  - eapply final_correct'; eauto.
  - intros. eapply external_correct'; eauto.
  - intros. eapply step_correct_injp; eauto.
  + auto using well_founded_ltof.
Qed.

Require Import ValueAnalysis Invariant CallconvBig InvariantC.
Require Import VCompBig.

Lemma RTL_ro_selfsim prog:
  GS.forward_simulation ro (RTL.semantics prog) (RTL.semantics prog).
Proof.
  eapply preserves_fsim. eapply RTL_ro_preserves.
Qed.

Lemma va_interface_selfsim prog :
   GS.forward_simulation (ro @ c_injp) (RTL.semantics prog) (RTL.semantics prog).
Proof.
  intros. eapply st_fsim_vcomp. eapply RTL_ro_selfsim. eapply RTL_injp_selfsim.
Qed.
