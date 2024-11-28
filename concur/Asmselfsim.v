Require Import Coqlib Mapsrel.
Require Import AST Integers Valuesrel Eventsrel CKLR LanguageInterface Smallstep.
Require Import Op Registersrel.
Require Export Asm.

Require Import CallConv CallconvBig Injp.
Require Import CallconvBig InjectFootprint Injp Extends Ext.

(** ext *)
Section EXT.

Variable prog: program.
Variable w: ext_world.
Variable se: Genv.symtbl.
Let m10 := match w with extw m1 _ _ => m1 end.
Let init_sup := Mem.support m10.
Let ge := Genv.globalenv se prog.

Definition regset_lessdef (rs1 rs2: regset) := forall r, Val.lessdef (rs1 r) (rs2 r).

Inductive match_states : ext_world -> state -> state -> Prop :=
|match_states_normal:
  forall rs m rs' m' wp Hm flag
    (RLD: regset_lessdef rs rs')
    (ACI: ext_acci wp (extw m m' Hm))
    (ACE: ext_acce w (extw m m' Hm)),
  match_states wp (State rs m flag)
               (State rs' m' flag).
(*
Lemma ros_address_lessdef:
  forall ros rs rs',
  regset_lessdef rs rs' ->
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
 *)

Lemma regset_lessdef_set : forall rs1 rs2 r v1 v2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef v1 v2 ->
    regset_lessdef (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  intros. red. intros.
  destruct (Pregmap.elt_eq r r0). subst.
  rewrite !Pregmap.gss. eauto.
  rewrite !Pregmap.gso; try congruence. eauto.
Qed.

Lemma regset_lessdef_nextinstr : forall rs1 rs2,
    regset_lessdef rs1 rs2 ->
    regset_lessdef (nextinstr rs1) (nextinstr rs2).
Proof.
  intros. unfold nextinstr.
  eapply regset_lessdef_set; eauto.
  generalize (H PC). intro.
  inv H0; constructor.
Qed.

Lemma regset_lessdef_undef_regs : forall l rs1 rs2,
    regset_lessdef rs1 rs2 ->
    regset_lessdef (undef_regs l rs1) (undef_regs l rs2).
Proof.
  induction l; intros; simpl; eauto.
  eapply IHl.
  eapply regset_lessdef_set; eauto.
Qed.
  
Lemma regset_lessdef_nextinstr_nf : forall rs1 rs2,
    regset_lessdef rs1 rs2 ->
    regset_lessdef (nextinstr_nf rs1) (nextinstr_nf rs2).
Proof.
  intros. unfold nextinstr_nf.
  eapply regset_lessdef_nextinstr; eauto.
  eapply regset_lessdef_undef_regs; eauto.
Qed.

Lemma regset_lessdef_ptr : forall rs1 rs2 r b ofs,
    regset_lessdef rs1 rs2 ->
    rs1 r = Vptr b ofs ->
    rs2 r = Vptr b ofs.
Proof.
  intros. generalize (H r). intro.
  inv H1; congruence.
Qed.

Lemma step_correct :
  forall s1 t s2, step init_sup ge s1 t s2 ->
  forall wp s1' (MS : match_states wp s1 s1'),
  exists s2', step init_sup ge s1' t s2' /\ match_states wp s2 s2'. 
Proof.
  induction 1; intros; inv MS.
  - (* internal steps *)
    Ltac 
    Ltac solve_exec_instr := split;
                             [econstructor; eauto using regset_lessdef_ptr; try econstructor; eauto | econstructor; eauto ].
    destruct i; inv EXEC; eexists; solve_exec_instr.
    + eapply regset_lessdef_nextinstr. eapply regset_lessdef_set; eauto.
    + eapply regset_lessdef_nextinstr_nf. eapply regset_lessdef_set; eauto.
    + eapply regset_lessdef_nextinstr_nf. eapply regset_lessdef_set; eauto.
    + eapply regset_lessdef_nextinstr_nf. eapply regset_lessdef_set; eauto.
    + simpl. admit. (*load*)
    + admit.
      eapply regset_lessdef_nextinstr_nf. eapply regset_lessdef_set; eauto.
      
    admit.
  - (* builtin steps *)
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
