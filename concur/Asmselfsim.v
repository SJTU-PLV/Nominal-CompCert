Require Import Coqlib Mapsrel.
Require Import AST Integers Valuesrel Eventsrel CKLR LanguageInterface Smallstep.
Require Import Op Registersrel.
Require Export Asm Asmrel.

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
Let sem := Asm.semantics prog.

Definition regset_lessdef (rs1 rs2: regset) := forall r, Val.lessdef (rs1 r) (rs2 r).

Inductive match_states : ext_world -> state -> state -> Prop :=
|match_states_normal:
  forall rs m rs' m' wp Hm flag
    (RLD: regset_lessdef rs rs')
    (ACI: ext_acci wp (extw m m' Hm))
    (ACE: ext_acce w (extw m m' Hm)),
  match_states wp (State rs m flag)
    (State rs' m' flag).

Inductive match_states' : ext_world -> (sup * state) -> (sup * state ) -> Prop  :=
|match_states'_intro:
  forall wp sup1 sup2 s1 s2
    (SUP1: sup1 = init_sup)
    (SUP2: sup2 = init_sup)
    (MS: match_states wp s1 s2),
    match_states' wp (sup1, s1) (sup2,s2).
  
(*
Lemma ros_address_lessdef:
  forall ros rs rs',
  regset_lessdef rs rs' ->
  Val.lessdef (ros_address ge ros rs) (ros_address ge ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
Qed.
 *)

Lemma find_funct_lessdef: forall vf vf' fd,
    Genv.find_funct ge vf = Some fd ->
    Val.lessdef vf vf' ->
    Genv.find_funct ge vf' = Some fd.
Proof.
  intros. unfold Genv.find_funct in *. inv H0; simpl in *; try congruence.
Qed.
(*
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

Lemma regset_lessdef_set_pair : forall rs1 rs2 p v1 v2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef v1 v2 ->
    regset_lessdef (set_pair p v1 rs1) (set_pair p v2 rs2).
Proof.
  intros. unfold set_pair. destruct p.
  eapply regset_lessdef_set; eauto.
  eapply regset_lessdef_set; eauto.  eapply regset_lessdef_set; eauto.
  inv H0; constructor; eauto.
  inv H0; constructor; eauto.
Qed.

Lemma regset_lessdef_undef_caller_save_regs : forall rs1 rs2,
    regset_lessdef rs1 rs2 ->
    regset_lessdef (undef_caller_save_regs rs1) (undef_caller_save_regs rs2).
Proof.
  intros. unfold undef_caller_save_regs. red. intros. destr; eauto.
Qed.

Lemma regset_lessdef_set_res : forall res rs1 rs2 v1 v2,
    regset_lessdef rs1 rs2 ->
    Val.lessdef v1 v2 ->
    regset_lessdef (set_res res v1 rs1) (set_res res v2 rs2).
Proof.
  induction res; intros; simpl; eauto.
  - eapply regset_lessdef_set; eauto.
  - eapply IHres2. eapply IHres1. eauto.
    inv H0; constructor.
    inv H0; constructor.
Qed.

Ltac rs_lessdef :=
  match goal with
  | [ |- regset_lessdef (nextinstr_nf _ ) (nextinstr_nf _) ] =>
      eapply regset_lessdef_nextinstr_nf; eauto
  | [ |- regset_lessdef (nextinstr _) (nextinstr _) ] =>
      eapply regset_lessdef_nextinstr; eauto
  | [ |- regset_lessdef (undef_regs _ _) (undef_regs _ _) ] =>
      eapply regset_lessdef_undef_regs; eauto
  | [ |- regset_lessdef (undef_caller_save_regs _) (undef_caller_save_regs _) ] =>
      eapply regset_lessdef_undef_caller_save_regs; eauto
  | [ |- regset_lessdef (_ # _ <- _ ) (_ # _ <- _) ] =>
      eapply regset_lessdef_set; eauto
  | [ |- regset_lessdef (set_pair _ _ _ ) (set_pair _ _ _) ] =>
      eapply regset_lessdef_set_pair; eauto
  | [ |- regset_lessdef (set_res _ _ _ ) (set_res _ _ _) ] =>
      eapply regset_lessdef_set_res; eauto
  end.

Ltac rs_lessdefs := repeat rs_lessdef.


(** For exec_load *)

Lemma eval_addrmode_lessdef : forall rs1 rs2 a se,
    regset_lessdef rs1 rs2 ->
    Val.lessdef (eval_addrmode se a rs1) (eval_addrmode se a rs2).
Proof.
Admitted.


(** For exec_store *)



Lemma step_correct:
  forall s1 t s2, step init_sup ge s1 t s2 ->
  forall wp s1' (MS : match_states wp s1 s1'),
  exists s2', step init_sup ge s1' t s2' /\ match_states wp s2 s2'. 
Proof.
  induction 1; intros; inv MS.
  - (* internal steps *)
    admit.
    (*
    (* only for trivial instrs *)
    Ltac solve_exec_instr1 :=
      eexists; split;
      [econstructor; eauto using regset_lessdef_ptr;
       econstructor; eauto |
        econstructor; eauto; rs_lessdefs ].
    (* general pattern after state existention*)
     Ltac solve_exec_instr :=
      eexists; split;
      [econstructor; eauto using regset_lessdef_ptr;
       try econstructor; eauto |
        econstructor; eauto; try rs_lessdefs ].
    destruct i; inv EXEC; try solve_exec_instr1.
    + (*exec_load*)
      unfold exec_load in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.loadv_extends; eauto. intros [v' [Hl Hv]].
      solve_exec_instr. simpl. unfold exec_load. rewrite Hl. reflexivity.
      rs_lessdefs.
    + (*exec_load*)
      unfold exec_load in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.loadv_extends; eauto. intros [v' [Hl Hv]].
      solve_exec_instr. simpl. unfold exec_load. rewrite Hl. reflexivity.
      rs_lessdefs.
    + (*exec_store*)
      unfold exec_store in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.storev_extends; eauto. intros [m'1 [Hs He]].
      exploit ext_acci_storev. apply Heqo. apply Hs. eauto. intro ACI1.
      solve_exec_instr. simpl. unfold exec_store. rewrite Hs. reflexivity.
      rs_lessdefs. instantiate (1:= He). etransitivity; eauto. etransitivity; eauto.
    + (*exec_store*)
      unfold exec_store in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.storev_extends; eauto. intros [m'1 [Hs He]].
      exploit ext_acci_storev. apply Heqo. apply Hs. eauto. intro ACI1.
      solve_exec_instr. simpl. unfold exec_store. rewrite Hs. reflexivity.
      rs_lessdefs. instantiate (1:= He). etransitivity; eauto. etransitivity; eauto.
    + unfold exec_load in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.loadv_extends; eauto. intros [v' [Hl Hv]].
      solve_exec_instr. simpl. unfold exec_load. rewrite Hl. reflexivity.
      rs_lessdefs.
    + unfold exec_store in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.storev_extends; eauto. intros [m'1 [Hs He]].
      exploit ext_acci_storev. apply Heqo. apply Hs. eauto. intro ACI1.
      solve_exec_instr. simpl. unfold exec_store. rewrite Hs. reflexivity.
      rs_lessdefs. instantiate (1:= He). etransitivity; eauto. etransitivity; eauto.
    + admit.
    + 
    + solve_exec_instr.
    + solve_exec_instr.
    + (*exec_load*)
      unfold exec_load in *. destr_in H1. inv H1.
      exploit eval_addrmode_lessdef. eauto. intro.
      exploit Mem.loadv_extends; eauto. intros [v' [Hl Hv]].
      solve_exec_instr. simpl. unfold exec_load. rewrite Hl. reflexivity.
      rs_lessdefs.
    + admit.
    + solve_exec_instr.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + solve_exec_instr. admit.
    + admit.
    + solve_exec_instr. admit.
    + admit.
    + solve_exec_instr. admit.
    + admit.
    + solve_exec_instr. admit.
    + admit.
    + solve_exec_instr.
      generalize (RLD rs0). intro. inv H0; constructor.
    + solve_exec_instr. admit.
    + solve_exec_instr. 
     *)
  - (* builtin steps *)
    exploit (eval_builtin_args_rel ext (extw m m'0 Hm)); simpl.
    instantiate (1:= se). eapply Genv.match_stbls_id.
    red. intros. 
    eapply val_inject_id. apply RLD. eapply val_inject_id.
    generalize (RLD RSP). eauto. constructor. eauto.
    intros [vargs' [EVAL' ARGSL]].
    exploit external_call_mem_extends; eauto.
    apply val_inject_list_lessdef; eauto.
    intros (res' & m'1 & CALL' & A & B & C & D).
    assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'1 B)).
    econstructor; eauto using external_call_tid, external_call_support.
    red. intros. eauto using external_call_max_perm.
    red. intros. eauto using external_call_max_perm.
    eexists. split. eapply exec_step_builtin; eauto using regset_lessdef_ptr.
    econstructor; eauto. rs_lessdefs.
    etransitivity; eauto. etransitivity; eauto.
  - exploit (extcall_arguments_inject ext (extw m m'0 Hm)); simpl.
    red. red. intros.  simpl.
    eapply val_inject_id. apply RLD. constructor. eauto.
    intros [args' [ARGS' Hll]].
    apply val_inject_list_lessdef in Hll.
    exploit external_call_mem_extends; eauto.
    intros (res' & m'1 & CALL' & A & B & C & D).
    assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'1 B)).
    econstructor; eauto using external_call_tid, external_call_support.
    red. intros. eauto using external_call_max_perm.
    red. intros. eauto using external_call_max_perm.
    eexists. split. eapply exec_step_external; eauto using regset_lessdef_ptr.
    unfold inner_sp in *. destr_in ISP. exploit regset_lessdef_ptr.
    eauto. apply Heqv. intro. rewrite H0. rewrite ISP. reflexivity.
    econstructor; eauto. rs_lessdefs.
    etransitivity; eauto. etransitivity; eauto.
Admitted. 

Lemma initial_correct:
  forall q1 q2 st1, GS.match_query asm_ext w q1 q2 -> initial_state ge q1 st1 ->
               exists st2, initial_state ge q2 st2 /\ match_states (get w) st1 st2.
Proof.
  intros. destruct H0. destruct q2. inv H. inv H4. inv H5. clear Hm1.
  rewrite <- H4 in *. simpl in H3.
  eexists. split. econstructor; eauto. eapply find_funct_lessdef; eauto.
  eapply val_inject_id; eauto.
  generalize (H3 RSP). intro. inv H5; congruence.
  generalize (H3 RA). intro. inv H5; congruence.
  econstructor; eauto. red. intros. eapply val_inject_id; eauto.
  instantiate (1:= Hm).
  constructor; eauto; red; intros; eauto. rewrite <- H4. reflexivity.
Qed.

Lemma initial_correct':
  forall q1 q2 st1, GS.match_query asm_ext w q1 q2 -> Smallstep.initial_state (sem se)  q1 st1 ->
               exists st2, Smallstep.initial_state (sem se) q2 st2 /\ match_states' (get w) st1 st2.
Proof.
  intros. simpl in H0. destruct st1. destruct H0. unfold m10 in init_sup.
  (* simpl in H. destruct q1, q2. inv H. simpl in *. *)
  exploit initial_correct; eauto.
  intros (st2 & A & B). exists (s, st2). split.
  constructor. eauto.
  destruct q1,q2. inv H. simpl. destruct H3. inv H1. inv Hm1. eauto.
  constructor; eauto.
  destruct q1,q2. inv H. simpl. destruct H3. inv H1. unfold init_sup, m10. rewrite <- H3. reflexivity.
  destruct q1,q2. inv H. simpl. destruct H3. inv H1. unfold init_sup, m10. rewrite <- H3. reflexivity.
Qed.

Lemma final_correct:
  forall wp st1 st2 r1, match_states wp st1 st2 -> final_state st1 r1 ->
                   exists r2 wp', final_state st2 r2 /\ (get w) o-> wp' /\ ext_acci wp wp' /\
                                                               GS.match_reply (asm_ext) (CallconvBig.set w wp') r1 r2.
Proof.
  intros. inv H0. inv H.
  eexists. exists (extw m m' Hm). split.
  - constructor.
  - split. auto. split. auto. constructor; cbn; auto.
    intros. eapply val_inject_id; eauto.
    constructor.
Qed.

Lemma external_correct:
  forall wp st1 st2 q1, match_states wp st1 st2 -> at_external ge st1 q1 ->
  exists wx q2, at_external ge st2 q2 /\ ext_acci wp (get wx) /\  GS.match_query (asm_ext) wx q1 q2 /\ se = se /\
  forall r1 r2 st1' wp'', (get wx) o-> wp'' -> GS.match_reply (asm_ext) (CallconvBig.set w wp'') r1 r2 -> after_external init_sup st1 r1 st1' ->
  exists st2', after_external init_sup st2 r2 st2' /\ match_states wp'' st1' st2'.
Proof.
  intros wp st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst.
  exists (extw m m' Hm). eexists. intuition idtac.
  - econstructor; eauto. eapply find_funct_lessdef; eauto.
  - constructor; CKLR.uncklr; auto. simpl. intros.
    eapply val_inject_id; eauto. split. intro. rewrite H0 in H. inv H.
    constructor.
  - inv H2. destruct r2. inv H1. simpl in H2. simpl in H0, H3. inv H3.
    eexists. split. econstructor; eauto. inv H0. eauto.
    unfold inner_sp in *. generalize (H2 RSP). intro. apply val_inject_id in H1.
    destr_in H8. inv H1. rewrite H8. reflexivity.
    econstructor; eauto. red. intros. apply val_inject_id; eauto.
    reflexivity. etransitivity. eauto. simpl in H0. inv H0. constructor; eauto.
Qed.

End EXT.

Theorem Asm_ext_selfsim prog :
  GS.forward_simulation (asm_ext) (Asm.semantics prog) (Asm.semantics prog).
Proof.
  constructor.
  eapply GS.Forward_simulation.
  + reflexivity.
  + intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
    (* set (ms := fun wp (s1 s2: sup * state) =>
          fst s1 = fst s2 /\ match_states w wp (snd s1) (snd s2)). *)
  eapply GS.forward_simulation_step; subst.
  - intros. CKLR.uncklr. destruct q1, q2. inv H. simpl. destruct H1.
    simpl in H0. generalize (H0 PC). intro.
    apply val_inject_id in H2. inv H2. reflexivity. congruence.
  - apply initial_correct'.
  - intros. destruct s1 as [sup1 s1]. destruct H0. inv H. 
    exploit final_correct; eauto. constructor.
  - intros. destruct w. inv H. simpl in H0. exploit external_correct; eauto.
    intros (wA & q2 & A & B & C & D & E).
    exists wA, q2. split. eauto. split. eauto. split. eauto. split. eauto.
    intros. destruct s1'. destruct H2. exploit E; eauto.
    intros (st2' & F & G). exists (s, st2'). split. econstructor. eauto. eauto.
    econstructor; eauto.
  - simpl. intros. destruct s1 as [sup1 s1]. destruct s1' as [sup1' s1'].
    inv H. destruct s2 as [sup2 s2]. inv H0. destruct w.
    exploit step_correct; simpl; eauto. simpl. eauto. simpl.
    intros (s2' & A & B). exists (Mem.support m1, s2').
    repeat apply conj; eauto. constructor; eauto.
  + auto using well_founded_ltof.
Qed.

