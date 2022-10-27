Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler CA.

Require Import CKLRAlgebra Extends Inject InjectFootprint.

(* forget it for now
Search wt_c.
*)

Section injp_CA.

Section MS.
Variable w: ccworld (cc_c injp @ cc_c_asm).

Definition se := fst (fst w).
Definition injw := snd (fst w).
Definition caw0 := snd (w).
Definition sg := caw_sg caw0.
Definition rs0 := caw_rs caw0.
Definition m2 := caw_m caw0.

Definition sp0 := rs0 RSP.
Definition ra0 := rs0 RA.
Definition vf0 := rs0 PC.
Definition bx0 := rs0 RBX. (*only used callee_save register in this sample*)
(*cc_c_asm_mq*)

Inductive new_blockv (s:sup) : val -> Prop :=
  new_blockv_intro : forall b ofs, ~ sup_In b s -> new_blockv s (Vptr b ofs).

Inductive match_state_c_asm : state -> (sup * Asm.state) -> Prop :=
  |match_ca_callg i m m2':
     injp_match_mem injw m m2' ->
     args_removed sg sp0 m2 m2 ->
     rs0 RDI = Vint i ->
     match_state_c_asm (Callstateg i m) ((Mem.support m2),State rs0 m2 true)
  |match_ca_callf w' i m m2' tm (rs: regset) vfc sb:
     let sp := rs RSP in let ra := rs RA in let vf := rs PC in
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RBX = Vint i ->
     rs RDI = Vint (Int.sub i Int.one) ->
     args_removed int_int_sg sp tm m2' ->
     Val.has_type sp Tptr -> Val.has_type ra Tptr ->
     sp = Vptr sb Ptrofs.zero ->
     sup_In sb (Mem.support tm) -> ~ sup_In sb (Mem.support m2) ->
     (forall i, loc_out_of_reach (injp_mi w') m sb i) ->
     vf <> Vundef -> ra <> Vundef -> vfc <> Vundef ->
     Val.inject (injp_mi w') vfc vf ->
     Mem.loadv Mptr tm (Val.offset_ptr sp (Ptrofs.repr 16)) = Some ra0 ->
     Mem.loadv Mptr tm (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     Mem.loadv Many64 tm (Val.offset_ptr sp (Ptrofs.repr 8)) = Some bx0 ->
     (forall r, is_callee_save r = true /\ r <> BX -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     match_state_c_asm (Callstatef vfc i m) ((Mem.support m2),State rs tm true)
  |match_ca_returnf w' m2' i rig m tm (rs: regset):
     let sp := rs RSP in
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RBX = Vint i -> rs RAX = Vint rig ->
     Mem.unchanged_on (fun b ofs => True) m2' tm ->
     Mem.support m2' = Mem.support tm ->
     Mem.loadv Mptr tm (Val.offset_ptr sp (Ptrofs.repr 16)) = Some ra0 ->
     Mem.loadv Mptr tm (Val.offset_ptr sp Ptrofs.zero) = Some sp0 ->
     Mem.loadv Many64 tm (Val.offset_ptr sp (Ptrofs.repr 8)) = Some bx0 ->
     (forall r, is_callee_save r = true /\ r <> BX -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     match_state_c_asm (Returnstatef i rig m) ((Mem.support m2), State rs tm true)
  |match_ca_returng w' m2' m tm (rs: regset) ri:
     injp_acc injw w' ->
     injp_match_mem w' m m2' ->
     rs RAX = Vint ri ->
     Mem.unchanged_on (fun b ofs => True) m2' tm ->
     Mem.support m2' = Mem.support tm ->
     rs RSP = rs0 RSP -> rs PC = rs0 RA ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support tm) -> (*unchanged_on of Outgoing*)
     (*cc_c_asm_mr*)
     match_state_c_asm (Returnstateg ri m) ((Mem.support m2), State rs tm false).
End MS.

Axiom not_win: Archi.win64 = false.
Lemma size_int_int_sg_0:
  size_arguments int_int_sg = 0.
Proof.
  unfold size_arguments, int_int_sg, loc_arguments. replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int :
  loc_arguments int_int_sg = One (R DI)::nil.
Proof.
  unfold loc_arguments.
  replace Archi.ptr64 with true by reflexivity.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_int_sg = One AX.
Proof.
  unfold loc_result.
  replace Archi.ptr64 with true by reflexivity.
  reflexivity.
Qed.

Lemma match_program_id :
  match_program (fun _ f0 tf => tf = id f0) eq prog prog.
Proof.
  red. red. constructor; eauto.
    constructor. constructor. eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor. constructor; eauto. constructor; eauto.
    constructor; eauto.
    constructor; eauto. constructor; eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor.
Qed.

Lemma loadv_unchanged_on : forall P m m' chunk b ptrofs v,
    Mem.unchanged_on P m m' ->
    (forall i, let ofs := Ptrofs.unsigned ptrofs in
    ofs <= i < ofs + size_chunk chunk -> P b i) ->
    Mem.loadv chunk m (Vptr b ptrofs) = Some v ->
    Mem.loadv chunk m' (Vptr b ptrofs) = Some v.
Proof.
  intros. unfold Mem.loadv in *. cbn in *.
  eapply Mem.load_unchanged_on; eauto.
Qed.

Lemma injp_CA_simulation: forward_simulation
                 (cc_c injp @ cc_c_asm)
                 (cc_c injp @ cc_c_asm)
                 Bspec (Asm.semantics prog).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_c_asm w s1 s2 /\
                         caw_sg (snd w) = int_int_sg).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as [[se [f ? ? Hm]] [sg rs0 m2'0]]; destruct Hse; subst; cbn in *; eauto.
  - (*valid_query*)
    intros. destruct H0 as [qm [Hq1 Hq2]]. inv Hq1. inv Hq2.
    simpl. cbn in *. subst vf.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto. inv H; eauto.
  - (* initial *)
    intros q1 q3 s1 [q2 [Hq1 Hq2]] Hi1. inv Hi1.
    inv Hq1. inv Hq2. cbn in *. inv H7.
    exists (Mem.support m2'0, State rs0 m2'0 true). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      eapply Genv.find_funct_transf in TRAN; eauto. inv H; eauto.
      inv H17. subst sp. congruence.
    + eauto.
    + econstructor; cbn; eauto.
      constructor. red. rewrite size_int_int_sg_0. reflexivity.
      rewrite loc_arguments_int in H6. simpl in H6. inv H6. inv H3. reflexivity.
    + eauto.
  - (* final_state *)
    intros s1 s3 r1 Hms Hf1. inv Hf1. inv Hms. inv H0. cbn in *.
    exists (rs,tm). split. constructor.
    exists (cr (Vint s) m2'). split.
    exists w'. split. eauto. constructor; eauto.
    constructor; eauto. eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. auto.
    constructor. eauto with mem.
    intros. inv H0. rewrite size_int_int_sg_0 in H11. extlia.
    intros. inv H0. rewrite size_int_int_sg_0 in H11. extlia.
    intros. inv H0. rewrite size_int_int_sg_0 in H2. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. inv EXT1. inv MS.
    inv H0. cbn in *. inv H4. inv H5. cbn in *.
    inv H. eapply Genv.match_stbls_incr in H4; eauto.
    2:{
      intros. exploit H29; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    exists ((se2,(injpw f' m m2' Hm4)),(caw int_int_sg rs tm)).
    exists (rs,tm). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + exists (cq vf1 int_int_sg (Vint (Int.sub aif Int.one)::nil) m2').
      split.
      -- constructor; eauto. simpl. constructor.
      -- econstructor; eauto.
         rewrite loc_arguments_int. simpl. congruence.
         subst sp. rewrite H11. constructor; eauto.
    + constructor. apply H4.
      inversion H25. eauto with mem.
      inversion H26. eauto with mem.
    + reflexivity.
    + (*after_external*)
      intros r1 r3 s1' [r2 [Hr1 Hr2]] Haf1.
      destruct Hr1 as [w [Hw Hr1]]. inv Haf1. inv Hr1. inv Hr2.
      cbn in *.
      exists ((Mem.support m2'0), (State rs' tm' true)). repeat apply conj.
      -- constructor. inversion H36; eauto.
         unfold inner_sp. rewrite H40. subst sp. rewrite H11.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- econstructor; cbn.
         ++ etransitivity; eauto. constructor; eauto.
         ++ eauto.
         ++ generalize (H34 BX). intro. exploit H; eauto.
            simpl. intro A. rewrite A. eauto.
         ++ rewrite loc_result_int in H1. simpl in H1.
            inv H1. reflexivity.
         ++ eapply Mem.unchanged_on_implies; eauto.
            intros. red. intro. inv H2. rewrite size_int_int_sg_0 in H32. extlia.
         ++ eauto.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ destruct w. inv H5. inv Hw.
            rewrite H40. subst sp. rewrite H11 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H35.
            intros. simpl. red. intro A. inv A. rewrite size_int_int_sg_0 in H2. extlia.
            eapply Mem.load_unchanged_on. apply H43.
            intros. eauto.
            inv H8. eauto.
            rewrite size_int_int_sg_0 in H27. extlia.
         ++ intros. rewrite H34. rewrite H23. eauto. eauto. apply H.
         ++ inversion H36. eauto with mem.
      -- reflexivity.
  - (*internal_steps*)
    intros. inv H0; inv H1.
    ++ (*step_zero*)
      
      

End injp_CA.
Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply injp_protection.
  eapply compose_forward_simulations.
  eapply self_wt.
  rewrite <- !(cc_compose_assoc) at 1.
  eapply compose_forward_simulations.
  rewrite cc_compose_assoc at 1.
  rewrite cc_compose_assoc at 1.
  rewrite <- cc_ca_cllmma at 1.
  rewrite cc_cllmma_ca.
  eapply CA.
  eapply semantics_asm_rel; eauto.
Qed.
*)
