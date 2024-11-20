Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.

Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.


Require Import Integers.
Require Import Values Memory.

Require Import CallconvBig InjectFootprint Injp.
Require Import CAnew.
Require Import Asm Asmrel.
Require Import Asmgenproof0 Asmgenproof1.
Require Import Encrypt EncryptSpec.

Import GS.

Section MS.
  
  Variable w: ccworld cc_c_asm_injp_new.
  Variable se tse : Genv.symtbl.
  Let ge := Genv.globalenv se b1.
  Let tge := Genv.globalenv tse b1.

  Let wp := cajw_injp w.
  Let sg := cajw_sg w.
  Let rs0 := cajw_rs w.
  Let m2 := match wp with injpw _ _ m2 _ => m2 end.
  Let s2 := Mem.support m2.
  Hypothesis GE: CKLR.match_stbls injp wp se tse.
  Let sp0 := rs0 RSP.
  Let ra0 := rs0 RA.
  Let vf0 := rs0 PC.
  
  Inductive match_states_c_asm : injp_world -> state -> (sup * Asm.state) -> Prop :=
  |match_initial i b ofs j m1 m2 Hm b' delta eb:
     wp = injpw j m1 m2 Hm ->
     sp0 <> Vundef -> ra0 <> Vundef ->
     Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
     valid_blockv s2 sp0 ->
     rs0 RDI = Vint i ->
     j b = Some (b', delta) ->
     rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
     vf0 = Vptr eb Ptrofs.zero ->
     Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
     match_states_c_asm wp (Initial i (Vptr b ofs) m1) (s2, State rs0 m2 true)
  |match_final j m1' m2' Hm' (rs: regset):
    rs RSP = rs0 RSP -> rs PC = rs0 RA ->
    (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
    Mem.sup_include s2 (Mem.support m2') ->
    injp_acci wp (injpw j m1' m2' Hm') ->
    injp_acce wp (injpw j m1' m2' Hm') ->
    match_states_c_asm wp (Final m1') (s2, State rs m2' false).
    
End MS.
  
Axiom not_win: Archi.win64 = false.

Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.

Ltac rlia := rewrite maxv; lia.
Ltac Plia := try rewrite !Ptrofs.unsigned_zero; try rewrite!Ptrofs.unsigned_repr; try rlia.
Ltac Ap64 := replace Archi.ptr64 with true by reflexivity.
Ltac Ap64_in H0 := replace Archi.ptr64 with true in H0 by reflexivity.


Lemma size_int_ptr__void_sg_0:
  size_arguments int_ptr__void_sg = 0.
Proof.
  unfold size_arguments, int_ptr__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int_ptr :
  loc_arguments int_ptr__void_sg = One (R DI) :: One (R SI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_ptr__void_sg = One AX.
Proof.
  unfold loc_result. Ap64. reflexivity.
Qed.

Lemma match_program_id :
  match_program (fun _ f0 tf => tf = id f0) eq b1 b1.
Proof.
  red. red. constructor; eauto.
  constructor. constructor. eauto. simpl. econstructor; eauto.
  constructor. eauto.
  constructor; cbn; eauto. constructor; eauto.
  econstructor.
  apply linkorder_refl.
  constructor. constructor; eauto.
Qed.

Lemma CAinjp_simulation_encrypt : forward_simulation (cc_c_asm_injp_new) L_E (Asm.semantics b1).
Proof.
  constructor.
  econstructor; eauto. instantiate (1:= fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun wp s1 s2 => match_states_c_asm w se2 wp s1 s2 /\ cajw_sg w = int_ptr__void_sg).
  eapply forward_simulation_plus with (match_states := ms);
    destruct w as [[f ? ? Hm] sg rs0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  - (* valid *)
    intros. inv H.
    simpl. cbn in *.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros. inv H. inv H0.
    exists (Mem.support m2, State rs0 m2 true).
    split.
    + constructor; eauto.
      econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      eapply Genv.find_funct_transf in TRAN; eauto.
      inv H14. subst tsp0. congruence.
    + constructor; eauto.
      subst targs. rewrite loc_arguments_int_ptr in H9.
      simpl in H9. inv H9. inv H7. inv H9. inv H4.
      econstructor; simpl; eauto.
      inv H14. subst tsp0. congruence.
      inv H3. reflexivity.
  - (* final *)
    intros. inv H0. inv H. inv H0.
    cbn in *.
    exists (rs, m2'). exists (injpw j m m2' Hm').
    repeat apply conj; eauto. constructor.
    econstructor; eauto.
  - intros. inv H0.
  - (* step *)
    Local Opaque undef_regs.
    Ltac compute_pc := rewrite Ptrofs.add_unsigned;
                       rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
    Ltac find_instr := cbn; try rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
    intros. inv H. inv H0. inv H.
    cbn in *. inv H7. rename m3 into m2. rename m into m1.
    assert (exists s2': Asm.state,
               plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs0 m2 true) E0 s2'
               /\ ms (injpw j m1 m2 Hm )(Final m') (Mem.support m2, s2')).
    {
      eexists. split.
      - (* steps *)
        econstructor.
        econstructor; eauto.
        find_instr.
          
    }
    destruct H as [s2' [STEP MS]].  cbn.
    exists (Mem.support m2, s2'). intuition eauto.
    revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
    pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
  - auto using well_founded_ltof.
Qed.
