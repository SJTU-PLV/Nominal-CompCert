Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec DemoBproofnew.

Require Import CallConv Compiler.

Require Import CKLRAlgebra Extends Inject InjectFootprint.

(** * Step1 : self_simulation of Bspec *)

Section SELF_INJP.

Section ms.
Variable w : world injp.

Inductive match_states' : state -> state -> Prop :=
  |match_Callstateg_intro f m1 m2 Hm i:
     w = injpw f m1 m2 Hm ->
     match_states' (Callstateg i m1) (Callstateg i m2)
  |match_Callstatef_intro f m1 m2 Hm i vf vf2:
     w = injpw f m1 m2 Hm ->
     vf <> Vundef ->
     Val.inject f vf vf2 ->
     match_states' (Callstatef vf i m1) (Callstatef vf2 i m2)
  |match_Returnstatef_intro f m1 m2 Hm i ti:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstatef i ti m1) (Returnstatef i ti m2)
  |match_Returnstateg_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstateg i m1) (Returnstateg i m2).
End ms.

Theorem self_simulation_C :
  forward_simulation (cc_c injp) (cc_c injp) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => match_states' w s1 s2).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  -  intros. inv Hse. inv H. cbn in H3.
    eapply Genv.is_internal_transf; eauto.
    + red. red. repeat apply conj; eauto.
      instantiate (1:= id).
      constructor.
      -- constructor; eauto. econstructor; eauto. apply linkorder_refl.
      -- constructor; eauto.
         econstructor; eauto. simpl.
         econstructor; eauto. econstructor; eauto.
         econstructor; eauto. simpl.
         econstructor; eauto. econstructor; eauto. apply linkorder_refl.
         econstructor; eauto.
    + reflexivity.
  - intros. inv H0. inv H. inv H6. inv H1. inv H3. inv Hse. inv H7.
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto. cbn in *. unfold id in TRAN.
(*    Search Genv.find_funct_ptr.
    eapply Genv.find_funct_ptr_match in H4; eauto. destruct H as [tb [A B]]. *)
    exists (Callstateg i m2). split.
    econstructor; eauto.
    econstructor; eauto.
  - intros. inv H; inv H0.
    exists (cr (Vint i) m2). split; econstructor; eauto.
    split. eauto. constructor. simpl. eauto.
    constructor.
  - intros. inv H; inv H0. inv Hse.
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    exists (injpw f m1 m2 Hm) , (cq vf2 int_int_sg ((Vint (Int.sub i Int.one)) :: nil) m2).
    repeat apply conj; eauto.
    + econstructor. eauto.
    + constructor. simpl. eauto.
    econstructor; eauto.
    simpl. constructor. congruence.
    + intros r1 r2 s1' [w'[ Hw Hr]] F.
      destruct w' as [f' m1' m2' INJ0].
      destruct r1 as [t1 m1'1].
      destruct r2 as [t2 m2'1].
      inv Hr. cbn in *.
      inv F. inv H5. inv H9.
      exists (Returnstatef i ti m2'1). split.
      econstructor; eauto.
      econstructor; eauto.
  - intros. inv H0; inv H.
    + (* zero *)
      exists (Returnstateg (Int.zero) m2). split. constructor; eauto.
      econstructor; eauto. reflexivity.
    + (* read *)
      exists (Returnstateg ti m2).
      inv Hse. unfold Genv.symbol_address in FINDM. destruct Genv.find_symbol eqn:FIND; try congruence.
      inv FINDM.
      eapply Genv.find_symbol_match in H2; eauto.
      destruct H2 as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD1. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      exploit Mem.loadv_inject; eauto.
      intros [v1 [LOAD1' VINJ1]]. inv VINJ1.
      split.
      econstructor; eauto. unfold Genv.symbol_address.
      rewrite FINDM'. reflexivity.
      econstructor; eauto. reflexivity.
    + (* call *)
      inv Hse.
      assert (VVF: Val.inject f (Genv.symbol_address se1 f_id Ptrofs.zero)
             (Genv.symbol_address se2 f_id Ptrofs.zero)).
      eapply Op.symbol_address_inject; eauto.
      unfold Genv.symbol_address in FINDM.
      destruct Genv.find_symbol eqn:FIND; try congruence.
      inv FINDM.
      eapply Genv.find_symbol_match in H2 as F; eauto.
      destruct F as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD0. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      exists (Callstatef (Genv.symbol_address se2 f_id Ptrofs.zero) i m2).
      split.
      econstructor; eauto.
      unfold Genv.symbol_address. rewrite FINDM'. eauto.
      unfold Genv.symbol_address in *.
      destruct (Genv.find_symbol se1 f_id); try congruence.
      destruct (Genv.find_symbol se2 f_id); try congruence. inv VVF.
      econstructor; eauto.
    + (* return *)
      destruct w as [f0 m1'0 m2'0 Hm0].
      inv Hse. inv H1. rename m' into m1'1. rename m'' into m1'2.
      eapply Genv.match_stbls_incr in H3; eauto.
      2:{ intros. exploit H14; eauto. intros [E F].
      unfold Mem.valid_block in *. split; eauto. }
      unfold Genv.symbol_address in FINDM. destruct Genv.find_symbol eqn:FIND; try congruence.
      inv FINDM.
      eapply Genv.find_symbol_match in H3. 2: eapply FIND.
      destruct H3 as [b' [C D]].
      edestruct Mem.store_mapped_inject as [m2'1 [STORE0' INJ1]]; eauto.
      edestruct Mem.store_mapped_inject as [m2'2 [STORE1' INJ2]]; eauto.
      exists (Returnstateg (Int.add ti i) m2'2).
      econstructor; eauto.
      econstructor; eauto.
      unfold Genv.symbol_address. rewrite D. reflexivity.
      econstructor; eauto.
      instantiate (1:= INJ2).
      transitivity (injpw f m1 m2 Hm'2).
      constructor; eauto.
      constructor; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- eapply Mem.unchanged_on_trans.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
      -- eapply Mem.unchanged_on_trans. 
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE0.
         destruct STORE0 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE1.
         destruct STORE1 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
      -- red. intros. congruence.
  - constructor. intros. inv H.
Qed.

End SELF_INJP.

Section WT_C.

Theorem self_simulation_wt :
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec Bspec.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [[se1' [se2' sg]] ?]. destruct Hse as [Hse Hse2].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd (snd (fst w)) = int_int_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. inv H0. inv H. inv H1. reflexivity.
  - intros. inv H. inv H1. cbn in *. inv H. inv H1. exists s1. exists s1.
    split. inv H2. inv H0. simpl. simpl in *.
    inv H. inv H2. inv H5.
    econstructor; eauto. split. reflexivity.
    inv H0. reflexivity.
  - intros. inv H. exists r1.
    split. auto. exists r1. inv H0.
    split; simpl; auto.
    econstructor; simpl. eauto.
    econstructor. constructor.
  - intros. subst.
    exists (se2 , (se2, int_int_sg), tt).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + exists q1. split; inv H0; simpl;  constructor; simpl; eauto.
    + constructor; eauto. simpl. constructor. eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      destruct H as [r3 [A B]].
      inv A. inv B. inv H1. inv H2. econstructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

End WT_C.
(*
Module CL.

Definition int_loc_arguments := loc_arguments int_int_sg.

Definition int_loc_argument := if Archi.ptr64 then (if Archi.win64 then (R CX) else (R DI))
                                          else S Outgoing 0 Tint.
Lemma loc_result_int:
 loc_result int_int_sg = One AX.
Proof.
  intros. unfold int_int_sg, loc_result.
  replace Archi.ptr64 with true by reflexivity.
  reflexivity.
Qed.

Lemma ls_result_int:
  forall ls, Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls = ls (R AX).
Proof.
  intros. rewrite loc_result_int. reflexivity.
Qed.

Definition int_loc_result' : rpair mreg := loc_result int_int_sg.
(* Compute int_loc_result. One AX *)

Definition int_loc_result : loc := R AX.

Definition loc_int_loc (i: int) (l : loc): Locmap.t :=
  fun loc => if Loc.eq loc l  then (Vint i) else Vundef.
*)
(*
Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply self_simulation_C.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  repeat eapply compose_forward_simulations.
  eapply CL.c_locset. eapply LM.locset_mach. eapply mach_asm.
  eapply semantics_asm_rel; eauto.
Qed.
*)



