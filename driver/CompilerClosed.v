Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import Compiler.

Section CLOSE_COMPCERT.
Import Closed.

Variable p : Csyntax.program.
Variable tp : Asm.program.
Hypothesis transf : transf_c_program p = OK tp.
Let se := Genv.symboltbl (erase_program p).

Variable main_block_c : block.
Variable m0_c : mem.

Let liA1 := li_c.
Let liB1 := li_c.
Let sg := AST.mksignature nil (AST.Tret AST.Tint) AST.cc_default.
Let main_function_value_c := Vptr main_block_c Ptrofs.zero.
Let query1 := cq main_function_value_c sg nil m0_c.

Inductive reply1 : int -> c_reply -> Prop :=
  | reply1_intro: forall r m,
      reply1 r (cr (Vint r) m).

Let s1 := Csem.semantics p.
Let se1 := se.
Let lts1' := (Smallstep.activate s1 se1).

Let ge_c' := Smallstep.globalenv (s1 se).
Let ge_c := Csem.genv_genv ge_c'.
Variable main_c : Csyntax.fundef.
Hypothesis Hinitial_state_c :
  Genv.init_mem (erase_program p) = Some m0_c /\
  Genv.find_symbol se p.(prog_main) = Some main_block_c /\
  Genv.find_funct_ptr ge_c main_block_c = Some main_c.

Import Asm.

Let s2 := Asm.semantics tp.
Let ge_asm := Smallstep.globalenv (s2 se).
Variable m0_asm' m0_asm : mem.
Variable dsp : block. (** The dummy block as stack pointer *)
Hypothesis Hinitial_state_asm1: Genv.init_mem (erase_program tp) = Some m0_asm'.
Hypothesis Hinitial_state_asm2: Mem.alloc m0_asm' 0 0 = (m0_asm, dsp).

Let liA2 := li_asm.
Let liB2 := li_asm.
Let rs0 :=
    (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge_asm tp.(prog_main) Ptrofs.zero)
    # RA <- Vnullptr
    # RSP <- (Vptr dsp Ptrofs.zero).

Let query2 := (rs0, m0_asm).

Inductive reply2: int -> (regset * mem) -> Prop :=
  | reply2_intro: forall r (rs:regset) m,
      (* rs#PC = Vnullptr -> *)
      rs#RAX = Vint r ->
      reply2 r (rs, m).
Let se2 := se.
Let lts2' := (Smallstep.activate s2 se2).

Lemma erase_same: erase_program p = erase_program tp.
Proof.
  exploit transf_c_program_match; eauto. intro MATCH.
  unfold match_c_prog in MATCH. simpl in MATCH. repeat destruct MATCH as (? & MATCH).
  fold Csyntax.fundef. remember p as xx.
  rename xx into p', p into xx. rename p' into p.
  match goal with
  | H: ?P p ?p2 |- _ => rewrite Heqxx in H
  end.
  rewrite Heqxx. clear Heqxx.
  Ltac mp H p1 p2 :=
    unfold Linking.match_program in H;
    match type of H with
    | Linking.match_program_gen _ _ _ _ _ =>
        apply Linking.match_program_skel in H;
        try fold CminorSel.fundef in H;
        try fold RTL.fundef in H;
        rewrite H; clear H p1;
        rename p2 into p1
    | Linking.match_program_gen _ _ _ _ _ /\ _ =>
        let H' := fresh "H" in
        let garbage := fresh "H" in
        destruct H as (H' & garbage);
        clear garbage;
        mp H' p1 p2
    end.
  Ltac try_rewrite xx := match goal with
  | H: ?P xx ?p2 |- _ =>
    unfold P in H; mp H xx p2
  | H: match_if ?cond ?P xx ?p2 |- _ =>
    unfold match_if, P in H;
    let H' := fresh "H" in
    assert (H' : erase_program xx = erase_program p2) by (destr_in H; mp H xx p2; auto);
    rewrite H';
    clear H' H xx;
    rename p2 into xx
  end.
  repeat try_rewrite xx.
  unfold Unusedglobproof.match_prog in H12.
  destruct H12 as (u & VALID & MATCH').
  inv MATCH'. rewrite <- match_prog_skel.
  clear match_prog_main match_prog_public match_prog_def match_prog_skel VALID xx u.
  rename x12 into xx.
  repeat try_rewrite xx.
  auto.
Qed.

Lemma m0_same: m0_c = m0_asm'.
Proof.
  rewrite erase_same, Hinitial_state_asm1 in Hinitial_state_c.
  destruct Hinitial_state_c. inv H. auto.
Qed.

Let ccA : callconv liA1 liA2 := cc_compcert.
Let ccB : callconv liB1 liB2 := cc_compcert.

Lemma Hvalid: Genv.valid_for (erase_program p) se1.
Proof.
  red. intros. rewrite Genv.find_info_symbol in H. destruct H as (b & []).
  exists b, g. unfold se1, se. split; auto. split; auto.
  destruct g; constructor. constructor.
  destruct v. constructor; constructor.
Qed.

Lemma m0_inject_c: Mem.inject (Mem.flat_inj (Mem.support m0_c)) m0_c m0_c.
Proof.
  apply (Genv.initmem_inject (erase_program p)).
  apply Hinitial_state_c.
Qed.

Lemma m0_inject_c_asm: Mem.inject (Mem.flat_inj (Mem.support m0_c)) m0_c m0_asm.
Proof.
  eapply Mem.alloc_right_inject.
  2: apply Hinitial_state_asm2; eauto.
  rewrite <- m0_same.   apply m0_inject_c.
Qed.

Let j' := fun b => if eq_block b dsp then Some (dsp ,0) else (Mem.flat_inj (Mem.support m0_c)) b.

Lemma m0_inject_asm : Mem.inject j' m0_asm m0_asm.
Proof.
  generalize m0_inject_c. intro H. rewrite m0_same in H.  
  exploit Mem.alloc_parallel_inject. eauto.
  apply Hinitial_state_asm2. reflexivity. reflexivity.
  intros (j'1 & m2' & dsp' & A &B & C & D& E).
  generalize Hinitial_state_asm2. intro H2. rewrite A in H2. inv H2.
  replace j' with j'1. eauto.
  apply Axioms.functional_extensionality.
  intros. unfold j'. destr. subst. eauto. rewrite m0_same. eapply E; eauto.
Qed.

Let wB : ccworld ccB.
  unfold ccB, cc_compcert, CA.cc_c_asm_injp. simpl.
  (* ro *)
  split. split. exact se. split. exact se. exact m0_c.
  (* wt_c *)
  split. split. exact se. split. exact se. exact sg.
  (* cc_c_asm_injp *)
  split. split. exact se. split.
  simpl. econstructor. exact m0_inject_c_asm. exact sg. exact rs0.
  (* cc_asm injp *)
  econstructor. exact m0_inject_asm.
Defined.

Hypothesis closed:
  forall v id sg, Genv.find_funct (Genv.globalenv se tp) v <> Some (External (EF_external id sg)).

Lemma closed2 : forall s q, Smallstep.safe lts2' s -> ~ Smallstep.at_external lts2' s q.
Proof.
  unfold lts2', s2, se2, semantics. simpl. intros. intro.
  destruct s. inv H0.
  eapply closed; eauto.
Qed.

Lemma reply_sound2: forall s r, Smallstep.final_state lts2' s r -> exists i, reply2 i r.
Proof.
  unfold lts2', s2, se2. simpl. intros. destruct s.
  inversion H. eexists. econstructor.
  admit.
Abort.
(*
1. rs#RAX should be a integer
2. rs#PC should be Vnullptr

 *)

Lemma sound_memory_ro: ValueAnalysis.sound_memory_ro se m0_c.
Proof.
  unfold se. destruct Hinitial_state_c. clear H0.
  eapply ValueAnalysis.initial_ro_sound; eauto.
Qed.

Lemma main_block_genv: Genv.find_symbol se (prog_main tp) = Some main_block_c.
Proof.
  destruct Hinitial_state_c as [? []].
  pose proof erase_same. inv H2. simpl in H0. rewrite H0. auto.
Qed.

Lemma has_main_block: sup_In main_block_c (Mem.support m0_c).
Proof.
  destruct Hinitial_state_c as [? []].
  eapply Genv.find_symbol_not_fresh; eauto.
Qed.

Lemma size_0: Conventions.size_arguments sg = 0.
Proof.
  unfold Conventions.size_arguments, Conventions1.loc_arguments. simpl.
  destruct Archi.ptr64, Archi.win64; simpl; auto.
Qed.

Lemma Hmatch_query : match_query ccB wB query1 query2.
Proof.
  simpl.
  exists query1. split.
  constructor. constructor. exact sound_memory_ro.
  exists query1. split.
  constructor. split. reflexivity. simpl. auto.
  exists query2. split.
  unfold query1, query2. econstructor; simpl.
  unfold Conventions1.loc_arguments. cbn.
  destruct Archi.ptr64, Archi.win64; simpl; constructor.
  unfold rs0. simpl.
  unfold main_function_value_c, Genv.symbol_address.
  rewrite main_block_genv.
  econstructor. unfold Mem.flat_inj. pose proof has_main_block. destr.
  rewrite Ptrofs.add_zero. auto.
  intros. rewrite size_0 in H. inv H. extlia.
  cbn. unfold Vnullptr, Tptr. destruct Archi.ptr64; simpl; auto.
  cbn. unfold Vnullptr, Tptr. destruct Archi.ptr64; simpl; auto.
  constructor. eapply Mem.valid_new_block. eapply Hinitial_state_asm2.
  econstructor. apply size_0.
  unfold main_function_value_c. discriminate.
  discriminate.
  unfold cc_asm_match'. simpl. split; [|split].
  intros. unfold rs0.
  destruct (PregEq.eq r RSP); [subst; rewrite Pregmap.gss|
  rewrite Pregmap.gso; auto; destruct (PregEq.eq r RA); [subst; rewrite Pregmap.gss|
  rewrite Pregmap.gso; auto; destruct (PregEq.eq r PC); [subst; rewrite Pregmap.gss|
                                                          rewrite Pregmap.gso; auto]]].
  econstructor; eauto. unfold j'. destr. rewrite Ptrofs.add_zero. reflexivity.
  unfold Vnullptr. destr; constructor.
  unfold Genv.symbol_address. destr; econstructor.
  unfold ge_asm in Heqo. simpl in Heqo. rewrite main_block_genv in Heqo. inv Heqo.
  unfold j'. unfold Mem.flat_inj. pose proof has_main_block. destr.
  pose proof Hinitial_state_asm2. inv e.
  apply Mem.fresh_block_alloc in H0. rewrite <- m0_same in H0. elim H0. rewrite <- H1. eauto.
  destr.
  rewrite Ptrofs.add_zero. auto.
  unfold rs0.
  rewrite Pregmap.gso; [|discriminate].
  rewrite Pregmap.gso; [|discriminate].
  rewrite Pregmap.gss.
  unfold ge_asm. simpl. unfold Genv.symbol_address. rewrite main_block_genv. discriminate.
  constructor.
Qed.

Lemma Hmatch_reply1 : forall r r1 r2,
    match_reply ccB wB r1 r2 ->
    reply1 r r1 -> reply2 r r2.
Proof.
  intros. destruct H as [r_c [Hro [r_c' [Hwt [r_a [Hca Hasm]]]]]].
  inv H0. inv Hro. inv Hwt. inv Hca.
  destruct Hasm as [wj [Hw Hr]].
  destruct r2. inv Hr.
  constructor.
  (*r0 RAX -> rs' RAX -> Vint r via the signature sg*)
  assert (tres = rs' RAX).
  { unfold tres. unfold sg. unfold CA.rs_getpair.
    unfold Conventions1.loc_result, Conventions1.loc_result_64, Conventions1.loc_result_32. simpl. destruct Archi.ptr64; reflexivity.
  }
  inv H8. generalize (H1 RAX).
  intro. simpl in H4. rewrite <- H3 in H4. rewrite <- H6 in H4.
  inv H4. reflexivity.
Qed.

Lemma Hmatch_reply2 : forall r r1 r2,
    match_reply ccB wB r1 r2 ->
    reply2 r r2 ->
    reply1 r r1.
Proof.
  intros. destruct H as [r_c [Hro [r_c' [Hwt [r_a [Hca Hasm]]]]]].
  inv H0. inv Hro. inv Hwt. inv Hca.
  destruct Hasm as [wj [Hw Hr]].
  unfold Conventions1.loc_result, Conventions1.loc_result_64, Conventions1.loc_result_32 in tres. unfold sg in tres.
  assert (Archi.ptr64 = true). admit.
  unfold CA.rs_getpair in tres. simpl in tres.
  unfold map_rpair in tres. simpl in tres.
  assert (tres = rs' RAX).
  unfold tres. rewrite H2. simpl. reflexivity.
  rewrite H3 in H7.
  admit. (*problem: res can be Vundef*)
Abort.

Lemma Hmatch_reply : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply1 r r1 <-> reply2 r r2.
Proof.
Abort.

Lemma m0_se_support : Genv.genv_sup se = Mem.support m0_c.
Proof.
  unfold se. rewrite erase_same. rewrite m0_same.
  eapply Genv.init_mem_genv_sup; eauto.
Qed.

Lemma match_se_initial : Genv.match_stbls (Mem.flat_inj (Mem.support m0_c)) se se.
Proof.
  pose proof m0_se_support as SUP.
  constructor; intros; eauto.
  - rewrite <- SUP. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
  - rewrite <- SUP. exists b2. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
  - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
  - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
  - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
Qed.
    
Lemma Hmatch_senv : match_senv ccB wB se1 se2.
Proof.
  pose proof m0_se_support as SUP.
  pose proof Hinitial_state_asm2 as ALLOC.
  apply Mem.fresh_block_alloc in ALLOC as FRESH; eauto.
  rewrite <- m0_same in FRESH.
  assert (SUPINCL: Mem.sup_include (Mem.support m0_c) (Mem.support m0_asm)).
  apply Mem.support_alloc in ALLOC. rewrite ALLOC. red.
  intros. apply Mem.sup_incr_in2; eauto. rewrite <- m0_same. eauto.
  unfold ccB, cc_compcert, se1, se2. simpl.
  split; [|split; [|split]].
  constructor. auto.
  constructor. auto.
  constructor. apply match_se_initial; eauto.
  rewrite SUP. eauto.
  rewrite SUP. eauto.
  constructor.
  eapply Genv.match_stbls_incr. apply match_se_initial.
  red. intros. unfold j'. destr. subst b. unfold Mem.flat_inj in H. destr_in H.
  intros. unfold j' in H0. destr_in H0. subst b1. inv H0.
  rewrite SUP. split; eauto.
  rewrite SUP. eauto.
  rewrite SUP. eauto.
Qed.

(* Lemma open_fsim : Smallstep.forward_simulation ccA ccB s1 s2.
Proof.
  exploit clight_semantic_preservation.
  apply transf_c_program_match. auto. *)

Lemma open_simulation: Smallstep.backward_simulation ccA ccB s1 s2.
Proof.
  apply c_semantic_preservation, transf_c_program_match. auto.
Qed.

(*
Lemma compcert_close_sound :
  backward_simulation (L1 query1 reply1 s1 se1) (L2 query2 reply2 s2 se2).
Proof.
  eapply close_sound_backward; eauto using
    closed2, reply_sound2, Hvalid, Hmatch_query, Hmatch_senv, open_simulation.
  intros. eapply Hmatch_reply2; eauto.
Qed.
 *)

Lemma compcert_close_sound_forward : 
  forward_simulation (L1 query1 reply1 s1 se2) (L2 query2 reply2 s2 se2).
Proof.
  eapply close_sound_forward; eauto.
  exact Hvalid. eapply Hmatch_query; eauto. exact Hmatch_senv.
  intros.
  eapply Hmatch_reply1; eauto.
  admit. (*The missing Open Sim *)
Abort.
End CLOSE_COMPCERT.
(*
Lemma loading_forward: forall L1 L2,
    Smallstep.forward_simulation cc_compcert cc_compcert L1 L2 ->
    exists CL1 CL2,
    forward_simulation CL1 CL2.
*)
