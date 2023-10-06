Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import Server Serverspec.

Require Import CallConv Compiler CA.
Require Import CKLRAlgebra Extends Inject InjectFootprint.

Require Import Asmgenproof0 Asmgenproof1.

(** Refinement between the hand-written specification and the assembly
semantics of `server.s` (`server_opt.s`) *)


Section MS.

Variable w: ccworld (cc_c_asm_injp).
Variable se tse: Genv.symtbl.
Let ge := Genv.globalenv se b1.
Let tge := Genv.globalenv tse b1.

Let wp := cajw_injp w.
Let sg := cajw_sg w.
Let rs0 := cajw_rs w.
Let m2 := match wp with injpw _ _ m2 _ => m2 end.
Let s2 := Mem.support m2.
Hypothesis GE: match_stbls injp wp se tse.
Let sp0 := rs0 RSP.
Let ra0 := rs0 RA.
Let vf0 := rs0 PC.

Inductive new_blockv (s:sup) : val -> Prop :=
  new_blockv_intro : forall b ofs, ~ sup_In b s -> new_blockv s (Vptr b ofs).

Inductive match_state_c_asm : state -> (sup * Asm.state) -> Prop :=
|match_call1 m1 b b' ofs eb input j Hm delta:
  wp = injpw j m1 m2 Hm ->
  sp0 <> Vundef -> ra0 <> Vundef ->
  Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
  valid_blockv (Mem.support m2) sp0 ->
  vf0 = Vptr eb Ptrofs.zero ->
  Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
  j b = Some (b', delta) ->
  rs0 RDI = Vint input ->
  rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
  match_state_c_asm (Call1 (Vptr b ofs) input m1) (s2, State rs0 m2 true)
|match_call2 m1 b ofs j j' Hm (rs:regset) m1' m2' Hm' b' delta eb sb tsb:
    let sp := Vptr sb Ptrofs.zero in let tsp := rs RSP in let ra := rs RA in let vf := rs PC in
    tsp = Vptr tsb Ptrofs.zero ->
    wp = injpw j m1 m2 Hm ->
    (forall ofs, (0 <= ofs < 8 \/ 16 <= ofs < 24) -> loc_out_of_reach j' m1' tsb ofs) ->
    Mem.range_perm m2' tsb 0 8 Cur Freeable ->
    Mem.range_perm m2' tsb 16 24 Cur Freeable ->
    injp_acc wp (injpw j' m1' m2' Hm') ->
    rs PC = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
    j b = Some (b', delta) ->
    j' sb = Some (tsb, 8) -> (forall b (d:Z) , j' b = Some (tsb, d) -> b = sb) ->
    rs RDI = Vptr tsb (Ptrofs.repr 8) ->
    ra = Vptr eb (Ptrofs.repr 6) ->
    Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
    sup_In tsb (Mem.support m2') -> ~ sup_In tsb s2 -> ~sup_In sb (Mem.support m1) ->
    vf <> Vundef ->
    Mem.loadv Mptr m2' (Val.offset_ptr tsp (Ptrofs.repr 16)) = Some ra0 ->
    Mem.loadv Mptr m2' (Val.offset_ptr tsp Ptrofs.zero) = Some sp0 ->
    valid_blockv s2 sp0 ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include s2 (Mem.support m2')  ->
     match_state_c_asm (Call2 (Vptr b ofs) sb m1') (s2, State rs m2' true)
|match_return1 j j' m1 m1'' m2'' Hm Hm'' (rs:regset) eb sb tsb:
    let tsp := rs RSP in let sp := Vptr sb Ptrofs.zero in
     tsp = Vptr tsb Ptrofs.zero ->
     wp = injpw j m1 m2 Hm ->
     (forall ofs, (0 <= ofs < 8 \/ 16 <= ofs < 24) -> loc_out_of_reach j' m1'' tsb ofs) ->
     Mem.range_perm m2'' tsb 0 8 Cur Freeable ->
     Mem.range_perm m2'' tsb 16 24 Cur Freeable ->
     injp_acc wp (injpw j' m1'' m2'' Hm'') ->
     rs PC = Vptr eb (Ptrofs.repr 6) ->
     Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b1) ->
     j' sb = Some (tsb, 8) -> (forall b (d:Z) , j' b = Some (tsb, d) -> b = sb) ->
     Mem.loadv Mptr m2'' (Val.offset_ptr tsp (Ptrofs.repr 16)) = Some ra0 ->
     Mem.loadv Mptr m2'' (Val.offset_ptr tsp Ptrofs.zero) = Some sp0 ->
     ~ sup_In tsb s2 -> ~sup_In sb (Mem.support m1) ->
     valid_blockv (Mem.support m2) sp0 ->
     (forall r, is_callee_save r = true  -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include (Mem.support m2) (Mem.support m2'') ->
     match_state_c_asm (Return1 sb m1'') (s2, State rs m2'' true)
|match_return2 j' m2'' m1'' (rs:regset) Hm'':
  (injp_acc wp (injpw j' m1'' m2'' Hm'')) ->
   rs RSP = rs0 RSP -> rs PC = rs0 RA ->
   (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
   Mem.sup_include s2 (Mem.support m2'') ->
   match_state_c_asm (Return2 m1'') (s2, State rs m2'' false).

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

Lemma size_intptr__void_sg_0:
  size_arguments intptr__void_sg = 0.
Proof.
  unfold size_arguments, intptr__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma size_int_fptr__void_sg_0:
  size_arguments int_fptr__void_sg = 0.
Proof.
  unfold size_arguments, int_fptr__void_sg, loc_arguments. Ap64.
  rewrite not_win. reflexivity.
Qed.

Lemma loc_arguments_int_fptr :
  loc_arguments int_fptr__void_sg = One (R DI):: One (R SI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_arguments_int :
  loc_arguments intptr__void_sg = One (R DI) :: nil.
Proof.
  unfold loc_arguments. Ap64.
  rewrite not_win. simpl. reflexivity.
Qed.

Lemma loc_result_int :
  loc_result int_fptr__void_sg = One AX.
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
  constructor. eauto. econstructor.
  apply linkorder_refl. eauto.
  constructor; eauto.
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

Lemma load_result_Mptr_eq:
    forall v, v <> Vundef -> Val.has_type v Tptr ->
         Val.load_result Mptr v = v.
Proof.
  intros. unfold Mptr. Ap64. cbn.
  unfold Tptr in H0. Ap64_in H0.
  destruct v; cbn in *; eauto; try congruence; eauto.
  inv H0. inv H0. inv H0.
Qed.

Lemma load_result_Many64_eq:
    forall v,  Val.load_result Many64 v = v.
Proof.
  intros. reflexivity. Qed.

Lemma enter_fung_exec:
  forall m (rs0: regset),
      (rs0 RSP) <> Vundef -> Val.has_type (rs0 RSP) Tptr ->
      (rs0 RA) <> Vundef -> Val.has_type (rs0 RA) Tptr ->
      exists m1 m2 m3 tsp,
    Mem.alloc m 0 24 = (m1,tsp)
    /\ Mem.store Mptr m1 tsp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2
    /\ Mem.store Mptr m2 tsp (Ptrofs.unsigned (Ptrofs.repr 16)) (rs0 RA) = Some m3
    /\ forall m4 tv, Mem.store Many64 m3 tsp (Ptrofs.unsigned (Ptrofs.repr 8)) tv = Some m4
      -> tv <> Vundef ->
        Mem.load Mptr m4 tsp (Ptrofs.unsigned (Ptrofs.repr 16)) = Some (rs0 RA)
        /\ Mem.load Mptr m4 tsp (Ptrofs.unsigned (Ptrofs.zero)) = Some (rs0 RSP)
        /\ Mem.load Many64 m4 tsp (Ptrofs.unsigned (Ptrofs.repr 8)) = Some tv
        /\ Mem.unchanged_on (fun _ _ => True) m m3
        /\ Mem.unchanged_on (fun _ _ => True) m m4.
Proof.
  intros m rs0 RSP1 RSP2 RA1 RA2.
  destruct (Mem.alloc m 0 24) as [m1 sp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  assert (STORE: {m2| Mem.store Mptr m1 sp (Ptrofs.unsigned Ptrofs.zero) (rs0 RSP) = Some m2}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H. simpl in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_zero.
  red. exists  0. lia. destruct STORE as [m2 STORE1].
  assert (STORE: {m3| Mem.store Mptr m2 sp (Ptrofs.unsigned (Ptrofs.repr 16)) (rs0 RA) = Some m3}).
  apply Mem.valid_access_store.
  red. split. red. intros.
  rewrite Ptrofs.unsigned_repr in H.
  unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem. rlia.
  unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_repr.
  exists 2. lia. rlia.
  destruct STORE as [m3 STORE2].
  exists m1,m2, m3,sp. split. eauto. split. eauto. split. eauto.
  intros m4 tv STORE3 tv1.
  apply Mem.load_store_same in STORE1 as LOAD1.
  apply Mem.load_store_same in STORE2 as LOAD2.
  erewrite <- Mem.load_store_other in LOAD1; eauto.
  cbn in *. rewrite load_result_Mptr_eq in LOAD2; eauto.
  rewrite load_result_Mptr_eq in LOAD1; eauto.
  2:{ right. left. unfold Mptr. Ap64. cbn. Plia. lia. }
  erewrite <- Mem.load_store_other in LOAD1; eauto.
  2:{ right. left. unfold Mptr. Ap64. cbn. Plia. lia. }
  erewrite <- Mem.load_store_other in LOAD2; eauto.
  2:{ right. right. unfold Mptr. Ap64. cbn. Plia. lia. }
  apply Mem.load_store_same in STORE3 as LOAD3.
  cbn in *. 
  assert (UNC1 : Mem.unchanged_on (fun _ _ => True) m m1).
  eapply Mem.alloc_unchanged_on; eauto.
  assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp) m1 m3).
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on; eauto.
  eapply Mem.store_unchanged_on; eauto.
  assert (UNC3: Mem.unchanged_on (fun b ofs => b <> sp) m1 m4).
  eapply Mem.unchanged_on_trans; eauto.
  eapply Mem.store_unchanged_on; eauto.
  repeat apply conj; intuition eauto.
  - inv UNC1. inv UNC2. constructor.
    + eauto with mem.
    + intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst.
      apply Mem.alloc_result in ALLOC. rewrite ALLOC in H0. exploit freshness; eauto.
      eauto with mem.
    + intros. etransitivity. apply unchanged_on_contents0.
      intros. subst. apply Mem.perm_valid_block in H0.
      apply Mem.alloc_result in ALLOC. rewrite ALLOC in H0. exploit freshness; eauto.
      eauto with mem.
      eauto.
  - inv UNC1. inv UNC3. constructor.
    + eauto with mem.
    + intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst.
      apply Mem.alloc_result in ALLOC. rewrite ALLOC in H0. exploit freshness; eauto.
      eauto with mem.
    + intros. etransitivity. apply unchanged_on_contents0.
      intros. subst. apply Mem.perm_valid_block in H0.
      apply Mem.alloc_result in ALLOC. rewrite ALLOC in H0. exploit freshness; eauto.
      eauto with mem.
      eauto.
Qed.

Lemma undef_regs_pc :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs PC = rs PC.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq PC r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rdi :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RDI = rs RDI.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RDI r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rsi :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RSI = rs RSI.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RSI r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rsp :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RSP = rs RSP.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RSP r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rax :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RAX = rs RAX.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RAX r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_rbx :
  forall (rs:regset),
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs RBX = rs RBX.
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  intros. destruct (preg_eq RBX r'). subst.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
  inv H. congruence. inv H0. congruence.
Qed.

Lemma undef_regs_callee_save :
  forall (rs:regset) r,
    is_callee_save r = true ->
    undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs (preg_of r) = rs (preg_of r).
Proof.
  intros. rewrite undef_regs_other. reflexivity.
  destruct r; cbn in *; try congruence;
    intros; destruct H0 as [A|[B|[C|[D|[E|F]]]]]; subst; try congruence.
Qed.

Lemma undef_regs_nil :
  forall rs,
    undef_regs nil rs = rs.
Proof.
  intros. reflexivity. Qed.
(*
Lemma undef_regs_commut : forall l rs r val,
    ~ In r l ->
    (undef_regs l rs) # r <- val = undef_regs l (rs # r <- val).
Proof.
  intros. apply Axioms.functional_extensionality.
  intros. destruct (preg_eq r x).
  - subst. rewrite Pregmap.gss. rewrite undef_regs_other.
    rewrite Pregmap.gss. eauto. intros. intro. subst. apply H. eauto.
  - destruct (in_dec preg_eq x l).
    + Search undef_regs.
    rewrite Pregmap.gso; eauto. rewrite undef_regs_other.
    rewrite undef_regs_other.
    rewrite Pregmap.gso; eauto.
    intros. intro. subst. apply H. eauto.
    intros. intro. subst. apply H. eauto.
    rewrite Pregmap.gss. eauto.
    
    rewrite Pregmap.gss. eauto. 
    rewrite Pregmap.gss. eauto. 
  *)  
Ltac Pgso := rewrite Pregmap.gso; try congruence.
Ltac Pgss := rewrite Pregmap.gss.

(*we can proof d = 0 by the representable property of f in a Mem.inject,
 but this is strong enough here *)
Lemma symbol_address_inject : forall ge tge f b ofs id,
    Genv.match_stbls f ge tge ->
    Genv.symbol_address ge id  ofs = Vptr b ofs ->
    exists b' d, f b = Some (b',d) /\
            Ptrofs.add ofs (Ptrofs.repr d) = ofs /\
          Genv.symbol_address tge id ofs = Vptr b' ofs.
Proof.
  intros.
  eapply Op.symbol_address_inject in H as H1. rewrite H0 in H1.
  inv H1. unfold Genv.symbol_address in H4.
  destruct Genv.find_symbol; try congruence.
  inv H4.
  exists b0, delta. intuition eauto.
  rewrite !H3. eauto.
  rewrite !H3. eauto.
Qed.

Lemma CAinjp_simulation_L1: forward_simulation
                 (cc_c_asm_injp)
                 (cc_c_asm_injp)
                 L1 (Asm.semantics b1).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_c_asm w se2 s1 s2 /\
                          cajw_sg w = int_fptr__void_sg).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as [[f ? ? Hm] sg rs0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  -  (*valid_query*)
    intros. inv H.
    simpl. cbn in *.
    generalize  match_program_id. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros q1 q2 s1 Hq Hi1. inv Hi1.
    inv Hq.
    inv H18. 2:{ rewrite size_int_fptr__void_sg_0 in H3. extlia. }
    rename tm0 into m2. rename m into m1.
    exists (Mem.support m2, State rs0 m2 true).
    generalize  match_program_id. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    repeat apply conj.
    + econstructor; eauto. inv H17.
      subst tsp0. congruence.
    + eauto.
    + subst tvf. unfold Genv.find_funct in TRAN.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      subst targs. rewrite loc_arguments_int_fptr in H11. simpl in H11. inv H11. inv H8.
      inv H4. inv H7.
      econstructor; cbn; eauto.
      inv H17. subst tsp0. congruence.
    + eauto.
  - (* final_state *)
    intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms. inv H. cbn in *.
    exists (rs, m2''). split. constructor.
    econstructor; eauto.
    intros. inv H. rewrite size_int_fptr__void_sg_0 in H9. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. cbn. inv EXT1. inv MS.
    inv H. cbn in *. inv H12. cbn in *.
    symmetry in H8. inv H8.
    eapply Genv.match_stbls_incr in H2; eauto.
    2:{
      intros. exploit H37; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    exists (cajw (injpw j' m m2' Hm'1) intptr__void_sg rs).
    exists (rs,m2'). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id. intro TRAN.
      rewrite H13.
      assert (Val.inject j' (Vptr b ofs) (Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)))).
      econstructor; eauto.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + rename m into m'. rename m1 into m. rename m2 into tm. rename m2' into tm'.
      econstructor; eauto.
      -- rewrite loc_arguments_int. cbn. rewrite H17.
         constructor; eauto.
      -- rewrite H13. econstructor; eauto.
      -- intros. rewrite size_intptr__void_sg_0 in H.
         subst tsp. rewrite H7 in H. inv H. extlia.
      -- subst tsp. rewrite H7. constructor.
      -- subst ra. rewrite H18. constructor.
      -- subst tsp. rewrite H7. constructor. eauto.
      -- eapply args_removed_tailcall_possible.
         red. apply size_intptr__void_sg_0.
      -- congruence.
      -- subst ra. rewrite H18. congruence.
    + constructor; eauto.
      inversion H34. eauto with mem.
    + (*after_external*)
      intros r1 r2 s1' Hr Haf1.
      inv Haf1. inv Hr.
      cbn in *.
      rename m into m1'.
      inv H39. rename m' into m1''. rename tm' into m2''.
      exists ((Mem.support m2), (State rs' m2'' true)). repeat apply conj.
      -- constructor. inversion H47; eauto.
         unfold inner_sp. cbn.
         rewrite H42. subst tsp. rewrite H7.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- assert ( RANGEPERM1: Mem.range_perm m2'' tsb 0 8 Cur Freeable). 
         { red. intros.
           inversion H47.
           eapply unchanged_on_perm; eauto.
         }
         assert ( RANGEPERM2: Mem.range_perm m2'' tsb 16 24 Cur Freeable). 
         { red. intros.
           inversion H47.
           eapply unchanged_on_perm; eauto.
         }
         econstructor; cbn.
         rewrite H42. eauto.
         reflexivity. 
         instantiate (1:= j'0).
         {
           intros. red. intros. destruct (j' b0) as [[tsb' d']|] eqn:Hinj.
           apply H48 in Hinj as EQ. rewrite H0 in EQ. inv EQ.
           intro. apply H9 in H.
           red in H.  eapply H in Hinj as Hp. apply Hp.
           apply H44; eauto.
           apply inject_implies_dom_in in Hm9.
           eapply Hm9; eauto.
           exploit H49; eauto. intros [A B].
           exfalso. apply B. eauto.
         }
         eauto. eauto. instantiate (1:= Hm'5). all: eauto.
         ++ etransitivity. instantiate (1:= injpw j' m1' m2' Hm'1).
            constructor; eauto.
            constructor; eauto.
         ++ rewrite H43. eauto.
         ++ intros. destruct (j' b0) as [[tsb' d']|] eqn:Hj'.
            apply H48 in Hj' as EQ. rewrite H in EQ. inv EQ.
            eauto. exploit H49; eauto. intros [A B].
            exfalso. apply B. eauto.
         ++ rewrite H42. subst tsp. rewrite H7 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H47. 2: eauto.
            intros. eapply H9. right.
            rewrite Ptrofs.add_zero_l in H.
            rewrite Ptrofs.unsigned_repr in H.
            rewrite size_chunk_Mptr in H. Ap64_in H. lia.
            Plia.
         ++ rewrite H42. subst tsp. rewrite H7 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H47. 2: eauto.
            intros. eapply H9. left.
            rewrite Ptrofs.add_zero_l in H.
            rewrite Ptrofs.unsigned_zero in H.
            rewrite size_chunk_Mptr in H. Ap64_in H. lia.
         ++ intros. rewrite H40; eauto.
         ++ inversion H47. eauto with mem.
      -- reflexivity.
  - (*internal_steps*)
    Local Opaque undef_regs.
    Ltac compute_pc := rewrite Ptrofs.add_unsigned;
                       rewrite Ptrofs.unsigned_one; rewrite Ptrofs.unsigned_repr; try rlia; cbn.
    Ltac find_instr := cbn; try rewrite Ptrofs.unsigned_repr; try rlia; cbn; reflexivity.
    intros. inv H; inv H0; inv H; cbn in *.
    ++ (*step_xor*)
      inv H14. symmetry in H7. inv H7.
      destruct (enter_fung_exec m2 rs0) as (m2'1 & m2'2 & m2'3  & tsp &
                                              ALLOC' & STORE1 & STORE2
                                            & STEP2); eauto.
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      apply Mem.fresh_block_alloc in ALLOC' as FRESH'.
      exploit Mem.alloc_right_inject; eauto. intro INJ11.
      exploit Mem.alloc_left_mapped_inject. eauto with mem.
      eauto. eauto with mem. instantiate (1:= 8).
      rlia.
      intros. right. exploit Mem.perm_alloc_inv; eauto.
      rewrite pred_dec_true. intro. rlia. reflexivity.
      intros. 
      exploit Mem.perm_alloc_2; eauto. instantiate (1:= ofs0 + 8). lia.
      eauto with mem.
      cbn. red. intros.
      {
        destruct chunk; simpl; try (exists 8; lia ); try (exists 4; lia); try (exists 2; lia); exists 1; lia.
      }
      intros.
      inv Hm0. exploit mi_mappedblocks; eauto.
      intros (f' & INJ2 & INCR & MAPSP & INCRDIF).
      assert (NEWINJ: forall b d, f' b = Some (tsp,d) -> b = sp).
      {
        intros. destruct (eq_block b0 sp); auto.
        rewrite INCRDIF in H; eauto.
        inv Hm0. exploit mi_mappedblocks; eauto.
        intro. congruence.
      }
      exploit Mem.store_outside_inject; eauto.
      intros. apply NEWINJ in H as EQ. subst b'0.
      rewrite MAPSP in H.  inv H.
      eapply Mem.perm_alloc_3 in H1; eauto.
      rewrite Ptrofs.unsigned_zero in H3.
      unfold Mptr in H3. Ap64_in H3. cbn in H3. extlia.
      intro INJ3.
      exploit Mem.store_outside_inject; eauto.
       intros. apply NEWINJ in H as EQ. subst b'0.
      rewrite MAPSP in H.  inv H.
      eapply Mem.perm_alloc_3 in H1; eauto.
      rewrite Ptrofs.unsigned_repr in H3.
      unfold Mptr in H3. Ap64_in H3. cbn in H3. extlia.
      rlia.
      intro INJ4.
      eapply Genv.find_symbol_match in FINDKEY as FINDK'; eauto.
      destruct FINDK' as [b_mem' [VINJM FINDK']].
      rename H13 into Hpc. rename H17 into Hrdi. rename H18 into Hrsi.
      set (output := Int.xor input key).

      
      exploit Mem.store_mapped_inject; eauto.
      intros (m2'4 & STORE3 & INJ5).
      rewrite Ptrofs.unsigned_zero in STORE3. cbn in STORE3.
      exploit STEP2; eauto. congruence.
      intros (LOAD2 & LOAD1 & LOAD3 & UNC1 & UNC2).
      assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs0 m2 true) E0 s2'
             /\ ms (Call2 (Vptr b ofs) sp m'') (Mem.support m2, s2')).
      { 
        (*execution of Asm code*)
        eexists. split.
        - (*plus steps*)
          econstructor.
      (*Pallocframe*)
      econstructor; eauto.
      find_instr. simpl.
      rewrite ALLOC'. rewrite Ptrofs.add_zero. rewrite STORE1.
      rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
      repeat try Pgso. rewrite Hpc. cbn.
      rewrite Ptrofs.add_zero_l. reflexivity.
      (*read key*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. simpl.
      unfold exec_load. unfold Mem.loadv. unfold eval_addrmode. Ap64. cbn.
      unfold Genv.symbol_address in *. rewrite FINDK'. Ap64.
      rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_zero.
      exploit Mem.load_inject. apply INJ4. apply LOADKEY. eauto.
      intros [v2' [LOADK' INJV2]]. inv INJV2. rewrite Z.add_0_r in LOADK'.
      fold Ptrofs.zero. rewrite LOADK'.
      unfold nextinstr_nf, nextinstr. rewrite undef_regs_pc. Pgso. Pgss.
      cbn.
      rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one. simpl.
      (*Lemma undef_regs_commut : forall l rs r val,
          ~ In r l ->
          (undef_regs l rs) # r <- val = undef_regs l (rs # r <- val). *)
      reflexivity.
      (*xor*)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. Ap64. do 2 Pgso. rewrite undef_regs_rdi.
      rewrite undef_regs_rax. do 4 Pgso. Pgss.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_pc. Pgso. Pgss. cbn.
      compute_pc. reflexivity.
      (*store output*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      Ap64. unfold exec_store. cbn. unfold eval_addrmode. Ap64. simpl. cbn.
      rewrite undef_regs_rsp. repeat Pgso. rewrite undef_regs_rsp.
      do 2 Pgso. Pgss. rewrite undef_regs_rdi. Pgss. cbn. Ap64.
      rewrite Int64.add_zero_l. rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
      2: { unfold Int64.max_unsigned. cbn. lia. }
      unfold Mem.storev.
      Plia.
      rewrite Hrdi. cbn. rewrite STORE3.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_nil.
      rewrite !undef_regs_pc. Pgss. cbn.
      compute_pc. reflexivity.
      (*read address to RDI*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      rewrite undef_regs_rsp. repeat Pgso. rewrite undef_regs_rsp.
      do 2 Pgso. rewrite undef_regs_rsp. do 2 Pgso. Pgss. cbn. Ap64.
      rewrite Int64.add_zero_l. rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
      2: { unfold Int64.max_unsigned. cbn. lia. }
      unfold nextinstr. cbn.
      compute_pc. reflexivity.
      (*call*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      compute_pc. reflexivity.
      apply star_refl. traceEq.
        - constructor; eauto.
          econstructor; eauto.
          + do 5 Pgso. rewrite undef_regs_rsp.
            Pgso. rewrite undef_regs_rsp. do 2 Pgso. rewrite undef_regs_rsp.
            do 2 Pgso. Pgss. reflexivity.
          + simpl. reflexivity.
          + intros. red. intros. intro.
            apply NEWINJ in H1 as EQ. subst b0.
            rewrite MAPSP in H1. inv H1.
            exploit Mem.perm_alloc_3. apply ALLOC.
            eapply Mem.perm_store_2; eauto. intro.
            extlia.
          + red. intros. eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_2; eauto. lia.
          + red. intros. eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_2; eauto. lia.
          + instantiate (1:= INJ5).
          constructor; eauto.
            -- red.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_alloc; eauto.
               eapply Mem.ro_unchanged_store; eauto.
               red. intro. eapply Mem.valid_block_alloc; eauto.
               red. intros. eauto with mem.
            -- eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_alloc; eauto.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_store; eauto.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_store; eauto.
               eapply Mem.ro_unchanged_store; eauto.
               erewrite <- Mem.support_store; eauto.
               red. eauto using Mem.perm_store_2.
               erewrite <- Mem.support_store; eauto.
               red. eauto using Mem.perm_store_2.
               red. intro. eapply Mem.valid_block_alloc; eauto.
               red. intros. eapply Mem.perm_alloc_4; eauto.
               intro. apply Mem.fresh_block_alloc in ALLOC.
               subst. congruence.
            -- red. intros. eauto with mem.
            -- red. intros. inv UNC2. eapply unchanged_on_perm; eauto.
            -- assert (X : Mem.unchanged_on (fun _ _ => True) m1 m').
               eapply Mem.alloc_unchanged_on; eauto.
               assert (Y: Mem.unchanged_on (fun b ofs => b <> sp) m' m'').
               eapply Mem.store_unchanged_on; eauto.
               inv X. inv Y. constructor.
               eauto with mem.
               intros. etransitivity. eauto. apply unchanged_on_perm0.
               intro. subst.
               apply Mem.alloc_result in ALLOC. rewrite ALLOC in H1. exploit freshness; eauto.
               eauto with mem.
               intros. etransitivity. apply unchanged_on_contents0.
               intros. subst. apply Mem.perm_valid_block in H1. intro. subst.
               apply Mem.alloc_result in ALLOC. rewrite ALLOC in H1. exploit freshness; eauto.
               eauto with mem.
               eauto.
            -- eapply Mem.unchanged_on_implies; eauto.
               intros. cbn. auto.
            -- red. intros. destruct (eq_block b1 sp).
               subst. rewrite MAPSP in H1. inv H1. split; eauto.
               rewrite INCRDIF in H1. congruence. eauto.
          + Pgso. Pgss. reflexivity.
          + apply Mem.valid_new_block in ALLOC' as VALID. unfold Mem.valid_block in *.
            erewrite Mem.support_store. 2: eauto.
            erewrite Mem.support_store. 2: eauto.
            erewrite Mem.support_store; eauto.
          + Pgss. rewrite undef_regs_rsi. repeat Pgso. rewrite undef_regs_rsi.
            repeat Pgso. rewrite undef_regs_rsi. repeat Pgso.
          + intros. cbn. repeat try Pgso; destruct r; cbn in *; try congruence; eauto.
            rewrite not_win in H. inv H. Ap64_in H. rewrite not_win in H. inv H.
          + cbn. inversion UNC2. eauto.
      }
      destruct H as [s2' [STEP MS]].  cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
      pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
      ++ (*step_free*)
     assert ({m2''1| Mem.free m2'' tsb 0 24 = Some m2''1}).
     {
       apply Mem.range_perm_free; eauto.
       red. intros.
       apply Mem.free_range_perm in FREE as Rperm1.
       eapply Mem.range_perm_inject in H13; eauto. cbn in H13.
       assert (0<= ofs < 8 \/ (8 <= ofs <16 \/ 16 <= ofs < 24)). lia.
       destruct H0 as [A | [B | C]].
       eapply H8; eauto. eapply H13; eauto. eapply H9; eauto.
     }
     destruct X as [m2'1 FREE'].
     exploit Mem.free_left_inject. apply Hm''. eauto. intro INJ'0.
     exploit Mem.free_right_inject. apply INJ'0. eauto.
     intros. apply H14 in H as EQ. subst b1. rewrite H13 in H. inv H.
     assert (0 <= ofs + 8 < 8 \/ (8 <= ofs + 8 < 16 \/ 16 <= ofs + 8 < 24)). lia.
     destruct H as [A | [b | C]].
     assert (loc_out_of_reach j' m tsb (ofs + 8)).  eapply H7; eauto.
     red in H. exploit H; eauto. replace (ofs + 8 - 8) with ofs by lia.
     eauto with mem.
     eapply Mem.perm_free_4 in H0; eauto. destruct H0. congruence. extlia.
     assert (loc_out_of_reach j' m tsb (ofs + 8)).  eapply H7; eauto.
     red in H. exploit H; eauto. replace (ofs + 8 - 8) with ofs by lia.
     eauto with mem.
     intro INJ'.
     symmetry in H4. inv H4.  inv H19.
     assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b1) (State rs m2'' true) E0 s2'
             /\ ms (Return2 m') (Mem.support m2, s2')).
     {
       eexists. split.
       econstructor. econstructor; eauto. find_instr.
      (* Pfreeframe *)
       simpl. cbn. unfold Mem.loadv. subst tsp. rewrite H3 in *.
       cbn in H15. cbn in H16. cbn. rewrite H15. rewrite H16.
       Plia. cbn. rewrite FREE'. unfold nextinstr. cbn. rewrite H11.
       cbn. compute_pc. reflexivity.
       (*Pret*)
       eapply star_step; eauto. econstructor; eauto. Simplif.
       find_instr. cbn. unfold inner_sp. rewrite <- H.
       rewrite pred_dec_true; eauto.
       eapply star_refl. traceEq.
      - constructor; eauto.
        econstructor. instantiate (1:= INJ'). all: eauto.
        + cbn. inv H10.
          constructor; eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
             inversion H29. eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
          -- red. eauto using Mem.perm_free_3.
          -- red. eauto using Mem.perm_free_3.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1:= fun b ofs => loc_unmapped f b ofs /\ Mem.valid_block m1 b).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. apply H18. eauto.
             intros. constructor; eauto.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1 := fun b ofs => loc_out_of_reach f m1 b ofs /\ Mem.valid_block m2 b).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. apply H17; eauto.
             intros. simpl. intuition auto.
        + intros. cbn.
          cbn. repeat try Pgso; eauto; destruct r; cbn in *; try congruence; eauto.
        + cbn. cbn. inv H10.
          erewrite (Mem.support_free _ _ _ _ _ FREE'). inv H30. eauto.
      }
      destruct H1 as [s2' [STEP MS]].  cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se1 b1); clear; intros.
      pattern (State rs m2'' true),E0,s2'. eapply plus_ind2; eauto; intros.
      * apply plus_one; eauto.
      * eapply plus_trans; eauto.
        apply plus_one. auto.
  - constructor. intros. inv H.
Qed.


Theorem self_simulation_wt :
  forward_simulation wt_c wt_c L1 L1.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [se' sg].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd w = int_fptr__void_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. reflexivity.
  - intros. inv H. exists s1. exists s1. constructor; eauto. inv H0.
    inv H1. cbn. eauto.
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
  - intros. subst.
    exists (se2, intptr__void_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0. constructor; cbn; eauto.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H0. inv H1.
      inv H. cbn. constructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

(* Self-sim using ro *)
Require Import ValueDomain.
Require Import ValueAnalysis.

Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_Callstateg : forall vf i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call1 vf i m)
| sound_Callstatef : forall vf o m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Call2 vf o m)
| sound_Returnstatef : forall b m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return1 b m)
| sound_Returnstateg : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return2 m).
End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma L1_ro : preserves L1 ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + assert (ro_acc m m'').
      eapply ro_acc_trans; eauto.
      eapply ro_acc_alloc; eauto.
      unfold Mem.storev in STORE.
      eapply ro_acc_store; eauto.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
    + apply ro_acc_free in FREE.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor. eapply ro_acc_trans; eauto.
    eapply ro_acc_sound; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Theorem self_simulation_ro :
  forward_simulation ro ro L1 L1.
Proof.
  eapply preserves_fsim. eapply L1_ro; eauto.
Qed.

(** L_1 ⩽ [[server.s]] *)
Lemma semantics_preservation_L1:
  forward_simulation cc_compcert cc_compcert L1 (Asm.semantics b1).
Proof.
  unfold cc_compcert.
  eapply compose_forward_simulations.
  eapply self_simulation_ro.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  eapply compose_forward_simulations.
  eapply CAinjp_simulation_L1.
  eapply semantics_asm_rel; eauto.
Qed.

(** L2 --> b2*)

Section MS.

Variable w0: ccworld (ro @ cc_c_asm_injp).
Let row := snd (fst w0).
Let w := snd w0.
Let wp:= cajw_injp w.

Variable se tse: Genv.symtbl.

Let ge := Genv.globalenv se b2.
Let tge := Genv.globalenv tse b2.

Hypothesis GE: match_stbls injp wp se tse.


Let sg := cajw_sg w.
Let rs0 := cajw_rs w.
Let m2 := match wp with injpw _ _ m2 _ => m2 end.
Let s2 := Mem.support m2.

Let sp0 := rs0 RSP.
Let ra0 := rs0 RA.
Let vf0 := rs0 PC.

Inductive match_state_ro_c_asm : state -> (sup * Asm.state) -> Prop :=
|match_call1_ro m1 b b' ofs eb input j Hm delta:
  wp = injpw j m1 m2 Hm ->
  sp0 <> Vundef -> ra0 <> Vundef ->
  Val.has_type sp0 Tptr -> Val.has_type ra0 Tptr ->
  valid_blockv (Mem.support m2) sp0 ->
  vf0 = Vptr eb Ptrofs.zero ->
  Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
  j b = Some (b', delta) ->
  rs0 RDI = Vint input ->
  rs0 RSI = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
  sound_memory_ro se m1 ->
  match_state_ro_c_asm (Call1 (Vptr b ofs) input m1) (s2, State rs0 m2 true)
|match_call2_ro m1 b ofs j j' Hm (rs:regset) m1' m2' Hm' sb tsb b' delta eb:
    let sp := Vptr sb Ptrofs.zero in let tsp :=rs RSP in let ra := rs RA in let vf := rs PC in
    tsp = Vptr tsb Ptrofs.zero ->
    wp = injpw j m1 m2 Hm ->
    (forall ofs, (0 <= ofs < 8 \/ 16 <= ofs < 24) -> loc_out_of_reach j' m1' tsb ofs) ->
    Mem.range_perm m2' tsb 0 8 Cur Freeable ->
    Mem.range_perm m2' tsb 16 24 Cur Freeable ->
    injp_acc wp (injpw j' m1' m2' Hm') ->
    rs PC = Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) ->
    j b = Some (b', delta) ->
    j' sb = Some (tsb, 8) -> (forall b (d:Z) , j' b = Some (tsb, d) -> b = sb) ->
    rs RDI = Vptr tsb (Ptrofs.repr 8) ->
    ra = Vptr eb (Ptrofs.repr 5) ->
    Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
    sup_In tsb (Mem.support m2') -> ~ sup_In tsb s2 -> ~sup_In sb (Mem.support m1) ->
    vf <> Vundef ->
    Mem.loadv Mptr m2' (Val.offset_ptr tsp (Ptrofs.repr 16)) = Some ra0 ->
    Mem.loadv Mptr m2' (Val.offset_ptr tsp Ptrofs.zero) = Some sp0 ->
    valid_blockv s2 sp0 ->
     (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
     Mem.sup_include s2 (Mem.support m2')  ->
     sound_memory_ro se m1' ->
     match_state_ro_c_asm (Call2 (Vptr b ofs) sb m1') (s2, State rs m2' true)
|match_return1_ro j j' m1 m1'' m2'' Hm Hm'' (rs:regset) eb sb tsb:
    let sp := Vptr sb Ptrofs.zero in let tsp := rs RSP in
    tsp = Vptr tsb Ptrofs.zero ->
    wp = injpw j m1 m2 Hm ->
    (forall ofs,  (0 <= ofs < 8 \/ 16 <= ofs < 24) -> loc_out_of_reach j' m1'' tsb ofs) ->
    Mem.range_perm m2'' tsb 0 8 Cur Freeable ->
    Mem.range_perm m2'' tsb 16 24 Cur Freeable ->
    injp_acc wp (injpw j' m1'' m2'' Hm'') ->
    rs PC = Vptr eb (Ptrofs.repr 5) ->
    Genv.find_funct_ptr tge eb = Some (Internal func_encrypt_b2) ->
    j' sb = Some (tsb, 8) -> (forall b (d:Z) , j' b = Some (tsb, d) -> b = sb) ->
    Mem.loadv Mptr m2'' (Val.offset_ptr tsp (Ptrofs.repr 16)) = Some ra0 ->
    Mem.loadv Mptr m2'' (Val.offset_ptr tsp Ptrofs.zero) = Some sp0 ->
    ~ sup_In tsb s2 -> ~sup_In sb (Mem.support m1) ->
    valid_blockv (Mem.support m2) sp0 ->
    (forall r, is_callee_save r = true  -> rs (preg_of r) = rs0 (preg_of r)) ->
    Mem.sup_include (Mem.support m2) (Mem.support m2'') ->
    match_state_ro_c_asm (Return1 sb m1'') (s2, State rs m2'' true)
|match_return2_ro j' m2'' m1'' (rs:regset) Hm'':
  (injp_acc wp (injpw j' m1'' m2'' Hm'')) ->
   rs RSP = rs0 RSP -> rs PC = rs0 RA ->
   (forall r, is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r)) ->
   Mem.sup_include s2 (Mem.support m2'') ->
   match_state_ro_c_asm (Return2 m1'') (s2, State rs m2'' false).

End MS.

Lemma match_program_id' :
  match_program (fun _ f0 tf => tf = id f0) eq b2 b2.
Proof.
  red. red. constructor; eauto.
  constructor. constructor. eauto. simpl. econstructor; eauto.
  constructor. eauto.
  constructor; cbn; eauto. constructor; eauto.
  econstructor.
  apply linkorder_refl.
  constructor. constructor; eauto.
  constructor. eauto. econstructor.
  apply linkorder_refl. eauto.
  constructor; eauto.
Qed.

Definition source_mem (w: injp_world) := match w with injpw _ m1 _ _ => m1 end.

(*need non-trivial induction*)

Require Import Maps.

Lemma fold_right_get : forall bl se id b vdef,
    sup_In b bl ->
    Genv.find_symbol se id = Some b ->
    Genv.find_info se b = Some (Gvar vdef) ->
    gvar_readonly vdef && negb (gvar_volatile vdef) && definitive_initializer (gvar_init vdef) = true ->
    Maps.PTree.get id (fold_right (check_add_global se) (PTree.empty ablock) bl) =
      Some (store_init_data_list (ablock_init Pbot) 0 (gvar_init vdef)).
Proof.
  induction bl; intros.
  - inv H.
  - destruct (eq_block a b).
    + subst. simpl. unfold check_add_global. simpl.
      apply Genv.find_invert_symbol in H0. rewrite H0.
      simpl. setoid_rewrite H1. rewrite H2.
      rewrite PTree.gss. reflexivity.
    + exploit IHbl; eauto. destruct H. congruence. eauto.
      intro IH.
      simpl. unfold check_add_global.
      destruct Genv.invert_symbol eqn:SYMB; eauto.
      assert (id <> i).
      {
        intro. subst. erewrite Genv.invert_find_symbol in H0; eauto.
        inv H0. congruence.
      }
      destruct Memory.NMap.get; eauto.
      -- destruct g.
         rewrite PTree.gro; eauto.
         destruct ( gvar_readonly v && negb (gvar_volatile v) && definitive_initializer (gvar_init v)).
         rewrite PTree.gso; eauto.
         rewrite PTree.gro; eauto.
      -- rewrite PTree.gro; eauto.
Qed.

Lemma romem_for_ablock : forall se id b vdef,
    Genv.find_symbol se id = Some b  ->   
    Genv.find_info se b = Some (Gvar vdef) ->
    gvar_readonly vdef && negb (gvar_volatile vdef) && definitive_initializer (gvar_init vdef) = true ->
    Maps.PTree.get id (romem_for_symtbl se) = Some (store_init_data_list (ablock_init Pbot) 0 (gvar_init vdef)).
Proof.
  intros. unfold romem_for_symtbl.
  eapply fold_right_get; eauto.
  eapply Genv.genv_symb_range; eauto.
Qed.

Lemma CAinjp_simulation_L2: forward_simulation
                 (ro @ cc_c_asm_injp)
                 (ro @ cc_c_asm_injp)
                 L2 (Asm.semantics b2).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state_ro_c_asm w se1 se2 s1 s2 /\
                          cajw_sg (snd w) = int_fptr__void_sg /\
                          ro_mem (snd (fst w)) = source_mem (cajw_injp (snd w))).
  eapply forward_simulation_plus with (match_states := ms);
  destruct w as  [[? [? ?]] [[f ? ? Hm] sg rs0]]; destruct Hse as [Hi Hse];
    inv Hi; inv Hse; subst; cbn in *; eauto.
  -  (*valid_query*)
    intros q1' q2 [q1 [Hqi Hq]]. inv Hqi. inv Hq.
    simpl. cbn in *.
    generalize  match_program_id'. intro TRAN.
    eapply Genv.is_internal_transf in TRAN; eauto.
  - (* initial *)
    intros q1' q2 s1 [q1 [Hqi Hq]] Hi1. inv Hi1.
    inv Hqi. inv Hq.
    inv H19. 2:{ rewrite size_int_fptr__void_sg_0 in H4. extlia. }
    rename tm0 into m2. rename m into m1.
    exists (Mem.support m2, State rs0 m2 true).
    generalize  match_program_id'. intro TRAN.
    eapply Genv.find_funct_transf in TRAN; eauto.
    repeat apply conj.
    + econstructor; eauto. inv H18.
      subst tsp0. congruence.
    + eauto.
    + subst tvf. unfold Genv.find_funct in TRAN.
      destruct (rs0 PC) eqn:HPC; try congruence. destruct Ptrofs.eq_dec; try congruence.
      subst targs. rewrite loc_arguments_int_fptr in H12. simpl in H12. inv H12. inv H9.
      inv H7. inv H8.
      econstructor; cbn; eauto.
      inv H18. subst tsp0. congruence.
      inv H. eauto.
    + eauto.
    + inv H. eauto.
  - (* final_state *)
    intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms. inv H. cbn in *. inv H0.
    exists (rs, m2''). split. constructor.
    exists (cr Vundef m). split. constructor. constructor.
    inv H3. constructor; eauto. inversion H17. eauto.
    econstructor; eauto.
    intros. inv H. rewrite size_int_fptr__void_sg_0 in H1. extlia.
  - (* at_external*)
    intros s1 s2 q1 MS EXT1. cbn. inv EXT1. inv MS.
    inv H. cbn in *. inv H13. cbn in *.
    symmetry in H9. inv H9.
    eapply Genv.match_stbls_incr in H2; eauto.
    2:{
      intros. exploit H39; eauto. intros [A B].
      unfold Mem.valid_block in *. split; eauto with mem.
    }
    rename m into m1'.
    exists ((s,row s m1'),(cajw (injpw j' m1' m2' Hm'1) intptr__void_sg rs)).
    exists (rs,m2'). repeat apply conj.
    + econstructor; eauto.
      generalize  match_program_id'. intro TRAN.
      rewrite H14.
      assert (Val.inject j' (Vptr b ofs) (Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)))).
      econstructor; eauto.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + rename m1 into m. rename m2 into tm. rename m2' into tm'. rename m1' into m'.
      exists (cq (Vptr b ofs) intptr__void_sg (Vptr sb Ptrofs.zero :: nil) m'). split.
      constructor. constructor. eauto.
      econstructor; eauto.
      -- rewrite loc_arguments_int. cbn. rewrite H18.
         constructor; eauto.
      -- rewrite H14. econstructor; eauto.
      -- intros. rewrite size_intptr__void_sg_0 in H.
         subst tsp. rewrite H8 in H. inv H. extlia.
      -- subst tsp. rewrite H8. constructor.
      -- subst ra. rewrite H19. constructor.
      -- subst tsp. rewrite H8. constructor. eauto.
      -- eapply args_removed_tailcall_possible.
         red. apply size_intptr__void_sg_0.
      -- congruence.
      -- subst ra. rewrite H19. congruence.
    + constructor; eauto.
    + constructor; eauto.
      inversion H36. eauto with mem.
    + (*after_external*)
      intros r1' r2 s1' [r1 [Hri Hr]] Haf1.
      inv Haf1. inv Hri. inv H. inv Hr.
      cbn in *.
      inv H0.
      inv H42. rename m' into m1''. rename tm' into m2''.
      exists ((Mem.support m2), (State rs' m2'' true)). repeat apply conj.
      -- constructor. inversion H49; eauto.
         unfold inner_sp.  cbn.
         rewrite H45. subst tsp. rewrite H8.
         rewrite pred_dec_false; eauto.
      -- reflexivity.
      -- assert ( RANGEPERM1: Mem.range_perm m2'' tsb 0 8 Cur Freeable). 
         { red. intros. inversion H49.
           eapply unchanged_on_perm; eauto.
         }
         assert ( RANGEPERM2: Mem.range_perm m2'' tsb 16 24 Cur Freeable). 
         { red. intros. inversion H49.
           eapply unchanged_on_perm; eauto.
         }
         econstructor; cbn.
         rewrite H45. eauto.
         reflexivity.
         instantiate (1:= j'0).
         {
           intros. red. intros. destruct (j' b0) as [[tsb' d']|] eqn:Hinj.
           apply H50 in Hinj as EQ. rewrite H0 in EQ. inv EQ.
           intro. apply H10 in H.
           red in H.  eapply H in Hinj as Hp. apply Hp.
           apply H41; eauto.
           apply inject_implies_dom_in in Hm9.
           eapply Hm9; eauto.
           exploit H51; eauto. intros [A B].
           exfalso. apply B. eauto.
         }
         eauto. eauto. instantiate (1:= Hm'5). all: eauto.
         ++ etransitivity. instantiate (1:= injpw j' m1' m2' Hm'1).
            constructor; eauto.
            constructor; eauto.
         ++ rewrite H46. eauto.
         ++ intros. destruct (j' b0) as [[tsb' d']|] eqn: Hf.
            * apply H50 in Hf as Hf'. rewrite H in Hf'. inv Hf'. eauto.
            * exploit H51; eauto. intros [A B]. exfalso. apply B; eauto.
         ++ rewrite H45. subst tsp. rewrite H8 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H49. 2: eauto.
            intros. eapply H10. right.
            rewrite Ptrofs.add_zero_l in H.
            rewrite Ptrofs.unsigned_repr in H.
            rewrite size_chunk_Mptr in H. Ap64_in H. lia.
            Plia.
         ++ rewrite H45. subst tsp. rewrite H8 in *. cbn in *.
            eapply Mem.load_unchanged_on. apply H49. 2: eauto.
            intros. eapply H10. left.
            rewrite Ptrofs.add_zero_l in H.
            rewrite Ptrofs.unsigned_zero in H.
            rewrite size_chunk_Mptr in H. Ap64_in H. lia.
         ++ intros. rewrite H43; eauto.
         ++ inversion H49. eauto with mem.
     -- reflexivity.
     -- reflexivity.            
  - (*internal_steps*)
    Local Opaque undef_regs.
    intros. inv H; inv H0; inv H; cbn in *. inv H1.
    ++ (*step_xor*)
      inv H13. symmetry in H8. inv H8.
      destruct (enter_fung_exec m2 rs0) as (m2'1 & m2'2 & m2'3 & tsp &
                                              ALLOC' & STORE1 & STORE2
                                            & STEP2); eauto.
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      apply Mem.fresh_block_alloc in ALLOC' as FRESH'.
      exploit Mem.alloc_right_inject; eauto. intro INJ11.
      exploit Mem.alloc_left_mapped_inject. eauto with mem.
      eauto. eauto with mem. instantiate (1:= 8).
      rlia.
      intros. right. exploit Mem.perm_alloc_inv; eauto.
      rewrite pred_dec_true. intro. rlia. reflexivity.
      intros. 
      exploit Mem.perm_alloc_2; eauto. instantiate (1:= ofs1 + 8). lia.
      eauto with mem.
      cbn. red. intros.
      {
        destruct chunk; simpl; try (exists 8; lia ); try (exists 4; lia); try (exists 2; lia); exists 1; lia.
      }
      intros.
      inv Hm0. exploit mi_mappedblocks; eauto.
      intros (f' & INJ2 & INCR & MAPSP & INCRDIF).
      assert (NEWINJ: forall b d, f' b = Some (tsp,d) -> b = sp).
      {
        intros. destruct (eq_block b1 sp); auto.
        rewrite INCRDIF in H1; eauto.
        inv Hm0. exploit mi_mappedblocks; eauto.
        intro. congruence.
      }
      exploit Mem.store_outside_inject; eauto.
      intros. apply NEWINJ in H1 as EQ. subst b'0.
      rewrite MAPSP in H1.  inv H1.
      eapply Mem.perm_alloc_3 in H3; eauto.
      rewrite Ptrofs.unsigned_zero in H4.
      unfold Mptr in H4. Ap64_in H4. cbn in H4. extlia.
      intro INJ3.
      exploit Mem.store_outside_inject; eauto.
       intros. apply NEWINJ in H1 as EQ. subst b'0.
      rewrite MAPSP in H1.  inv H1.
      eapply Mem.perm_alloc_3 in H3; eauto.
      rewrite Ptrofs.unsigned_repr in H4.
      unfold Mptr in H4. Ap64_in H4. cbn in H4. extlia.
      rlia.
      intro INJ4.
      eapply Genv.find_symbol_match in FINDKEY as FINDK'; eauto.
      destruct FINDK' as [b_mem' [VINJM FINDK']].
      rename H14 into Hpc. rename H18 into Hrdi. rename H19 into Hrsi.
      assert (ROREAD : key = Int.repr 42).
      { clear - H20 ALLOC FINDKEY LOADKEY Hse1.
        apply ro_acc_alloc in ALLOC.
        exploit ro_acc_sound; eauto. intro Hsound.
        clear ALLOC H20.
        inv Hsound.
        red in H. red in Hse1.
        assert (Maps.PTree.get key_id (prog_defmap (erase_program b2)) = Some (Gvar key_def_const)).
        { cbn.
        rewrite Maps.PTree.gso; try congruence.
        rewrite Maps.PTree.gso; try congruence.
        rewrite Maps.PTree.gss. reflexivity.
        unfold key_id. unfold encrypt_id. congruence.
        unfold key_id. unfold complete_id. congruence.
        }
        exploit Hse1; eauto.
        intros (key_b' &  vardef & FIND' & INFO & L).
        inv L. inv H3. inv H9. inv H8.
        rewrite FINDKEY in FIND'. inv FIND'.
        exploit H; eauto.
        simpl.
        apply Genv.find_invert_symbol in FINDKEY as INVERT.
        rewrite INVERT. reflexivity.
        eapply romem_for_ablock; eauto. cbn.
        intros [_ [[_ B] _]].
        exploit B; eauto. intro. cbn in H2. rewrite Ptrofs.unsigned_zero in H2.
        unfold ablock_store,ablock_load in H2. cbn in H2. rewrite Maps.ZTree.gss in H2.
        inv H2. reflexivity.
      }
      set (output := Int.xor input key).
      exploit Mem.store_mapped_inject; eauto.
      intros (m2'4 & STORE3 & INJ5).
      rewrite Ptrofs.unsigned_zero in STORE3. cbn in STORE3.
      exploit STEP2; eauto. congruence.
      intros (LOAD2 & LOAD1 & LOAD3 & UNC1 & UNC2).
      assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b2) (State rs0 m2 true) E0 s2'
             /\ ms (Call2 (Vptr b ofs) sp m'') (Mem.support m2, s2')).
      { 
        (*execution of Asm code*)
        eexists. split.
        - (*plus steps*)
          econstructor.
      (*Pallocframe*)
      econstructor; eauto.
      find_instr. simpl.
      rewrite ALLOC'. rewrite Ptrofs.add_zero. rewrite STORE1.
      rewrite Ptrofs.add_zero_l. rewrite STORE2. unfold nextinstr.
      repeat try Pgso. rewrite Hpc. cbn.
      rewrite Ptrofs.add_zero_l. reflexivity.
      (*xor*)
      eapply star_step; eauto. econstructor; eauto. Simplif.
      find_instr. simpl. Ap64. do 2 Pgso.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_pc. Pgso. Pgss. cbn.
      rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_one. simpl.
      reflexivity.
      (*store output*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      Ap64. unfold exec_store. cbn. unfold eval_addrmode. Ap64. simpl. cbn.
      rewrite undef_regs_rsp. do 2 Pgso. Pgss.
      rewrite undef_regs_rdi. Pgss. cbn. Ap64.
      rewrite Int64.add_zero_l. rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
      2: { unfold Int64.max_unsigned. cbn. lia. }
      unfold Mem.storev.
      Plia.
      rewrite Hrdi. cbn. rewrite ROREAD in STORE3. rewrite STORE3.
      unfold nextinstr_nf, nextinstr. cbn.
      rewrite undef_regs_nil.
      rewrite !undef_regs_pc. Pgss. cbn.
      compute_pc. reflexivity.
      (*read address to RDI*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      rewrite undef_regs_rsp. repeat Pgso. rewrite undef_regs_rsp.
      do 2 Pgso. Pgss. cbn. Ap64.
      rewrite Int64.add_zero_l. rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
      2: { unfold Int64.max_unsigned. cbn. lia. }
      unfold nextinstr. cbn.
      compute_pc. reflexivity.
      (*call*)
      eapply star_step; eauto. econstructor; eauto. Simplif. find_instr. cbn.
      compute_pc. reflexivity.
      apply star_refl. traceEq.
        - constructor; eauto.
          econstructor; eauto.
          + do 5 Pgso. rewrite undef_regs_rsp.
            Pgso. rewrite undef_regs_rsp. do 2 Pgso.
            Pgss. reflexivity.
          + simpl. reflexivity.
          + intros. red. intros. intro.
            apply NEWINJ in H3 as EQ. subst b1.
            rewrite MAPSP in H3. inv H3.
            exploit Mem.perm_alloc_3. apply ALLOC.
            eapply Mem.perm_store_2; eauto. intro.
            extlia.
          + red. intros. eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_2; eauto. lia.
          + red. intros. eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_2; eauto. lia.
          + instantiate (1:= INJ5).
            constructor; eauto.
              -- red.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_alloc; eauto.
               eapply Mem.ro_unchanged_store; eauto.
               red. intro. eapply Mem.valid_block_alloc; eauto.
               red. intros. eauto with mem.
            -- eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_alloc; eauto.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_store; eauto.
               eapply Mem.ro_unchanged_trans.
               eapply Mem.ro_unchanged_store; eauto.
               eapply Mem.ro_unchanged_store; eauto.
               erewrite <- Mem.support_store; eauto.
               red. eauto using Mem.perm_store_2.
               erewrite <- Mem.support_store; eauto.
               red. eauto using Mem.perm_store_2.
               red. intro. eapply Mem.valid_block_alloc; eauto.
               red. intros. eapply Mem.perm_alloc_4; eauto.
               intro. apply Mem.fresh_block_alloc in ALLOC.
               subst. congruence.
            -- red. intros. eauto with mem.
            -- red. intros. inv UNC2. eapply unchanged_on_perm; eauto.
            -- assert (X : Mem.unchanged_on (fun _ _ => True) m1 m').
               eapply Mem.alloc_unchanged_on; eauto.
               assert (Y: Mem.unchanged_on (fun b ofs => b <> sp) m' m'').
               eapply Mem.store_unchanged_on; eauto.
               inv X. inv Y. constructor.
               eauto with mem.
               intros. etransitivity. eauto. apply unchanged_on_perm0.
               intro. subst.
               apply Mem.alloc_result in ALLOC. rewrite ALLOC in H3. exploit freshness; eauto.
               eauto with mem.
               intros. etransitivity. apply unchanged_on_contents0.
               intros. subst. apply Mem.perm_valid_block in H3. intro. subst.
               apply Mem.alloc_result in ALLOC. rewrite ALLOC in H3. exploit freshness; eauto.
               eauto with mem.
               eauto.
            -- eapply Mem.unchanged_on_implies; eauto.
               intros. cbn. auto.
            -- red. intros. destruct (eq_block b1 sp).
               subst. rewrite MAPSP in H3. inv H3. split; eauto.
               rewrite INCRDIF in H3. congruence. eauto.
          + Pgso. Pgss. reflexivity.
          + apply Mem.valid_new_block in ALLOC' as VALID. unfold Mem.valid_block in *.
            erewrite Mem.support_store. 2: eauto.
            erewrite Mem.support_store. 2: eauto.
            erewrite Mem.support_store; eauto.
          + Pgss. rewrite undef_regs_rsi. repeat Pgso. rewrite undef_regs_rsi.
            repeat Pgso.
          + cbn. rewrite <- H. constructor. eauto.
          + intros. cbn. repeat try Pgso; destruct r; cbn in *; try congruence; eauto.
            rewrite not_win in H1. inv H1. Ap64_in H1. rewrite not_win in H1. inv H1.
          + cbn. inversion UNC2. eauto.
          + eapply ro_acc_sound; eauto. eapply ro_acc_trans.
            eapply ro_acc_alloc; eauto. eapply ro_acc_store; eauto.
      }
      destruct H1 as [s2' [STEP MS]]. cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se2 b2); clear; intros.
      pattern (State rs0 m2 true),E0,s2'. eapply plus_ind2; eauto; intros.
    * apply plus_one; eauto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
      ++ (*step_free*)
           assert ({m2''1| Mem.free m2'' tsb 0 24 = Some m2''1}).
     {
       apply Mem.range_perm_free; eauto.
       red. intros.
       apply Mem.free_range_perm in FREE as Rperm1.
       eapply Mem.range_perm_inject in H14; eauto. cbn in H14.
       assert (0<= ofs < 8 \/ (8 <= ofs <16 \/ 16 <= ofs < 24)). lia.
       destruct H0 as [A | [B | C]].
       eapply H9; eauto. eapply H14; eauto. eapply H10; eauto.
     }
     destruct X as [m2'1 FREE'].
     exploit Mem.free_left_inject. apply Hm''. eauto. intro INJ'0.
     exploit Mem.free_right_inject. apply INJ'0. eauto.
     intros. apply H15 in H as EQ. subst b1. rewrite H14 in H. inv H.
     assert (0 <= ofs + 8 < 8 \/ (8 <= ofs + 8 < 16 \/ 16 <= ofs + 8 < 24)). lia.
     destruct H as [A | [b | C]].
     assert (loc_out_of_reach j' m tsb (ofs + 8)).  eapply H8; eauto.
     red in H. exploit H; eauto. replace (ofs + 8 - 8) with ofs by lia.
     eauto with mem.
     eapply Mem.perm_free_4 in H0; eauto. destruct H0. congruence. extlia.
     assert (loc_out_of_reach j' m tsb (ofs + 8)).  eapply H8; eauto.
     red in H. exploit H; eauto. replace (ofs + 8 - 8) with ofs by lia.
     eauto with mem.
     intro INJ'.
     symmetry in H7. inv H7. inv H20.
     assert (exists s2': Asm.state,
             plus (Asm.step (Mem.support m2)) (Genv.globalenv se2 b2) (State rs m2'' true) E0 s2'
             /\ ms (Return2 m') (Mem.support m2, s2')).
     {
       eexists. split.
       econstructor. econstructor; eauto. find_instr.
      (* Pfreeframe *)
       simpl. cbn. unfold Mem.loadv. subst tsp. rewrite H4 in *.
       cbn in H16. cbn in H17. cbn. rewrite H16. rewrite H17.
       Plia. cbn. rewrite FREE'. unfold nextinstr. cbn. rewrite H12.
       cbn. compute_pc. reflexivity.
       (*Pret*)
       eapply star_step; eauto. econstructor; eauto. Simplif.
       find_instr. cbn. unfold inner_sp. rewrite <- H.
       rewrite pred_dec_true; eauto.
       eapply star_refl. traceEq.
      - constructor; eauto.
        econstructor. instantiate (1:= INJ'). all: eauto.
        + cbn. inv H11.
          constructor; eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
             inversion H30. eauto.
          -- eapply Mem.ro_unchanged_trans; eauto.
             eapply Mem.ro_unchanged_free; eauto.
          -- red. eauto using Mem.perm_free_3.
          -- red. eauto using Mem.perm_free_3.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1:= fun b ofs => loc_unmapped f b ofs /\ Mem.valid_block m1 b).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. apply H19. eauto.
             intros. constructor; eauto.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1 := fun b ofs => loc_out_of_reach f m1 b ofs /\ Mem.valid_block m2 b).
             eapply Mem.free_unchanged_on; eauto.
             intros. intros [A B]. apply H18; eauto.
             intros. simpl. intuition auto.
        + intros. cbn.
          cbn. repeat try Pgso; eauto; destruct r; cbn in *; try congruence; eauto.
        + cbn. inv H11.
          erewrite (Mem.support_free _ _ _ _ _ FREE'). inv H31. eauto.
      }
      destruct H3 as [s2' [STEP MS]].  cbn.
      exists (Mem.support m2, s2'). intuition eauto.
      revert STEP. generalize (Mem.support m2), (Genv.globalenv se2 b2); clear; intros.
      pattern (State rs m2'' true),E0,s2'. eapply plus_ind2; eauto; intros.
      * apply plus_one; eauto.
      * eapply plus_trans; eauto.
        apply plus_one. auto.
  - constructor. intros. inv H.
Qed.

Theorem self_simulation_wt' :
  forward_simulation wt_c wt_c L2 L2.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [se' sg].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd w = int_fptr__void_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. reflexivity.
  - intros. inv H. exists s1. exists s1. constructor; eauto. inv H0.
    inv H1. cbn. eauto.
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
  - intros. subst.
    exists (se2, intptr__void_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0. constructor; cbn; eauto.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H0. inv H1.
      inv H. cbn. constructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.


Lemma cc_compcert_wt_ro:
  cceqv cc_compcert (wt_c @ (ro @ cc_c_asm_injp) @ cc_asm injp).
Proof.
  split; unfold cc_compcert.
  etransitivity. rewrite <- (cc_compose_assoc ro).
  rewrite inv_commute_ref. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc ro).
  reflexivity. reflexivity.
  etransitivity. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite inv_commute_ref. rewrite cc_compose_assoc.
  reflexivity. reflexivity.
Qed.

(** L_2 ⩽ [[server_opt.s]] *)
Lemma semantics_preservation_L2:
  forward_simulation cc_compcert cc_compcert L2 (Asm.semantics b2).
Proof.
  rewrite cc_compcert_wt_ro at 1.
  rewrite cc_compcert_wt_ro.
  eapply compose_forward_simulations.
  eapply self_simulation_wt'.
  eapply compose_forward_simulations.
  eapply CAinjp_simulation_L2.
  eapply semantics_asm_rel; eauto.
Qed.

