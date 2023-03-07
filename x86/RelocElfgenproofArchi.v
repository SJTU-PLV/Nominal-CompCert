Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes RelocElf RelocElfArchi Globalenvs.
Require Import Linking RelocProgLinking RelocElfLinking Errors.
Require Import EncDecRet RelocElfgen LocalLib RelocProgGlobalenvs.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import RelocProgSemantics2 RelocElfSemantics.
Require Import SymbtableDecode ReloctablesEncode ReloctablesDecode.
Require Import RelocProgSemanticsArchi.
Require Import ReloctablesEncodeArchi.
Require Import RelocElfgenproof0.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.


Lemma decode_encode_reloctable_correct: forall n l bs m1 m2 (M: match_idxmap m1 m2),
    (* let reloclen := if Archi.ptr64 then 24%nat else 8%nat in *)
    length l = n ->
    encode_reloctable m1 l = OK bs ->
    fold_left (acc_decode_reloctable_section reloc_entry_size m2) bs (OK ([], [], 1%nat)) = OK (l, [], 1%nat).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in H0. inv H0.
  unfold decode_reloctable_section. simpl. auto.

  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a1 & A1 & B1). subst.
  clear H.
  unfold encode_reloctable in H0. rewrite fold_left_app in H0.
  simpl in H0. unfold acc_reloctable in H0 at 1.
  monadInv H0. exploit IHn;eauto.
  intros. rewrite fold_left_app.

  rewrite H. clear H EQ IHn.
  exploit encode_relocentry_len;eauto.
  eapply encode_reloc_info_len.  
  intros LEN. 
  rename x0 into l.
  clear x.
  eapply (ReloctablesDecodeArchi.decode_encode_relocentry encode_reloc_info decode_reloc_info) in EQ1;eauto.
  2: eapply encode_reloc_info_len.
  2: eapply decode_encode_reloc_info.

  unfold acc_decode_reloctable_section. unfold reloc_entry_size.
  destruct Archi.ptr64.
  - do 25 (destruct l as [| ?b ?] ;simpl in LEN;try congruence).
    simpl in *. rewrite EQ1. simpl. auto.
  - do 9 (destruct l as [| ?b ?] ;simpl in LEN;try congruence).
    simpl in *. rewrite EQ1. simpl. auto.
Qed.


Section WITH_INSTR_SIZE.
  Variable instr_size: instruction -> Z.

Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: elf_file.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := RelocProgSemantics2.globalenv instr_size  prog.
Let tge := globalenv instr_size  tprog.


Lemma eval_addrmode_match_ge: forall ge1 ge2 a rs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
Proof.
  unfold eval_addrmode. destruct Archi.ptr64;intros.
  - unfold eval_addrmode64.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
  - unfold eval_addrmode32.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
Qed.

Lemma exec_load_match_ge: forall sz ge1 ge2 chunk m a rs rd (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_load sz ge1 chunk m a rs rd = exec_load sz ge2 chunk m a rs rd.
Proof.
  unfold exec_load.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.

Lemma exec_store_match_ge: forall sz ge1 ge2 chunk m a rs rd l (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_store sz ge1 chunk m a rs rd l = exec_store sz ge2 chunk m a rs rd l.
Proof.
  unfold exec_store.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.

Lemma eval_builtin_arg_match_ge: forall rs sp m arg varg ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
        eval_builtin_arg preg ge1 rs sp m arg varg ->
        eval_builtin_arg preg ge2 rs sp m arg varg.
Proof.
  induction 2;try constructor;auto.
  rewrite MATCHGE in H. auto.
  rewrite MATCHGE. constructor.
Qed.

Lemma eval_builtin_args_match_ge: forall rs sp m args vargs ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
        eval_builtin_args preg ge1 rs sp m args vargs ->
        eval_builtin_args preg ge2 rs sp m args vargs.
Proof.
  induction 2.
  - constructor.
  - econstructor.
    eapply eval_builtin_arg_match_ge;eauto.
    eauto.
Qed.

Lemma step_simulation: forall st1 st2 t,
    step instr_size ge st1 t st2 ->
    step instr_size tge st1 t st2.
Proof.
  intros.
  unfold ge,tge in *.
  exploit gen_reloc_elf_correct;eauto.
  eapply decode_encode_reloctable_correct.
  unfold globalenv.
  intros (p' & D1 & E1).
  rewrite D1.
  unfold RelocProgSemantics2.globalenv in *.
  destr_in H.
  exploit decode_prog_code_section_correct;eauto.
  intros (p2' & D2 & E2). rewrite D2.

  2: {
    (* trivial cases *)
  destr.
  exploit decode_prog_code_section_correct. eapply program_equiv_sym in E1.
  eauto. eauto.
  intros (p2' & D2 & E2). congruence.

  assert ((empty_program1 prog) = (empty_program1 p')).
  unfold empty_program1.
  f_equal.
  apply pe_prog_defs;eauto.
  apply pe_prog_main;eauto.
  apply pe_prog_senv;eauto.
  rewrite <- H0. auto. }
  
  inv H.
  - eapply exec_step_internal;eauto.
    + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
      destr. erewrite program_equiv_ext_funs1 in H1.
      eauto. eauto.
    + unfold RelocProgGlobalenvs.Genv.find_instr.
      erewrite program_equiv_instr_map.
      eauto. eapply program_equiv_sym. eauto.
    + apply program_equiv_sym in E2.
      destruct i;simpl in *;auto.
      1-27: try (erewrite program_equiv_symbol_address1;eauto).
      1-24: try (erewrite exec_load_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).
      1-12: try (erewrite exec_store_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).
      rewrite <- H3. do 3 f_equal.
      unfold eval_addrmode32.
      destruct a. f_equal.
      f_equal. destr.
      destruct p0. eapply program_equiv_symbol_address1;eauto.
      rewrite <- H3. do 3 f_equal.
      unfold eval_addrmode64.
      destruct a. f_equal.
      f_equal. destr.
      destruct p0. eapply program_equiv_symbol_address1;eauto.

  (* - eapply exec_step_builtin with (vargs:= vargs);eauto. *)
  (*   + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *. *)
  (*     destr. erewrite program_equiv_ext_funs1 in H1. *)
  (*     eauto. eauto. *)
  (*   + unfold RelocProgGlobalenvs.Genv.find_instr. *)
  (*     erewrite program_equiv_instr_map. *)
  (*     eauto. eapply program_equiv_sym. eauto. *)
  (*   + eapply eval_builtin_args_match_ge. *)
  (*     eapply program_equiv_symbol_address1;eauto. *)
  (*     eauto. *)
  (*   + eapply external_call_symbols_preserved with (ge1:= (Genv.genv_senv (RelocProgSemantics.globalenv instr_size p))). *)
  (*     simpl. erewrite pe_prog_senv. *)
  (*     unfold Senv.equiv. split;eauto. *)
  (*     auto. auto. *)
      
  - eapply exec_step_external;eauto.
    + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
      destr. erewrite program_equiv_ext_funs1 in H1.
      eauto. eauto.
    + eapply external_call_symbols_preserved with (ge1:= (Genv.genv_senv (RelocProgGlobalenvs.globalenv instr_size p))).
      simpl. erewrite pe_prog_senv.
      unfold Senv.equiv. split;eauto.
      auto. auto.
Qed.


End PRESERVATION.

  
Lemma initial_state_gen_match: forall D rs m st (p tp: RelocProg.program fundef unit instruction D),
    program_equiv p tp ->
    initial_state_gen instr_size (decode_program instr_size p) rs m st ->
    exists st', initial_state_gen instr_size (decode_program instr_size tp) rs m st' /\ st = st'.
Proof.
  intros.
  inv H0.
  set (ge' := RelocProgGlobalenvs.globalenv instr_size (decode_program instr_size tp)).
  set (rs0' :=  ((rs # PC <-
           (Genv.symbol_address ge' (RelocProg.prog_main (decode_program instr_size tp)) Ptrofs.zero))
          # RA <- Vnullptr) # RSP <-
         (Vptr stk
            (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8))
               (Ptrofs.repr (size_chunk Mptr))))).
  
  exists (State rs0' m2). split;auto.
  econstructor;eauto.
  f_equal.
  unfold rs0,rs0'.
  assert ((RelocProg.prog_main (decode_program instr_size p)) = (RelocProg.prog_main (decode_program instr_size tp))).
  unfold decode_program. simpl.
  eapply pe_prog_main;eauto.
  rewrite H0.

  unfold ge,ge'.
  erewrite program_equiv_symbol_address;eauto.
  eapply decode_program_equiv. auto.    
Qed.

End WITH_INSTR_SIZE.
