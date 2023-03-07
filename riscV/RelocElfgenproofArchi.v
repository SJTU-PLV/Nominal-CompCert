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
  - do 13 (destruct l as [| ?b ?] ;simpl in LEN;try congruence).
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


Lemma eval_offset_match_ge: forall ge1 ge2 ofs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
    eval_offset ge1 ofs = eval_offset ge2 ofs.
Proof.
  unfold eval_offset. intros.
  destr.
  eapply low_half_match_ge. eauto.
Qed.  

    
Lemma exec_load_match_ge: forall sz ge1 ge2 chunk m rs ra rd ofs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_load sz ge1 chunk rs m rd ra ofs = exec_load sz ge2 chunk rs m rd ra ofs.
Proof.
  unfold exec_load.
  intros.
  erewrite eval_offset_match_ge;eauto.
Qed.

Lemma exec_store_match_ge: forall sz ge1 ge2 chunk m rs ra s ofs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_store sz ge1 chunk rs m s ra ofs = exec_store sz ge2 chunk rs m s ra ofs.
Proof.
  unfold exec_store.
  intros.
  erewrite eval_offset_match_ge;eauto.
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
      1-24: try (erewrite program_equiv_symbol_address1;eauto).
      1-21: try (erewrite exec_load_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).
      1-10: try (erewrite exec_store_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).

      erewrite high_half_match_ge;eauto;eapply program_equiv_symbol_address1;eauto.
      
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
  set (rs0' :=(((Pregmap.init Vundef) # PC <-
           (Genv.symbol_address ge' (RelocProg.prog_main (decode_program instr_size tp)) Ptrofs.zero))
          # X2 <- Vnullptr) # X1 <- Vnullptr).
  
  exists (State rs0' m). split;auto.
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
