Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes RelocElf Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking RelocProgLinking RelocElfLinking Errors.
Require Import EncDecRet RelocElfgen LocalLib RelocProgGlobalenvs.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2 RelocElfSemantics.
Require Import SymbtableDecode ReloctablesEncode.
Require Import RelocProgSemanticsArchi.
Require Import ReloctablesEncodeArchi.
Require Import RelocElfgenproof0 RelocElfgenproofArchi.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.



Lemma store_init_data_bytes_match_ge: forall n bytes reloctbl m b p ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    length bytes = n ->
    store_init_data_bytes ge1 reloctbl m b p bytes = store_init_data_bytes ge2 reloctbl m b p bytes.
Proof. 
  unfold store_init_data_bytes. intros. do 4 f_equal.
  generalize H. clear H. revert bytes.
  generalize dependent n. 
  induction n;intros.
  - rewrite length_zero_iff_nil in H. subst.
    simpl. auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H.
    repeat rewrite fold_left_app in *.
    exploit IHn;eauto. intros.    
    simpl. rewrite H.
    destruct fold_left. destruct p0. destruct p0.
    rewrite <- H.
    unfold acc_data.

    destruct l0;auto.
    destr. destr.
    rewrite MATCHGE.
    destr.
Qed.

Section WITH_INSTR_SIZE.
  Variable instr_size: instruction -> Z.


Lemma program_equiv_init_mem: forall p1 p2 m,
    program_equiv p1 p2 ->
    init_mem instr_size p1 = Some m ->
    init_mem instr_size p2 = Some m.
Proof.
  unfold init_mem.
  intros. destr_in H0.
  assert (alloc_sections instr_size
      (RelocProgGlobalenvs.globalenv instr_size p2)
      (prog_reloctables p2)
      (prog_sectable p2) Mem.empty = Some m0).
  { unfold alloc_sections in *.
    rewrite PTree.fold_spec in *.
    assert ((PTree.elements (prog_sectable p1)) = (PTree.elements (prog_sectable p2))).
    { exploit PTree.elements_extensional.
      intros. exploit (@pe_sectable fundef unit);eauto.
      auto. }
    unfold RelocProgram.section in *.
    rewrite H1 in *. clear H1.
    set (l := (PTree.elements (prog_sectable p2))) in *.
    assert (LEN: exists n, length l = n).
    { clear Heqo.
      induction l. exists O. auto.
      destruct IHl.
      exists (S x). simpl. auto. }
    clear H0.
    destruct LEN. generalize H0 Heqo. generalize x l m0.
    clear l H0 Heqo x. clear m0 m.
    induction x;intros.
    - rewrite length_zero_iff_nil in H0. subst.
      simpl in *. auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H0.
      rewrite fold_left_app in *.
      simpl in *.
      unfold alloc_section in Heqo at 1.
      destr_in Heqo.
      exploit IHx;eauto.
      intros. rewrite H0.
      simpl.
      exploit (@pe_reloctable_map fundef unit);eauto.
      intros. repeat rewrite H1 in *.
      (* program_equiv and globalenv  *)

      clear H1 H0.
      destr.
      + destruct (Mem.alloc_glob).
        destr.

        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto.
      + destruct (Mem.alloc_glob).
        destr.
        
        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto. }
  rewrite H1.
  clear H1 Heqo.
  unfold alloc_external_symbols in *.
  rewrite PTree.fold_spec in *.
  rewrite <- H0. f_equal.
  symmetry.
  eapply PTree.elements_extensional.
  eapply pe_symbtable. eauto.
Qed.



Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: elf_file.
Hypothesis TRANSF: match_prog prog tprog.


Let ge := RelocProgSemantics2.globalenv instr_size  prog.
Let tge := globalenv instr_size  tprog.

Lemma transf_initial_state: forall st1 rs,
    RelocProgSemantics2.initial_state instr_size  prog rs st1 ->
    exists st2, initial_state instr_size  tprog rs st2 /\ st1 = st2.
  intros st1 rs S1.
  exists st1. split;auto.
  unfold match_prog in TRANSF.
  exploit gen_reloc_elf_correct;eauto.
  eapply decode_encode_reloctable_correct.
  intros (prog' & D1 & E1).  
  econstructor. eapply D1.
  inv S1.

  (* decode_prog_code_section equiv *)
  exploit decode_prog_code_section_correct;eauto.
  intros (p2' & D2 & E2). econstructor.
  eapply D2.

  (* init_mem equal *)
  exploit program_equiv_init_mem;eauto.

  (* initial_state_gen *)
  exploit initial_state_gen_match;eauto.
  intros (st' & GEN & EQ);subst;eauto.
Qed.


Theorem transf_program_correct: forall rs,
    forward_simulation (RelocProgSemantics2.semantics instr_size  prog rs) (semantics instr_size  tprog rs).
Proof.
  intros.
  unfold match_prog in TRANSF.
  exploit gen_reloc_elf_correct;eauto.
  eapply decode_encode_reloctable_correct.
  intros (p' & D1 & E1).
  
  eapply forward_simulation_step with (match_states:= fun (st1 st2: Asm.state) => st1 = st2).
  - simpl. unfold globalenv.
    unfold RelocProgSemantics2.globalenv.
    rewrite D1.
    destr.
    apply program_equiv_sym in E1.
    eapply decode_prog_code_section_correct in Heqr.
    destruct Heqr as (p2' & D2 & E2).
    rewrite D2.
    simpl. erewrite pe_prog_senv;eauto.
    auto.
    destr.
    eapply decode_prog_code_section_correct in Heqr0.
    destruct Heqr0 as (p2' & D2 & E2). rewrite Heqr in D2.
    congruence.
    auto. simpl. erewrite pe_prog_senv;eauto.
    apply program_equiv_sym. auto.
    
  - intros. 
    eapply transf_initial_state. auto.
  - simpl. intros. subst. auto.
  - intros. subst. exists s1'. split;auto.
    eapply step_simulation;eauto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.

Axiom Instance relocelfgen_transflink:
  TransfLink match_prog.
