(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Jul 26th     *)
(* *******************  *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import TranslateInstr RelocProgSemantics2.

Import ListNotations.
Local Open Scope error_monad_scope.
  
Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.

Hypothesis translate_instr_size: forall i e l l',
      translate_instr e i = OK l ->
      Instr_size (l ++ l') = instr_size i.

Definition match_prog (p: program) (tp: program) :=
  transf_program instr_size p = OK tp.

Lemma decode_prog_code_section_total: forall p tp,
    transf_program instr_size p = OK tp ->
    exists tp', decode_prog_code_section instr_size Instr_size tp = OK tp'.
Proof.
Admitted.



Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := RelocProgSemantics.globalenv instr_size prog.
Let tge := globalenv instr_size Instr_size tprog.



Definition match_instr (i1 i2: instruction):=
  forall e l l', translate_instr e i1 = OK l ->
         decode_instr e (l ++ l') = OK (i2,l').


(* instruction map is mostly identical *)
Lemma find_instr_refl: forall b ofs i,
    RelocProgSemantics.Genv.genv_instrs ge b ofs = Some i ->
    exists i1, RelocProgSemantics.Genv.genv_instrs tge b ofs = Some i
          /\ match_instr i i1.
Proof.
  unfold ge,tge. unfold globalenv.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A). rewrite A.
  simpl.
  unfold transf_program in *. monadInv TRANSF.
  unfold transl_sectable in EQ.
  unfold decode_prog_code_section in *.
  monadInv A. simpl in *.
  clear ge tge.
Admitted.


Lemma transf_initial_state:forall st1 rs,
    RelocProgSemantics1.initial_state instr_size prog rs st1 ->
    exists st2, initial_state instr_size Instr_size tprog rs st2 /\ st1 = st2.
  intros st1 rs H.
  inv H. inv H1.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A).
  
  assert (TOPROVE: init_mem instr_size tp' = Some m).
  { unfold RelocProgSemantics.init_mem in H.
    unfold init_mem.
    simpl in H. destr_in H.
    assert (alloc_sections (RelocProgSemantics.globalenv instr_size tp')
      (prog_symbtable tp') (prog_reloctables tp') 
      (prog_sectable tp') Mem.empty = Some m0).
    (* ge relation *)
    unfold decode_prog_code_section in A.
    monadInv A. simpl.
    unfold transf_program in TRANSF. monadInv TRANSF.
    unfold transl_sectable in  EQ0. simpl in *.
    exploit PTree_fold_elements. apply EQ. intros F1. clear EQ.
    exploit PTree_fold_elements. apply EQ0. intros F2. clear EQ0.
    
Admitted.

