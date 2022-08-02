Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Linking Errors.
Require Import EncDecRet RelocElf.
Require Import RelocElfgen RelocProgSemantics2.

Import ListNotations.
Local Open Scope error_monad_scope.

Section WITH_INSTR_SIZE.

  (* it should not be here *)
Variable instr_size : instruction -> Z.

Definition match_prog (p: program) (tp: elf_file) :=
  gen_reloc_elf instr_size p = OK tp.

Lemma transf_program_match:
  forall p tp, gen_reloc_elf instr_size p = OK tp -> match_prog p tp.
Proof.
  intros. red. auto.
Qed.

(*TODO: define the Semantics *)
End WITH_INSTR_SIZE.
