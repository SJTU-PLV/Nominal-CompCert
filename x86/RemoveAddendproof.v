Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Linking Errors.
Require Import EncDecRet.
Require Import RemoveAddend RelocProgSemantics2.

Import ListNotations.
Local Open Scope error_monad_scope.

Definition match_prog (p tp: program) :=
  transf_program p = tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. red. auto.
Qed.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.
Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Let ge := globalenv instr_size Instr_size prog.
Let tge := globalenv instr_size Instr_size tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma transf_program_correct:
  forall rs, forward_simulation (semantics instr_size Instr_size prog rs) (semantics instr_size Instr_size  tprog rs).
Proof.
Admitted.


End PRESERVATION.

End WITH_INSTR_SIZE.
