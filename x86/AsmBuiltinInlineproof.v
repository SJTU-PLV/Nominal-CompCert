Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import AsmBuiltinInline.
Import ListNotations.
Require AsmFacts.

Definition match_prog (p tp:Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.

Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: Asm.program.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Lemma transf_program_correct:
  forward_simulation (semantics instr_size prog) (semantics instr_size tprog).
Proof.
Admitted.


End PRESERVATION.

End WITH_INSTR_SIZE.
