Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import AsmLongInt.
Import ListNotations.
Require AsmFacts.

Definition match_prog (p tp:Asm.program) :=
  exists tp',
    transf_program p = tp' /\
    (* add defs *)
    prog_public tp = prog_public tp' /\
    prog_main tp = prog_main tp'.
    
Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  unfold match_prog. intros. exists tp; intuition.
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