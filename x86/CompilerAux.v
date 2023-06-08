Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
Require Asm RealAsm.
(** RealAsm passes  *)
Require PseudoInstructions.
Require AsmBuiltinInline.
Require AsmStructRet.
Require AsmFloatLiteral.
Require AsmLongInt.
Require AsmPseudoInstr.
Require Asmlabelgen.
Require Jumptablegen.
(** Assembler passes *)
Require Symbtablegen.
Require Reloctablesgen.
Require RelocBingen.
(** ELF generation *)
Require RelocElfgen.
Require EncodeRelocElf.

(** Assembler Proof *)
Require Symbtablegenproof.
Require Reloctablesgenproof.
Require RelocBingenproof.
Require RelocElfgenproof.
Require EncodeElfCorrect.
Require RelocProgLinking.
Require ReloctablesgenSize.
Require Import Compiler0.



Definition instr_size := Asm.instr_size_real.
Definition instr_size_bound := Asm.instr_size_bound_real.

Lemma instr_eq_size: forall i1 i2,
    ReloctablesgenproofArchi.instr_eq i1 i2 -> instr_size i1 = instr_size i2.
Proof.
  intros. unfold ReloctablesgenproofArchi.instr_eq in H.
  destruct i1;subst;auto.
  destruct i2;try congruence.
  auto.
Qed.

  (** TargetPrinter *)
Definition targetprinter p: res Asm.program :=
  OK p
  @@ time "Elimination of pseudo instruction" PseudoInstructions.transf_program
  @@@ time "Expand builtin inline assembly" AsmBuiltinInline.transf_program
  @@@ time "Pad Instructions with struct return" AsmStructRet.transf_program
  @@ time "Generation of the float literal" AsmFloatLiteral.transf_program
  @@ time "Generation of int64 literal" AsmLongInt.transf_program (* enable only in 64bit mode?  *)
  @@@ time "Elimination of other pseudo instructions" AsmPseudoInstr.transf_program
  @@@ time "Make local jumps use offsets instead of labels" Asmlabelgen.transf_program instr_size
  @@ time "Generation of the jump table" Jumptablegen.transf_program instr_size.


Definition match_prog_targetprinter p tp :=
  targetprinter p = OK tp.


Axiom targetprinter_fn_stack_requirements_match: forall p tp,
    match_prog_targetprinter p tp ->
    fn_stack_requirements p = fn_stack_requirements tp.

