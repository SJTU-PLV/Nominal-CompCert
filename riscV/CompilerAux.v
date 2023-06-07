Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep Compiler0.
Require Asm.
(** RealAsm passed. *)
(* Require RealAsmgen. *)
Require PseudoInstructions.
Require AsmFixupcode.
Require AsmBuiltinInline.
(* Require AsmStructRet. *)
(* Require AsmFloatLiteral. *)
Require AsmLiteral.
Require AsmPseudoInstr.
Require Asmlabelgen.
Require Jumptablegen.
(** Assembler passes *)
Require Symbtablegen.
Require Reloctablesgen ReloctablesgenproofArchi.
Require RelocBingen.
(* Require AsmLongInt. *)
(* Require MergeSection. *)
(* ELF generation *)
Require RelocElfgen.
Require EncodeRelocElf.

Definition instr_size := Asm.instr_size_real.
Definition instr_size_bound := Asm.instr_size_bound_real.

Lemma instr_eq_size: forall i1 i2,
    ReloctablesgenproofArchi.instr_eq i1 i2 -> instr_size i1 = instr_size i2.
Proof.
  intros. unfold ReloctablesgenproofArchi.instr_eq in H.
  subst. auto.
Qed.

  (** TargetPrinter *)
Definition targetprinter p: res Asm.program :=
  OK p
  @@ time "Elimination of pseudo instruction" PseudoInstructions.transf_program
  @@ time "Adjustment of float point arguments passing by fix-up code" AsmFixupcode.transf_program
  @@@ time "Expand builtin inline assembly" AsmBuiltinInline.transf_program
  @@ time "Generation of the literal" AsmLiteral.transf_program
  @@ time "Elimination of other pseudo instructions" AsmPseudoInstr.transf_program
  @@@ time "Make local jumps use offsets instead of labels" Asmlabelgen.transf_program instr_size
  @@ time "Generation of the jump table" Jumptablegen.transf_program instr_size.

Definition match_prog_targetprinter p tp :=
  targetprinter p = OK tp.

(* This should be an Axiom *)
Axiom targetprinter_fn_stack_requirements_match: forall p tp,
    match_prog_targetprinter p tp ->
    fn_stack_requirements p = fn_stack_requirements tp.

