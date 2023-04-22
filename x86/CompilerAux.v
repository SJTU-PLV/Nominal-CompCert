Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
Require Asm RealAsm.
(** RealAsm passes  *)
(* Require RealAsmgen. *)
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

(** RealAsm Proof *)
(* Require SSAsmproof.
Require RealAsmproof. *)
(* Require PseudoInstructionsproof. *)
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
(*  @@ time "SSAsm" SSAsmproof.transf_program
  @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program instr_size *)
  @@ time "Elimination of pseudo instruction" PseudoInstructions.transf_program
  @@@ time "Expand builtin inline assembly" AsmBuiltinInline.transf_program
  @@@ time "Pad Instructions with struct return" AsmStructRet.transf_program
  @@ time "Generation of the float literal" AsmFloatLiteral.transf_program
  @@ time "Generation of int64 literal" AsmLongInt.transf_program (* enable only in 64bit mode?  *)
  @@@ time "Elimination of other pseudo instructions" AsmPseudoInstr.transf_program
  @@@ time "Make local jumps use offsets instead of labels" Asmlabelgen.transf_program instr_size
  @@ time "Generation of the jump table" Jumptablegen.transf_program instr_size.

 (** Verified part from SACompcert *)
(*  Definition targetprinter1 p: res Asm.program :=
  OK p
  @@ time "SSAsm" SSAsmproof.transf_program
  @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program instr_size. *)

Definition match_prog_targetprinter p tp :=
  targetprinter p = OK tp.


Axiom targetprinter_fn_stack_requirements_match: forall p tp,
    match_prog_targetprinter p tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
(* Proof. *)
(*   intros. *)
(*   unfold match_prog_targetprinter in H. unfold targetprinter in H. *)
(*   unfold time in H. *)
(*   simpl in H.  *)
(*   destruct  AsmBuiltinInline.transf_program eqn: T1; simpl in H; try discriminate. *)
(*   destruct  AsmStructRet.transf_program eqn: T2; simpl in H; try discriminate. *)
(*   destruct  AsmPseudoInstr.transf_program eqn: T3; simpl in H; try discriminate. *)
(*   destruct  Asmlabelgen.transf_program eqn: T4; simpl in H; try discriminate. *)
(*   inv H. *)

  
(*   rewrite Pseudo_fn_stack_requirements_match. *)
(*   erewrite (BuiltInline_fn_stack_requirements_match _ _ T1). *)
(*   erewrite (AsmStructret_fn_stack_requirements_match _ _ T2). *)
(*   rewrite Float_fn_stack_requirements_match. *)
(*   rewrite LongInt_fn_stack_requirements_match. *)
(*   erewrite (AsmPseudo_fn_stack_requirements_match _ _ T3). *)
(*   erewrite (Asmlabel_fn_stack_requirements_match _ _ T4). *)
(*   erewrite Jumptable_fn_stack_requirements_match. *)
(*   auto. *)
(* Qed. *)
