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
Admitted.


  (** TargetPrinter *)
Definition targetprinter p: res Asm.program :=
  OK p
  (* @@ time "SSAsm" SSAsmproof.transf_program *)
  (* @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program instr_size *)
  @@ time "Elimination of pseudo instruction" PseudoInstructions.transf_program
  @@ time "Adjustment of float point arguments passing by fix-up code" AsmFixupcode.transf_program
  @@@ time "Expand builtin inline assembly" AsmBuiltinInline.transf_program
  (* @@@ time "Pad Instructions with struct return" AsmStructRet.transf_program *)
  (* @@ time "Generation of the float literal" AsmFloatLiteral.transf_program *)
  (* @@ time "Generation of int64 literal" AsmLongInt.transf_program (* enable only in 64bit mode?  *) *)
  @@ time "Generation of the literal" AsmLiteral.transf_program
  @@ time "Elimination of other pseudo instructions" AsmPseudoInstr.transf_program
  @@@ time "Make local jumps use offsets instead of labels" Asmlabelgen.transf_program instr_size
  @@ time "Generation of the jump table" Jumptablegen.transf_program instr_size.

 (* verified part from SACompcert *)
  (* Definition transf_c_program_real1 p: res Asm.program := *)
  (* transf_c_program p *)
  (* @@ time "SSAsm" SSAsmproof.transf_program *)
  (* @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program instr_size. *)



 (* without target printet, used to prove top theorem *)
 (* Definition transf_c_program_assembler1 (p: Csyntax.program) := *)
 (*  transf_c_program_real1 p *)
 (*  @@@ time "Generation of symbol table" Symbtablegen.transf_program instr_size *)
 (*  @@@ time "Generation of relocation table" Reloctablesgen.transf_program instr_size *)
 (*  @@@ time "Encoding of instructions and data" RelocBingen.transf_program *)
 (*  (* @@@ time "Merge Sections" MergeSection.transf_program *) *)
 (*  @@@ time "Generation of the reloctable Elf" RelocElfgen.gen_reloc_elf *)
 (*  @@@ time "Encoding of the reloctable Elf" EncodeRelocElf.encode_elf_file. *)

Definition match_prog_targetprinter p tp :=
  targetprinter p = OK tp.


Lemma Pseudo_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (PseudoInstructions.transf_program p).
Admitted.

Lemma Fixup_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmFixupcode.transf_program p).
Admitted.

Lemma BuiltInline_fn_stack_requirements_match: forall p tp,
    AsmBuiltinInline.transf_program p = OK tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
Admitted.

Lemma AsmPseudo_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmPseudoInstr.transf_program p).
Admitted.

Lemma Asmlabel_fn_stack_requirements_match: forall p tp,
    Asmlabelgen.transf_program instr_size p = OK tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
Admitted.  

Lemma AsmLiteral_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmLiteral.transf_program p).
Admitted.

    Lemma Jumptable_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (Jumptablegen.transf_program instr_size p).
Admitted.


Lemma targetprinter_fn_stack_requirements_match: forall p tp,
    match_prog_targetprinter p tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
Proof.
  intros.
  unfold match_prog_targetprinter in H. unfold targetprinter in H.
  unfold time in H.
  simpl in H. 
  destruct  AsmBuiltinInline.transf_program eqn: T1; simpl in H; try discriminate.
  destruct  Asmlabelgen.transf_program eqn: T2; simpl in H; try discriminate.
  inv H.

  rewrite Pseudo_fn_stack_requirements_match.
  rewrite Fixup_fn_stack_requirements_match.
  erewrite (BuiltInline_fn_stack_requirements_match _ _ T1).
  rewrite AsmLiteral_fn_stack_requirements_match.
  rewrite AsmPseudo_fn_stack_requirements_match.
  erewrite (Asmlabel_fn_stack_requirements_match _ _ T2).
  erewrite Jumptable_fn_stack_requirements_match.
  auto.
Qed.

