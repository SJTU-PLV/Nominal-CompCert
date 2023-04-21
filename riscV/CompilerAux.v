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
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
  - eapply Globalenvs.Genv.find_funct_ptr_transf in Heqo.
    erewrite Heqo.
    2: {
      instantiate (1:= PseudoInstructions.transf_fundef).
      unfold PseudoInstructions.transf_program.
      eapply match_transform_program. }
    unfold PseudoInstructions.transf_fundef,PseudoInstructions.transf_function,transf_fundef.
    destruct f. auto. auto.
  - eapply match_program_no_more_functions in Heqo.
    erewrite Heqo. auto.
    eapply match_transform_program.
Qed.

Lemma Fixup_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmFixupcode.transf_program p).
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
  - eapply Globalenvs.Genv.find_funct_ptr_transf in Heqo.
    erewrite Heqo.
    2: {
      instantiate (1:= AsmFixupcode.transf_fundef).
      unfold AsmFixupcode.transf_program.
      eapply match_transform_program. }
    unfold AsmFixupcode.transf_fundef,AsmFixupcode.transf_function,transf_fundef.
    destruct f. auto. auto.
  - eapply match_program_no_more_functions in Heqo.
    erewrite Heqo. auto.
    eapply match_transform_program.
Qed.


Lemma BuiltInline_fn_stack_requirements_match: forall p tp,
    AsmBuiltinInline.transf_program p = OK tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
  - eapply Globalenvs.Genv.find_funct_ptr_transf_partial in Heqo.
    destruct Heqo as (tf & A & B).
    erewrite A.
    2:{
      instantiate (1:= AsmBuiltinInline.transf_fundef).
      eapply match_transform_partial_program.
      unfold AsmBuiltinInline.transf_program in H. auto.
    }
    unfold AsmBuiltinInline.transf_fundef,transf_partial_fundef,AsmBuiltinInline.transf_function,transf_fundef in B.
    destruct f. monadInv B. monadInv EQ. auto. inv B. auto.
  - eapply match_program_no_more_functions in Heqo.
    erewrite Heqo. auto.
    eapply match_transform_partial_program.
    unfold AsmBuiltinInline.transf_program in H. eauto.
Qed.    
    
Lemma AsmPseudo_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmPseudoInstr.transf_program p).
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
  - eapply Globalenvs.Genv.find_funct_ptr_transf in Heqo.
    erewrite Heqo.
    2: {
      instantiate (1:= AsmPseudoInstr.transf_fundef).
      unfold AsmPseudoInstr.transf_program.
      eapply match_transform_program. }
    unfold AsmPseudoInstr.transf_fundef,AsmPseudoInstr.transf_function,transf_fundef.
    destruct f. auto. auto.
  - eapply match_program_no_more_functions in Heqo.
    erewrite Heqo. auto.
    eapply match_transform_program.
Qed.


Lemma Asmlabel_fn_stack_requirements_match: forall p tp,
    Asmlabelgen.transf_program instr_size p = OK tp ->
    fn_stack_requirements p = fn_stack_requirements tp.
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
  - eapply Globalenvs.Genv.find_funct_ptr_transf_partial in Heqo.
    destruct Heqo as (tf & A & B).
    erewrite A.
    2:{
      instantiate (1:= Asmlabelgen.transf_fundef instr_size).
      eapply match_transform_partial_program.
      unfold Asmlabelgen.transf_program in H. auto.
    }
    unfold Asmlabelgen.transf_fundef,transf_partial_fundef,Asmlabelgen.trans_function,transf_fundef in B.
    destruct f. monadInv B. monadInv EQ. auto. inv B. auto.
  - eapply match_program_no_more_functions in Heqo.
    erewrite Heqo. auto.
    eapply match_transform_partial_program.
    unfold Asmlabelgen.transf_program in H. eauto.
Qed.    


Lemma AsmLiteral_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (AsmLiteral.transf_program p).
Proof.
  intros. unfold fn_stack_requirements.  
  eapply Axioms.extensionality. intros.
  destr.
Admitted.

Lemma Jumptable_fn_stack_requirements_match: forall p,
    fn_stack_requirements p = fn_stack_requirements (Jumptablegen.transf_program instr_size p).
Admitted.

(* This should be an Axiom *)
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

