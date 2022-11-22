Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
Require Asm.
(** RealAsm passed. *)
(* Require RealAsmgen. *)
Require PseudoInstructions.
Require AsmBuiltinInline.
(* Require AsmStructRet. *)
(* Require AsmFloatLiteral. *)
Require AsmLiteral.
Require AsmPseudoInstr.
Require Asmlabelgen.
Require Jumptablegen.
(** Assembler passes *)
Require Symbtablegen.
Require Reloctablesgen.
Require RelocBingen.
(* Require AsmLongInt. *)
(* Require MergeSection. *)
(* ELF generation *)
Require RelocElfgen.
Require EncodeRelocElf.


(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.


Section INSTR_SIZE.

  Variable instr_size : Asm.instruction -> Z.
  
  (** TargetPrinter *)
Definition targetprinter p: res Asm.program :=
  OK p
  (* @@ time "SSAsm" SSAsmproof.transf_program *)
  (* @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program instr_size *)
  @@ time "Elimination of pseudo instruction" PseudoInstructions.transf_program
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

 
 (** Assembler *)
 Definition assembler (p: Asm.program) :=
  OK p
  @@@ time "Generation of symbol table" Symbtablegen.transf_program instr_size
  @@@ time "Generation of relocation table" Reloctablesgen.transf_program instr_size
  @@@ time "Encoding of instructions and data" RelocBingen.transf_program
  (* @@@ time "Merge Sections" MergeSection.transf_program *)
  @@@ time "Generation of the reloctable Elf" RelocElfgen.gen_reloc_elf
  @@@ time "Encoding of the reloctable Elf" EncodeRelocElf.encode_elf_file.

 (* without target printet, used to prove top theorem *)
 (* Definition transf_c_program_assembler1 (p: Csyntax.program) := *)
 (*  transf_c_program_real1 p *)
 (*  @@@ time "Generation of symbol table" Symbtablegen.transf_program instr_size *)
 (*  @@@ time "Generation of relocation table" Reloctablesgen.transf_program instr_size *)
 (*  @@@ time "Encoding of instructions and data" RelocBingen.transf_program *)
 (*  (* @@@ time "Merge Sections" MergeSection.transf_program *) *)
 (*  @@@ time "Generation of the reloctable Elf" RelocElfgen.gen_reloc_elf *)
 (*  @@@ time "Encoding of the reloctable Elf" EncodeRelocElf.encode_elf_file. *)
End INSTR_SIZE.
