(* *******************  *)
(* Author: Pierre Wilke  *)
(* Date:   Jun 24, 2020 *)
(* *******************  *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SymbolString.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Definition remove_addend_relocentry (re: relocentry) : relocentry :=
  {|
    reloc_offset := reloc_offset re;
    reloc_type := reloc_type re;
    reloc_symb := reloc_symb re;
    reloc_addend := 0;
  |}.

Definition remove_addend_reloctable rtbl :=
  List.map remove_addend_relocentry rtbl.

Definition remove_addend_reloctable_map (rtblmap: reloctable_map) :=
  PTree.map1 remove_addend_reloctable rtblmap.

Definition transf_program (p: program) : program :=
  {| prog_defs := p.(prog_defs);
     prog_public := p.(prog_public);
     prog_main := p.(prog_main);
     prog_sectable := prog_sectable p;
     prog_symbtable := p.(prog_symbtable);
     prog_reloctables := remove_addend_reloctable_map (prog_reloctables p);
     prog_senv := p.(prog_senv);
  |}.
