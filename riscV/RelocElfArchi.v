Require Import Coqlib Integers Maps.
Require Import AST Asm Archi MachineTypes.
Require Import Errors.
Require Import Encode.
Require Import Memdata.
Require Import Hex.
Require Import RelocElf.
Import Hex.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.

(** machine type *)
Definition machine := EM_RISCV.

(* elf flag *)
Definition elf_flag := 4%Z.

(* relocentry size *)
Definition reloc_entry_size := if ptr64 then 24%Z else 12%Z.

Definition rel_eh_type := SHT_RELA.