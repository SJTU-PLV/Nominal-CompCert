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
Definition machine := if ptr64 then EM_x86_64 else EM_386.

(* elf flag *)
Definition elf_flag := 0%Z.

(* relocentry size *)
Definition reloc_entry_size := if ptr64 then 24 else 8.

Definition rel_eh_type := if Archi.ptr64 then SHT_RELA else SHT_REL.

