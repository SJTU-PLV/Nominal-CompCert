Require Import Coqlib Maps Values AST.

(* Part of relocation types for RISCV
   follow https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc *)

Inductive reloctype :=
| R_RISCV_32                    (* data relocation *)
| R_RISCV_64                    (* data relocation *)
| R_RISCV_JAL                   (* 20-bit PC-relative jump offset *)
| R_RISCV_HI20                  (* High 20 bits of 32-bit absolute address, %hi(symbol) *)
| R_RISCV_LO12_I                (* I type: Low 12 bits of 32-bit absolute address, %lo(symbol) *)
| R_RISCV_LO12_S                (* S type: Low 12 bits of 32-bit absolute address, %lo(symbol) *)
.
