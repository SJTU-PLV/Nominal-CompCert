Require Import Coqlib Maps Values AST.

(* Part of relocation types for RISCV
   follow https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc *)

Inductive reloctype :=
| R_RISCV_32                    (* data relocation *)
| R_RISCV_64                    (* data relocation *)
| R_RISCV_CALL                  (* 32-bit PC-relative function call *)
| R_RISCV_JAL                   (* 20-bit PC-relative jump offset *)
| R_RISCV_HI20                  (* High 20 bits of 32-bit absolute address, %hi(symbol) *)
| R_RISCV_PCREL_HI20            (* High 20 bits of 32-bit PC-relative reference, %pcrel_hi(symbol) *)
| R_RISCV_LO12_I                (* I type: Low 12 bits of 32-bit absolute address, %lo(symbol) *)
| R_RISCV_PCREL_LO12_I           (* I type: Low 12 bits of a 32-bit PC-relative, %pcrel_lo(address of %pcrel_hi), the addend must be 0 *)
| R_RISCV_LO12_S                (* S type: Low 12 bits of 32-bit absolute address, %lo(symbol) *)
.

Definition encode_reloctype (t:reloctype) :=
  match t with
   | R_RISCV_32     => 1
   | R_RISCV_64     => 2
   | R_RISCV_JAL    => 17
   | R_RISCV_CALL   => 18
   | R_RISCV_PCREL_HI20 => 23
   | R_RISCV_PCREL_LO12_I => 24
   | R_RISCV_HI20   => 26
   | R_RISCV_LO12_I => 27
   | R_RISCV_LO12_S => 28  
  end.
