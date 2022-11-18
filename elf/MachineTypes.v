(** Machine architecture, support x86-32, x86_64 and RISC-V for now *)

Inductive elf_machine :Type := 
| EM_386
| EM_x86_64
| EM_RISCV.