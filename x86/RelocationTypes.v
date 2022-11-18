Require Import Coqlib Maps Values AST.

(* Part of relocation types for x86 *)

Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.

Definition encode_reloctype (t:reloctype) :=
  match t with
  | reloc_null => 0     (* R_386_NONE *)
  | reloc_abs  => 1     (* R_386_32, addend 64bit in 64bit mode*)
  | reloc_rel  => 2     (* R_386_PC32 in 32bit and R_X86_64_PC32 in 64bit mode*)
  end.
