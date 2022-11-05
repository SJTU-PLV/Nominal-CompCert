Require Import Coqlib Maps Values AST.

(* Part of relocation types for x86 *)

Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.
