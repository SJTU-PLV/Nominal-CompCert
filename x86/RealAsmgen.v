(** Translation from RawAsm to RealAsm *)

Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Mach Asm RealAsm.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Section INSTRSIZE.
Variable instr_size : instruction -> Z.

Definition transf_function (f: Asm.function) : res Asm.function :=
  if wf_asm_function_check instr_size f then
    OK f
  else
    Error (msg "asm_function_is_not_wellformed").

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

End INSTRSIZE.
