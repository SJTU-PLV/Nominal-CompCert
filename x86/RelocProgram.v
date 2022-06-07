(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 13, 2019 *)
(* Last updated:  Feb 27, 2022 by Jinhua Wu*)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs Asm RelocProg.

Definition section := @RelocProg.section instruction.

Definition sectable := @RelocProg.sectable instruction.

Definition sec_size (instr_size: instruction -> Z) (s: section) : Z :=
  match s with
  | sec_text c => code_size instr_size c
  | sec_data d => AST.init_data_list_size d
  (* | sec_rodata d => AST.init_data_list_size d *)
  | sec_bytes bs => Z.of_nat (length bs)
  end.

Definition sections_size instr_size stbl :=
  fold_left (fun sz sec => sz + (sec_size instr_size sec)) stbl 0.

Definition program := @RelocProg.program fundef unit instruction.

