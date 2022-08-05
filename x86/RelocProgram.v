(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 13, 2019 *)
(* Last updated:  Feb 27, 2022 by Jinhua Wu*)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs Asm RelocProg.
Require Import Errors.
Local Open Scope error_monad_scope.

Definition section := RelocProg.section instruction init_data.

Definition sectable := RelocProg.sectable instruction init_data.


Definition sec_size (instr_size: instruction -> Z) (s: section) : Z :=
  match s with
  | sec_text c => code_size instr_size c
  | sec_rwdata d => AST.init_data_list_size d
  | sec_rodata d => AST.init_data_list_size d
  end.

Definition sections_size instr_size stbl :=
  fold_left (fun sz sec => sz + (sec_size instr_size sec)) stbl 0.

Definition program := RelocProg.program fundef unit instruction init_data.

