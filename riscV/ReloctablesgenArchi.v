Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** ** Translation of instructions *)

Definition instr_reloc_offset (i: instruction) : option Z :=
  match i with
  | Plb    _ _ (Ofslow _ _) 
  | Plbu   _ _ (Ofslow _ _) 
  | Plh    _ _ (Ofslow _ _) 
  | Plhu   _ _ (Ofslow _ _) 
  | Plw    _ _ (Ofslow _ _) 
  | Plw_a  _ _ (Ofslow _ _) 
  | Pld    _ _ (Ofslow _ _) 
  | Pld_a  _ _ (Ofslow _ _) 
  | Psb    _ _ (Ofslow _ _) 
  | Psh    _ _ (Ofslow _ _) 
  | Psw    _ _ (Ofslow _ _) 
  | Psw_a  _ _ (Ofslow _ _) 
  | Psd    _ _ (Ofslow _ _) 
  | Psd_a  _ _ (Ofslow _ _) =>
      

