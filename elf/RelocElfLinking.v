Require Import Coqlib Integers Values Maps AST.
Require Import RelocElf.
Require Import Linking Errors.
Import ListNotations.

Local Open Scope list_scope.

Definition link_elf_file (p1 p2: elf_file) : option elf_file := None.

Program Instance Linker_elf_file : Linker elf_file :=
{
  link := link_elf_file;
  linkorder := fun _ _ => True;
}.

