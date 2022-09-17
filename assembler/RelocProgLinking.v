Require Import Coqlib Integers Values Maps AST.
Require Import RelocProg.
Require Import Linking Errors.
Import ListNotations.

Local Open Scope list_scope.

Definition link_reloc_prog (F V I D: Type) (p1 p2: program F V I D) : option (program F V I D) := None.

Program Instance Linker_reloc_prog (F V I D : Type) : Linker (program F V I D) :=
{
  link := (link_reloc_prog F V I D);
  linkorder := fun _ _ => True;
}.

