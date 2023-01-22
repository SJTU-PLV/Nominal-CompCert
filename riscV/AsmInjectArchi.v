(** * Properties about Injections at the Asm Level *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm (* AsmFacts *).
Require Import LocalLib.
Import ListNotations.

(* Injection lemmas dependent to architecture *)
