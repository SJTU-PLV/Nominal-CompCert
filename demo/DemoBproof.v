Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import Compiler.

Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Admitted.
