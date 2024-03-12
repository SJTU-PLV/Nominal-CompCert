Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Import Values Maps Memory AST.

Section MultiThread.

  Context {liA liB : language_interface}.

  Context {OS : semantics liA liB}.

  Definition state := state OS.

  (* The global state of concurrent semantics *)

  
