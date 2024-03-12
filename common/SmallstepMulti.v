Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Require Import SmallstepClosed.
Import Values Maps Memory AST.

Section MultiThread.

  Context {liA liB : language_interface}.

  Context {OS : semantics liA liB}.

  Definition local_state := state OS.

  Variable initial_query : query liB.

  
  (* The global state of concurrent semantics *)

  (* problem : how to deal with "thread variable" *)

  Definition state := list local_state.

  Closed.semantics
  (** Initial state of Concurrent semantics *)

  (* We need a "query" to the main function of the semantics *)
  (* Including the initial global memory*)


  

  
