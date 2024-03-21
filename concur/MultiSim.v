Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import CMulti AsmMulti.
Require Import CA Compiler.

Section ConcurSim.

  (** Hypothesis *)
  Variable OpenC : semantics li_c li_c.

  Variable OpenA : semantics li_asm li_asm.

  Hypothesis OpenSim : forward_simulation cc_c_asm_injp cc_c_asm_injp OpenC OpenA.

  (** * Get the concurrent semantics *)
  
  (** In order to construct a concurrent semantics from open semantics, we need to provide :
      (1) the query to its main function, including initial memory
      (2) A relation for the final state as the return state of main function, with a integer as return value
      (3) A symtbl table
      (4) A yield strategy for chosing target thread
   *)

  (** We start from symboltbl *)

  Definition se := Genv.symboltbl (skel OpenC).
  Definition LTSC := activate OpenC se.
  Definition ge := Smallstep.globalenv LTSC.

  Definition main_id := prog_main (skel OpenC).

  (** * Hypothesis1 about OpenC: it contains a main function *)
  Variable main_b : block.
  Hypothesis find_main : Genv.find_symbol se main_id = Some main_b.

  Variable m0 : mem.
  Hypothesis init_mem : Genv.init_mem (skel OpenC) = Some m0.
  Definition main_sig := AST.mksignature nil (AST.Tret AST.Tint) AST.cc_default.
  Definition main_vf := Vptr main_b Ptrofs.zero.
  Definition main_qc := cq main_vf main_sig nil m0.

  Inductive main_reply : int -> c_reply -> Prop :=
  |reply_int : forall r m, main_reply r (cr (Vint r) m).

  (*Variable yield_s : (state -> nat) 
  Definition ConcurC := Concur_sem *)
    
  Theorem
