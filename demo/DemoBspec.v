Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.

Require Import SymbolTable DemoB.

(*
  The specification of DemoB.prog in lts li_C -> li_C
 *)

Definition skel0 := erase_program DemoB.prog.

Inductive state: Type :=
| Callstate
    (i: int)
    (m: mem)
| Interstate
    (i: int)
    (m: mem)
| Returnstate
    (s: int)
    (m: mem).

Definition get_mem (st: state): mem :=
  match st with
  | Callstate _ m => m
  | Interstate _ m => m
  | Returnstate _ m => m
  end.

Section WITH_SE.
  Context (se: Genv.symtbl).

Inductive initial_state : query li_c -> state -> Prop :=
| initial_state_intro
    v args m b i
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (VS: args = (Vint i:: nil)):
    initial_state (cq v int_int_sg ((Vint i) :: nil) m) (Callstate i m).

Inductive at_external: state -> query li_c -> Prop :=
| at_external_intro
    g_fptr i m
    (FINDG: Genv.find_symbol se f_id = Some g_fptr) :
    at_external (Interstate i m) (cq (Vptr g_fptr Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    i ti m tm
    (SUM: ti = sum (Int.sub i Int.one)) :
    after_external (Interstate i m) (cr (Vint ti) tm) (Returnstate (sum i) tm).

Inductive step : state -> trace -> state -> Prop :=
| step_sum
    i m :
    step (Callstate i m) E0 (Returnstate (sum i) m)
| step_call
    i m
    (NZERO: i.(Int.intval) <> 0%Z) :
    step (Callstate i m) E0 (Interstate i m).

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m :
      final_state (Returnstate s m) (cr (Vint s) m).

(* no actual program context, donot need to check available internal function implementation*)
Definition valid_query (q : query li_c): bool := true.

(*  match Genv.find_symbol se g_id with
    |Some b =>
       match (cq_vf q) with
         |Vptr b' Ptrofs => eq_block b b'
         |_ => false
       end
    |None => false
  end.*)

Program Definition lts_Bspec :=
  {|
  Smallstep.step ge := step;
  Smallstep.valid_query := valid_query;
  Smallstep.initial_state := initial_state;
  Smallstep.at_external := at_external;
  Smallstep.after_external := after_external;
  Smallstep.final_state := final_state;
  globalenv := tt;
  |}.

End WITH_SE.

Program Definition Bspec : Smallstep.semantics li_c li_c :=
  {|
   Smallstep.skel := skel0;
   Smallstep.state := state;
   Smallstep.activate := lts_Bspec
   |}.


