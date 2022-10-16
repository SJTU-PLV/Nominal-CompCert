Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.

Require Import SymbolTable DemoB.

(*
  The specification of DemoB.prog in lts li_C -> li_C
 *)

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

Definition genv := Genv.t fundef unit.

Section WITH_SE.
  Context (se: Genv.symtbl).

Inductive initial_state : query li_c -> state -> Prop :=
| initial_state_intro
    v args m b i
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
(*    (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (VS: args = (Vint i:: nil)):
    initial_state (cq v int_int_sg ((Vint i) :: nil) m) (Callstate i m).

Inductive at_external: state -> query li_c -> Prop :=
| at_external_intro
    g_fptr i m
    (FINDG: Genv.find_symbol se f_id = Some g_fptr) :
    at_external (Interstate i m) (cq (Vptr g_fptr Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    i ti m m' m'' m''' b_mem
(*    (SUM: ti = sum (Int.sub i Int.one)) : *)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem Ptrofs.zero) (Vint i) = Some m'')
    (STORE0: Mem.storev Mint32 m'' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'''):
    after_external (Interstate i m) (cr (Vint ti) m') (Returnstate (Int.add ti i) m''').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstate i m) E0 (Returnstate (Int.zero) m)
| step_read
    i b_mem m ti
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
      step (Callstate i m) E0 (Returnstate ti m)
| step_call
    i m i' b_mem
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i'):
    step (Callstate i m) E0 (Interstate i m).

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m :
      final_state (Returnstate s m) (cr (Vint s) m).

End WITH_SE.
(*
Section WITH_SE.
  Context (ge: genv).

Inductive initial_state : query li_c -> state -> Prop :=
| initial_state_intro
    args m i gb
    (SYMB: Genv.symbol_address ge g_id Ptrofs.zero = Vptr gb Ptrofs.zero)
(*    (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (VS: args = (Vint i:: nil)):
    initial_state (cq (Vptr gb Ptrofs.zero) int_int_sg ((Vint i) :: nil) m) (Callstate i m).

Inductive at_external: state -> query li_c -> Prop :=
| at_external_intro
    fb i m
    (FINDG: Genv.symbol_address ge f_id Ptrofs.zero = Vptr fb Ptrofs.zero):
    at_external (Interstate i m) (cq (Vptr fb Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    i ti m m' m'' m''' b_mem
(*    (SUM: ti = sum (Int.sub i Int.one)) : *)
    (FINDM: Genv.symbol_address ge _memoized Ptrofs.zero = Vptr b_mem Ptrofs.zero)
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem Ptrofs.zero) (Vint i) = Some m'')
    (STORE0: Mem.storev Mint32 m'' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'''):
    after_external (Interstate i m) (cr (Vint ti) m') (Returnstate (Int.add ti i) m''').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstate i m) E0 (Returnstate (Int.zero) m)
| step_read
    i b_mem m ti
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.symbol_address ge _memoized Ptrofs.zero= Vptr b_mem Ptrofs.zero)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
      step (Callstate i m) E0 (Returnstate ti m)
| step_call
    i m i' b_mem
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.symbol_address ge _memoized Ptrofs.zero = Vptr b_mem Ptrofs.zero)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i'):
    step (Callstate i m) E0 (Interstate i m).

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m :
      final_state (Returnstate s m) (cr (Vint s) m).


Definition valid_query (q : query li_c): bool := Genv.is_internal ge (cq_vf q).

(*  match Genv.find_symbol se g_id with
    |Some b =>
       match (cq_vf q) with
         |Vptr b' Ptrofs => eq_block b b'
         |_ => false
       end
    |None => false
  end.*)

End WITH_SE.
*)
(*
Program Definition lts_Bspec :=
  {|
  Smallstep.step ge := step;
  Smallstep.valid_query := valid_query;
  Smallstep.initial_state := initial_state;
  Smallstep.at_external := at_external;
  Smallstep.after_external := after_external;
  Smallstep.final_state := final_state;
  globalenv := Genv.globalenv se DemoB.prog;
  |}.

End WITH_SE.

*)
Program Definition Bspec : Smallstep.semantics li_c li_c :=
  {|
   Smallstep.skel := erase_program DemoB.prog;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se DemoB.prog in
     {|
       Smallstep.step ge := step ge;
       Smallstep.valid_query q := Genv.is_internal ge (cq_vf q);
       Smallstep.initial_state := initial_state ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external ge;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
   |}.


