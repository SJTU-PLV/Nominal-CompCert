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
| Callstateg
    (ai: int)
    (m: mem)
| Callstatef
    (vf: val)
    (aif: int)
    (m: mem)
| Returnstatef
    (aif: int)
    (rig: int)
    (m: mem)
| Returnstateg
    (ri: int)
    (m: mem).

Definition genv := Genv.t fundef unit.

Section WITH_SE.
  Context (se: Genv.symtbl).
  
Inductive initial_state (ge:genv) : query li_c -> state -> Prop :=
| initial_state_intro
    v args m i
(*    (SYMB: Genv.symbol_address se g_id Ptrofs.zero = v)
    (FPTR: v = Vptr b Ptrofs.zero)
*)
    (FIND: Genv.find_funct ge v = Some (Internal func_g))
    (VS: args = (Vint i:: nil)):
    initial_state ge (cq v int_int_sg ((Vint i) :: nil) m) (Callstateg i m).

Inductive at_external (ge:genv): state -> query li_c -> Prop :=
| at_external_intro
    aif m vf id
    (FIND: Genv.find_funct ge vf = Some (External (EF_external id int_int_sg))):
    at_external ge (Callstatef vf aif m) (cq vf int_int_sg ((Vint (Int.sub aif Int.one)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    aif ti m m' vf:
    after_external (Callstatef vf aif m) (cr (Vint ti) m') (Returnstatef aif ti m').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstateg i m) E0 (Returnstateg (Int.zero) m)
| step_read
    i b_mem m ti i'
    (NZERO: i.(Int.intval) <> 0%Z)
    (EQ: i.(Int.intval) = i'.(Int.intval))
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
      step (Callstateg i m) E0 (Returnstateg ti m)
| step_call
    i m i' b_mem vf
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (FINDF: Genv.symbol_address se f_id Ptrofs.zero = vf)
    (VF: vf <> Vundef)
    (NEQ: i.(Int.intval) <> i'.(Int.intval)):
    step (Callstateg i m) E0 (Callstatef vf i m)
| step_return
    b_mem m m' m'' ti i
    (FINDM: Genv.symbol_address se _memoized Ptrofs.zero  = Vptr b_mem Ptrofs.zero)
    (STORE0: Mem.storev Mint32 m (Vptr b_mem Ptrofs.zero) (Vint i) = Some m')
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m''):
    step (Returnstatef i ti m) E0 (Returnstateg (Int.add ti i) m'').

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m:
      final_state (Returnstateg s m) (cr (Vint s) m).

End WITH_SE.

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
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
   |}.


