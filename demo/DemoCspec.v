Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.
Require Import Demo.

(** * C-level Abstract Specification for M_C *)

Inductive state: Type :=
| Callstatef
    (ai: int)
    (m: mem)
| Callstateg
    (vf: val)
    (aif: int)
    (m: mem)
| Returnstateg
    (aif: int)
    (rig: int)
    (m: mem)
| Returnstatef
    (ri: int)
    (m: mem).

Definition genv := Genv.t Clight.fundef Ctypes.type.

Section WITH_SE.
  Context (se: Genv.symtbl).
  
Inductive initial_state (ge:genv) : query li_c -> state -> Prop :=
| initial_state_intro
    v m i
    (FIND: Genv.find_funct ge v = Some (Ctypes.Internal func_f)):
    initial_state ge (cq v int_int_sg ((Vint i) :: nil) m) (Callstatef i m).

Inductive at_external (ge:genv): state -> query li_c -> Prop :=
| at_external_intro
    aif m vf id
    (FIND: Genv.find_funct ge vf = Some (Ctypes.External (EF_external id int_int_sg) (Tcons tint Tnil) tint cc_default)):
    at_external ge (Callstateg vf aif m) (cq vf int_int_sg ((Vint (Int.sub aif Int.one)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    aif ti m m' vf:
    after_external (Callstateg vf aif m) (cr (Vint ti) m') (Returnstateg aif ti m').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstatef i m) E0 (Returnstatef (Int.zero) m)
| step_sum_nz
    i sum b_mem m
    (NZERO: i.(Int.intval) <> 0%Z)
    (SUMNZERO: sum.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int i)) ) = Some (Vint sum)):
      step (Callstatef i m) E0 (Returnstatef sum m)
| step_call
    i m sum b_mem vg
    (NZERO: i.(Int.intval) <> 0%Z)
    (SUMZERO: sum.(Int.intval) = 0%Z)
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int i))) = Some (Vint sum))
    (FINDF: Genv.symbol_address se g_id Ptrofs.zero = vg)
    (VG: vg <> Vundef):
    step (Callstatef i m) E0 (Callstateg vg i m)
| step_return
    b_mem m m' sum sum' i
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE: Mem.storev Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int i))) (Vint sum') = Some m')
    (SUM: sum' = Int.add sum i):
    step (Returnstateg i sum m) E0 (Returnstatef sum' m').

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m:
      final_state (Returnstatef s m) (cr (Vint s) m).

End WITH_SE.

Definition L_C : Smallstep.semantics li_c li_c :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv M_C.
