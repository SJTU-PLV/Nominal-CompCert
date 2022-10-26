Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler CA.

Require Import CKLRAlgebra Extends Inject InjectFootprint.

Search wt_c.

Module C_injp.

Inductive state: Type :=
| Callstateg
    (ai: int)
    (m: mem)
| Callstatef
    (sp: val)
    (aif: int)
    (m: mem)
| Returnstatef
    (sp: val)
    (aif: int)
    (rig: int)
    (m: mem)
| Returnstateg
    (ri: int)
    (m: mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

Inductive initial_state : query li_c -> state -> Prop :=
| initial_state_intro
    v args m b i
    (SYMB: Genv.symbol_address se g_id Ptrofs.zero = v)
    (FPTR: v = Vptr b Ptrofs.zero)
(*    (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (VS: args = (Vint i:: nil)):
    initial_state (cq v int_int_sg ((Vint i) :: nil) m) (Callstateg i m).

Inductive at_external: state -> query li_c -> Prop :=
| at_external_intro
    g_fptr aif m sp
    (VALID: valid_blockv (Mem.support m) sp)
    (FINDG: Genv.symbol_address se f_id Ptrofs.zero = Vptr g_fptr Ptrofs.zero):
    at_external (Callstatef sp aif m)
                (cq (Vptr g_fptr Ptrofs.zero) int_int_sg ((Vint (Int.sub aif Int.one)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    aif ti m m' sp
    (UNCHANGE: Mem.unchanged_on (fun b _  => sp = Vptr b Ptrofs.zero) m m'):
    after_external (Callstatef sp aif m) (cr (Vint ti) m') (Returnstatef sp aif ti m').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstateg i m) E0 (Returnstateg (Int.zero) m)
| step_read
    i b_mem m ti
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.symbol_address se _memoized (Ptrofs.repr 4) = Vptr b_mem (Ptrofs.repr 4))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
      step (Callstateg i m) E0 (Returnstateg ti m)
| step_call
    i m i' b_mem m' sb
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.symbol_address se _memoized Ptrofs.zero= Vptr b_mem Ptrofs.zero)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i')
    (ALLOC: Mem.alloc m 0 24 = (m',sb)):
    step (Callstateg i m) E0 (Callstatef (Vptr sb Ptrofs.zero) i m')
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

End C_injp.
Variable Bspec' : Smallstep.semantics li_c li_c.

Axiom injp_protection : forward_simulation
                          (cc_c injp) (cc_c injp) Bspec Bspec'.

Variable self_wt : forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec' Bspec'.

Axiom CA : forward_simulation (cc_c_asm) (cc_c_asm) Bspec' (Asm.semantics DemoB.prog).


Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply injp_protection.
  eapply compose_forward_simulations.
  eapply self_wt.
  rewrite <- !(cc_compose_assoc) at 1.
  eapply compose_forward_simulations.
  rewrite cc_compose_assoc at 1.
  rewrite cc_compose_assoc at 1.
  rewrite <- cc_ca_cllmma at 1.
  rewrite cc_cllmma_ca.
  eapply CA.
  eapply semantics_asm_rel; eauto.
Qed.
