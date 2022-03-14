(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The RTL intermediate language: abstract syntax and semantics.
  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers RTL.

(** * Abstract syntax *)

(** RTLMach is almost same as RTL, the only difference here is we use
    the memory opration [record_frame_mach] to record new frame instead
    of [record_frame_vm] which is used in all semantics before.
    This new opration calculates only the first framesize of a tailcall
    stage to give the whole stack consumption after a record operation.
    Which is precisely the machine deals with tailcalls.
*)

Section ORACLE.

Variable fn_stack_requirements : ident -> Z.

Section RELSEM.

Variable ge: genv.
(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd id,
      ros_is_ident ros rs id ->
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m id)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m' id m'' m''',
      ros_is_ident ros rs id ->
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Mem.return_frame m' = Some m'' ->
      Mem.pop_stage m'' = Some m''' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Callstate s fd rs##args m''' id)
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m' m'' m''',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Mem.return_frame m' = Some m'' ->
      Mem.pop_stage m'' = Some m''' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) m''')
  | exec_function_internal:
      forall s f args m m' m'' m''' stk id path,
      Mem.alloc_frame m id = (m',path) ->
      Mem.alloc m' 0 f.(fn_stacksize) = (m'', stk) ->
      Mem.record_frame (Mem.push_stage m'')(Memory.mk_frame (fn_stack_requirements id)) = Some m''' ->
      step (Callstate s (Internal f) args m id)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m''')
  | exec_function_external:
      forall s ef args res t m m' sz,
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m sz)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

Lemma exec_Iop':
  forall s f sp pc rs m op args res pc' rs' v,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0 m1 b0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.alloc m0 0 0 = (m1,b0) ->
      initial_state p (Callstate nil f nil m1 (prog_main p)).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state  p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State s0 f sp pc' (regmap_setres res vres2 rs) m2). econstructor; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate s0 vres2 m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

(** * Operations on RTL abstract syntax *)

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)
End ORACLE.
