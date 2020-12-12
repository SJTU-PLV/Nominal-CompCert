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

(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import AST Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL Conventions.

(** * Abstract syntax *)

Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> Z -> typ -> mreg -> instruction
  | Lsetstack: mreg -> slot -> Z -> typ -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Ltailcall: signature -> mreg + ident -> instruction
  | Lbuiltin: external_function -> list (builtin_arg loc) -> builtin_res mreg -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Ljumptable: mreg -> list label -> instruction
  | Lreturn: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Section RELSEM.

Variable ge: genv.

Definition ros_address (ros: mreg + ident) (rs: locset) : val :=
  match ros with
  | inl r => rs (R r)
  | inr symb => Genv.symbol_address ge symb Ptrofs.zero
  end.

(** Linear execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (rs: locset)          (**r location state in calling function *)
             (c: code),            (**r program point in calling function *)
      stackframe
  | Stackbase:
      forall (ls: locset),         (**r incoming location state *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (vf: val)                (**r function to call *)
             (rs: locset)             (**r location state at point of call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset)             (**r location state at point of return *)
             (m: mem),                (**r memory state *)
      state.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)
Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init Vundef
  | Stackframe f sp ls c :: stack' => ls
  | Stackbase ls :: stack' => ls
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lop:
      forall s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m')
  | exec_Lcall:
      forall s f sp sig ros b rs m f',
      let vf := ros_address ros rs in
      Genv.find_funct ge vf = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) vf rs m)
  | exec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m',
      let vf := ros_address ros rs' in
      rs' = return_regs (parent_locset s) rs ->
      Genv.find_funct ge vf = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s vf rs' m')
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Lbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lreturn:
      forall s f stk b rs m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m')
  | exec_function_internal:
      forall s vf f rs m rs' m' stk,
      forall FIND: Genv.find_funct ge vf = Some (Internal f),
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s vf rs m)
        E0 (State s f (Vptr stk Ptrofs.zero) f.(fn_code) rs' m')
  | exec_function_external:
      forall s vf ef args res rs1 rs2 m t m',
      forall FIND: Genv.find_funct ge vf = Some (External ef),
      args = map (fun p => Locmap.getpair p rs1) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs2 = Locmap.setpair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs1) ->
      step (Callstate s vf rs1 m)
         t (Returnstate s rs2 m')
  | exec_return:
      forall s f sp rs0 c rs m,
      step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

Inductive initial_state (ge: genv): locset_query -> state -> Prop :=
  | initial_state_intro: forall vf f rs m,
      Genv.find_funct ge vf = Some (Internal f) ->
      let rs0 := initial_regs (fn_sig f) rs in
      initial_state ge
        (lq vf (fn_sig f) rs m)
        (Callstate (Stackbase rs0 :: nil) vf rs0 m).

Inductive at_external (ge: genv): state -> locset_query -> Prop :=
  | at_external_intro vf name sg s rs m:
      Genv.find_funct ge vf = Some (External (EF_external name sg)) ->
      at_external ge
        (Callstate s vf rs m)
        (lq vf sg rs m).

Inductive after_external (ge: genv): state -> locset_reply -> state -> Prop :=
  | after_external_intro vf name sg s rs m rs' m':
      Genv.find_funct ge vf = Some (External (EF_external name sg)) ->
      after_external ge
        (Callstate s vf rs m)
        (lr rs' m')
        (Returnstate s (result_regs sg rs rs') m').

Inductive final_state: state -> locset_reply -> Prop :=
  | final_state_intro: forall rs s rs' m',
      final_state
        (Returnstate (Stackbase rs :: s) rs' m')
        (lr rs' m').

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external after_external (fun _ => final_state) (@Genv.globalenv _ _) p.
