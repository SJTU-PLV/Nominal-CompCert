(** The Mach intermediate language: abstract semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.

(** This file defines the "abstract" semantics for the Mach
  intermediate language, as opposed to the more concrete
  semantics given in module [Machconcr].

  The only difference with the concrete semantics is the interpretation
  of the stack access instructions [Mgetstack], [Msetstack] and [Mgetparam].
  In the concrete semantics, these are interpreted as memory accesses
  relative to the stack pointer.  In the abstract semantics, these 
  instructions are interpreted as accesses in a frame environment,
  not resident in memory.  The frame environment is an additional
  component of the state.

  Not having the frame data in memory facilitates the proof of
  the [Stacking] pass, which shows that the generated code executes
  correctly with the abstract semantics.
*)

(** * Structure of abstract stack frames *)

(** An abstract stack frame comprises a low bound [fr_low] (the high bound
  is implicitly 0) and a mapping from (type, offset) pairs to values. *)

Record frame : Set := mkframe {
  fr_low: Z;
  fr_contents: typ -> Z -> val
}.

Definition typ_eq: forall (ty1 ty2: typ), {ty1=ty2} + {ty1<>ty2}.
Proof. decide equality. Defined.

Definition update (ty: typ) (ofs: Z) (v: val) (f: frame) : frame :=
  mkframe f.(fr_low)
   (fun ty' ofs' => 
     if zeq ofs ofs' then
       if typ_eq ty ty' then v else Vundef
     else
       if zle (ofs' + AST.typesize ty') ofs then f.(fr_contents) ty' ofs'
       else if zle (ofs + AST.typesize ty) ofs' then f.(fr_contents) ty' ofs'
       else Vundef).

Definition empty_frame := mkframe 0 (fun ty ofs => Vundef).

(** [get_slot fr ty ofs v] holds if the frame [fr] contains value [v]
  with type [ty] at word offset [ofs]. *)

Inductive get_slot: frame -> typ -> Z -> val -> Prop :=
  | get_slot_intro:
      forall fr ty ofs v,
      24 <= ofs ->
      fr.(fr_low) + ofs + AST.typesize ty <= 0 ->
      v = fr.(fr_contents) ty (fr.(fr_low) + ofs) -> 
      get_slot fr ty ofs v.

(** [set_slot fr ty ofs v fr'] holds if frame [fr'] is obtained from
  frame [fr] by storing value [v] with type [ty] at word offset [ofs]. *)

Inductive set_slot: frame -> typ -> Z -> val -> frame -> Prop :=
  | set_slot_intro:
      forall fr ty ofs v fr',
      24 <= ofs ->
      fr.(fr_low) + ofs + AST.typesize ty <= 0 ->
      fr' = update ty (fr.(fr_low) + ofs) v fr ->
      set_slot fr ty ofs v fr'.

Definition init_frame (f: function) :=
  mkframe (- f.(fn_framesize)) (fun ty ofs => Vundef).

(** Extract the values of the arguments of an external call. *)

Inductive extcall_arg: regset -> frame -> loc -> val -> Prop :=
  | extcall_arg_reg: forall rs fr r,
      extcall_arg rs fr (R r) (rs r)
  | extcall_arg_stack: forall rs fr ofs ty v,
      get_slot fr ty (Int.signed (Int.repr (4 * ofs))) v ->
      extcall_arg rs fr (S (Outgoing ofs ty)) v.

Inductive extcall_args: regset -> frame -> list loc -> list val -> Prop :=
  | extcall_args_nil: forall rs fr,
      extcall_args rs fr nil nil
  | extcall_args_cons: forall rs fr l1 ll v1 vl,
      extcall_arg rs fr l1 v1 -> extcall_args rs fr ll vl ->
      extcall_args rs fr (l1 :: ll) (v1 :: vl).

Definition extcall_arguments
   (rs: regset) (fr: frame) (sg: signature) (args: list val) : Prop :=
  extcall_args rs fr (Conventions.loc_arguments sg) args.
    
(** The components of an execution state are:

- [State cs f sp c rs fr m]: [f] is the function currently executing.
  [sp] is the stack pointer.  [c] is the list of instructions that
  remain to be executed.  [rs] assigns values to registers. 
  [fr] is the current frame, as described above.  [m] is the memory state.
- [Callstate cs f rs m]: [f] is the function definition being called.
  [rs] is the current values of registers,
  and [m] the current memory state.
- [Returnstate cs rs m]: [rs] is the current values of registers,
  and [m] the current memory state.

[cs] is a list of stack frames [Stackframe f sp c fr],
where [f] is the block reference for the calling function,
[c] the code within this function that follows the call instruction,
[sp] its stack pointer, and [fr] its private frame. *)

Inductive stackframe: Set :=
  | Stackframe:
      forall (f: function) (sp: val) (c: code) (fr: frame),
      stackframe.

Inductive state: Set :=
  | State:
      forall (stack: list stackframe) (f: function) (sp: val)
             (c: code) (rs: regset) (fr: frame) (m: mem),
      state
  | Callstate:
      forall (stack: list stackframe) (f: fundef) (rs: regset) (m: mem),
      state
  | Returnstate:
      forall (stack: list stackframe) (rs: regset) (m: mem),
      state.

(** [parent_frame s] returns the frame of the calling function.
  It is used to access function parameters that are passed on the stack
  (the [Mgetparent] instruction). *)

Definition parent_frame (s: list stackframe) : frame :=
  match s with
  | nil => empty_frame
  | Stackframe f sp c fr :: s => fr
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs fr m,
      step (State s f sp (Mlabel lbl :: c) rs fr m)
        E0 (State s f sp c rs fr m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs fr m)
        E0 (State s f sp c (rs#dst <- v) fr m)
  | exec_Msetstack:
     forall s f sp src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      step (State s f sp (Msetstack src ofs ty :: c) rs fr m)
        E0 (State s f sp c rs fr' m)
  | exec_Mgetparam:
      forall s f sp ofs ty dst c rs fr m v,
      get_slot (parent_frame s) ty (Int.signed ofs) v ->
      step (State s f sp (Mgetparam ofs ty dst :: c) rs fr m)
        E0 (State s f sp c (rs#dst <- v) fr m)
  | exec_Mop:
      forall s f sp op args res c rs fr m v,
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp (Mop op args res :: c) rs fr m)
        E0 (State s f sp c (rs#res <- v) fr m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp (Mload chunk addr args dst :: c) rs fr m)
        E0 (State s f sp c (rs#dst <- v) fr m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp (Mstore chunk addr args src :: c) rs fr m)
        E0 (State s f sp c rs fr m')
  | exec_Mcall:
      forall s f sp sig ros c rs fr m f',
      find_function ros rs = Some f' ->
      step (State s f sp (Mcall sig ros :: c) rs fr m)
        E0 (Callstate (Stackframe f sp c fr :: s) f' rs m)
  | exec_Mtailcall:
      forall s f stk soff sig ros c rs fr m f',
      find_function ros rs = Some f' ->
      step (State s f (Vptr stk soff) (Mtailcall sig ros :: c) rs fr m)
        E0 (Callstate s f' rs (Mem.free m stk))

  | exec_Malloc:
      forall s f sp c rs fr m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      step (State s f sp (Malloc :: c) rs fr m)
        E0 (State s f sp c
                   (rs#Conventions.loc_alloc_result <- (Vptr blk Int.zero))
                    fr m')
  | exec_Mgoto:
      forall s f sp lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      step (State s f sp (Mgoto lbl :: c) rs fr m)
        E0 (State s f sp c' rs fr m)
  | exec_Mcond_true:
      forall s f sp cond args lbl c rs fr m c',
      eval_condition cond rs##args m = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s f sp (Mcond cond args lbl :: c) rs fr m)
        E0 (State s f sp c' rs fr m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs fr m,
      eval_condition cond rs##args m = Some false ->
      step (State s f sp (Mcond cond args lbl :: c) rs fr m)
        E0 (State s f sp c rs fr m)
  | exec_Mreturn:
      forall s f stk soff c rs fr m,
      step (State s f (Vptr stk soff) (Mreturn :: c) rs fr m)
        E0 (Returnstate s rs (Mem.free m stk))
  | exec_function_internal:
      forall s f rs m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) rs m)
        E0 (State s f (Vptr stk (Int.repr (-f.(fn_framesize))))
                  f.(fn_code) rs (init_frame f) m')
  | exec_function_external:
      forall s ef args res rs1 rs2 m t,
      event_match ef args t res ->
      extcall_arguments rs1 (parent_frame s) ef.(ef_sig) args ->
      rs2 = (rs1#(Conventions.loc_result ef.(ef_sig)) <- res) ->
      step (Callstate s (External ef) rs1 m)
         t (Returnstate s rs2 m)
  | exec_return:
      forall f sp c fr s rs m,
      step (Returnstate (Stackframe f sp c fr :: s) rs m)
        E0 (State s f sp c rs fr m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      initial_state p (Callstate nil f (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs R3 = Vint r ->
      final_state (Returnstate nil rs m) r.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.
