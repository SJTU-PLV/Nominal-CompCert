Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import LanguageInterface.
Require Import Clight RustlightBase.

(** * Rust Intermediate Rrepresentation  *)

(** To compile Rustlight to RustIR, we replace the scopes (let stmt)
with StorageLive (StorageDead) statements, use CFG to represent the
program (better for analysis) and insert explicit drop operations (so
that the RustIR has no ownership semantics) *)

(** The definitions of place and expression are the same as Rustlight *)


Inductive statement :=
| Sassign : place -> expr -> statement
| Sset : ident -> expr -> statement
| Sstoragelive: ident -> statement
| Sstoragedead: ident -> statement
| Sdrop: place -> statement.

Definition bb := positive.

Inductive terminator :=
| Tgoto: bb -> terminator
| Tcall: option place -> expr -> list expr -> bb -> terminator
| Tifthenelse: expr -> bb -> bb -> terminator
| Treturn: option expr -> terminator.

Record basic_block :=
  { stmts : list statement;
    nextb: terminator }.

Definition cfg := PTree.t basic_block.

Record function :=
  { fn_return : type;
    fn_callconv: calling_convention;
    fn_params: list (ident * type);
    fn_vars: list (ident * type);
    fn_temps: list (ident * type); (* for drop flag *)
    fn_body: cfg;
    fn_entryblock : bb }.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.


Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal _ fd => type_of_function fd
  | External _ ef typs typ cc =>     
      Tfunction typs typ cc                
  end.


(** ** Semantics of RustIR *)

(* temporary variable environment  *)
Definition temp_env := PTree.t val.

(* global environment *)

Record genv := {genv_genv :> Genv.t fundef type; genv_cenv :> composite_env}.


Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env function) |}.


Section SEMANTICS.

(** States *)

Inductive stackframe: Type :=
| Stackframe
    (res: option place)
    (f: function)
    (next: bb)
    (e: env)
    (le: temp_env) : stackframe.
    
Inductive state: Type :=
| State
    (stack: list stackframe)
    (f: function)
    (b: bb)
    (pc: nat)
    (e: env)
    (le: temp_env)
    (m: mem) : state
| Callstate
    (stack: list stackframe)
    (vf: val)
    (args: list val)    
    (m: mem) : state
| Returnstate
    (stack: list stackframe)
    (res: val)
    (m: mem) : state.
  
(** get statement  *)

Definition code_in (id: bb) (pos: nat) (code: cfg) : option (statement + terminator) :=
  match code ! id with
  | Some b =>
      if Nat.eqb (length (stmts b)) pos then Some (inr (nextb b))
      else match nth_error (stmts b) pos with
           | Some stmt => Some (inl stmt)
           | _ => None
           end
  | None => None
  end.

(* same as Clight *)
Inductive alloc_variables (ce: composite_env) : env -> mem ->
                                                list (ident * type) ->
                                                env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables ce e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
      alloc_variables ce (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables ce e m ((id, ty) :: vars) e2 m2.

(* same as Clight *)
Fixpoint create_undef_temps (temps: list (ident * type)) : temp_env :=
  match temps with
  | nil => PTree.empty val
  | (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
 end.

(* It is the same as the function_entry in Clight *)
Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
    alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
    bind_parameters ge e m1 f.(fn_params) vargs m' ->
    le = create_undef_temps f.(fn_temps) ->
    function_entry ge f vargs m e le m'.

(** ** Evaluation of statements *)

Section SMALLSTEP.

Variable ge: genv.

Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f be p pc bid op stk e le m1 m2 b ofs v,
    eval_place ge e m1 p b ofs ->
    eval_expr ge e m1 be v op ->
    assign_loc ge (typeof be) m1 b ofs v m2 ->    
    (* get the statement *)
    code_in bid pc (fn_body f) = Some (inl (Sassign p be)) ->
    step (State stk f bid pc e le m1) E0 (State stk f bid (S pc) e le m2)
| step_set: forall f be id pc bid op stk e le le' m v,
    eval_expr ge e m be v op ->
    PTree.set id v le = le' ->
    (* get the statement *)
    code_in bid pc (fn_body f) = Some (inl (Sset id be)) ->
    step (State stk f bid pc e le m) E0 (State stk f bid (S pc) e le' m)
| step_drop: forall f p pc bid stk e le m m' b ofs,
    (* What is the semantics of drop statement? We can just drop the
    [Box] but this requires the compilation expland the drop operation
    for some composite types. Drop operations for some composite types
    (such as [List] defined by variant) are recursive, but it is a
    big-step in the source program. So it is difficult to prove a big
    step is simulated by the recursive function invokations. *)
    (** Current design is that this drop statement is drop with no
    partial moves. We plan to expand the drop when translating RustIR
    to Clight*)
    eval_place ge e m p b ofs ->
    drop_place_type ge (typeof_place p) m b ofs m' ->
    code_in bid pc (fn_body f) = Some (inl (Sdrop p)) ->
    step (State stk f bid pc e le m) E0 (State stk f bid (S pc) e le m')
| step_storagelive: forall f pc id bid stk e le m,
    code_in bid pc (fn_body f) = Some (inl (Sstoragelive id)) ->
    step (State stk f bid pc e le m) E0 (State stk f bid (S pc) e le m)
| step_storagedead: forall f pc id bid stk e le m,
    code_in bid pc (fn_body f) = Some (inl (Sstoragedead id)) ->
    step (State stk f bid pc e le m) E0 (State stk f bid (S pc) e le m)

(* evaluate terminator *)
| step_goto: forall f pc bid bid' stk e le m,
    code_in bid pc (fn_body f) = Some (inr (Tgoto bid')) ->
    step (State stk f bid pc e le m) E0 (State stk f bid' O e le m)
| step_ifthenelse: forall f pc bid bid1 bid2 bid' a v b op stk e le m,
    eval_expr ge e m a v op ->
    Val.bool_of_val v b ->
    bid' = (if b then bid1 else bid2) ->
    code_in bid pc (fn_body f) = Some (inr (Tifthenelse a bid1 bid2)) ->
    step (State stk f bid pc e le m) E0 (State stk f bid' O e le m)
| step_call: forall f bid bid' op pc stk a al optlp e le m vargs tyargs vf fd cconv tyres,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge e m a vf None ->
    eval_exprlist ge e m al tyargs vargs optlp ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    code_in bid pc (fn_body f) = Some (inr (Tcall op a al bid')) ->
    step (State stk f bid pc e le m) E0 (Callstate (Stackframe op f bid' e le :: stk) vf vargs m)
| step_return_0: forall f pc bid stk e le m,
    code_in bid pc (fn_body f) = Some (inr (Treturn None)) ->
    step (State stk f bid pc e le m) E0 (Returnstate stk Vundef m)
| step_return_1: forall f pc bid stk e le m a v op,
    eval_expr ge e m a v op ->
    code_in bid pc (fn_body f) = Some (inr (Treturn (Some a))) ->
    step (State stk f bid pc e le m) E0 (Returnstate stk v m)

| step_internal_function: forall f stk e le m m' vargs vf
    (FIND: Genv.find_funct ge vf = Some (Internal function f)),
  function_entry ge f vargs m e le m' ->
  step (Callstate stk vf vargs m) E0 (State stk f f.(fn_entryblock) O e le m')
| step_external_function: forall stk vf vargs m m' cc ty typs ef v t
    (FIND: Genv.find_funct ge vf = Some (External function ef typs ty cc)),
    external_call ef ge vargs m t v m' ->
    step (Callstate stk vf vargs m) t (Returnstate stk v m')

| step_returnstate_0: forall f stk bid e le m v,    
    step (Returnstate ((Stackframe None f bid e le) :: stk) v m) E0 (State stk f bid O e le m)
| step_returnstate_1: forall f stk bid e le m m' v p b ofs,
    eval_place ge e m p b ofs ->
    assign_loc ge (typeof_place p) m b ofs v m' ->
    step (Returnstate ((Stackframe (Some p) f bid e le) :: stk) v m) E0 (State stk f bid O e le m')
.

(** Open semantics *)

Inductive initial_state: c_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc ctargs ctres vargs m,
    Genv.find_funct ge vf = Some (Internal function f) ->
    type_of_function f = Tfunction targs tres tcc ->
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    initial_state (cq vf (signature_of_type ctargs ctres tcc) vargs m)
                  (Callstate nil vf vargs m).
    
Inductive at_external: state -> c_query -> Prop:=
| at_external_intro: forall vf name sg args stk m targs tres cconv,
    Genv.find_funct ge vf = Some (External function (EF_external name sg) targs tres cconv) ->    
    at_external (Callstate stk vf args m) (cq vf sg args m).

Inductive after_external: state -> c_reply -> state -> Prop:=
| after_external_intro: forall vf args stk m m' v,
    after_external
      (Callstate stk vf args m)
      (cr v m')
      (Returnstate stk v m').

Inductive final_state: state -> c_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate nil v m) (cr v m).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.
  
