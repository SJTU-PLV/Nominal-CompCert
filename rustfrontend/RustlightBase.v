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
Require Import Cop RustOp.
Require Import LanguageInterface.

Local Open Scope error_monad_scope.

(** * High-level Rust-like language  *)


(** ** Place (used to build lvalue expression) *)

Inductive place : Type :=
| Plocal : ident -> type -> place
| Pfield : place -> ident -> type -> place (**r access a field of struct: p.(id)  *)
| Pderef : place -> type -> place
| Pdowncast: place -> ident -> type -> place (**r represent the location of a constructor *)
.

Lemma place_eq: forall (p1 p2: place), {p1=p2} + {p1<>p2}.
Proof.
  generalize type_eq ident_eq. intros.
  decide equality.
Qed.

Global Opaque place_eq.

Definition typeof_place p :=
  match p with
  | Plocal _ ty => ty
  | Pfield _ _ ty => ty
  | Pderef _ ty => ty
  | Pdowncast _ _ ty => ty
  end.


(** ** Expression *)

Inductive pexpr : Type :=
| Eunit                                 (**r unit value  *)
| Econst_int: int -> type -> pexpr       (**r integer literal *)
| Econst_float: float -> type -> pexpr   (**r double float literal *)
| Econst_single: float32 -> type -> pexpr (**r single float literal *)
| Econst_long: int64 -> type -> pexpr    (**r long integer literal *)
| Eplace: place -> type -> pexpr (**r use of a variable, the only lvalue expression *)
| Ecktag: place -> ident -> pexpr           (**r check the tag of variant, e.g. [Ecktag p.(fid)]. We cannot check a downcast *)
| Eref:  origin -> mutkind -> place -> type -> pexpr     (**r &[mut] p  *)
| Eunop: unary_operation -> pexpr -> type -> pexpr  (**r unary operation *)
| Ebinop: binary_operation -> pexpr -> pexpr -> type -> pexpr. (**r binary operation *)

(* The evaluaiton of expr may produce a moved-out place *)
Inductive expr : Type :=
| Emoveplace: place -> type -> expr
| Epure: pexpr -> expr.


Definition typeof_pexpr (pe: pexpr) : type :=
  match pe with
  | Eunit => Tunit
  | Ecktag _ _ => type_bool
  | Econst_int _ ty
  | Econst_float _ ty
  | Econst_single _ ty
  | Econst_long _ ty                
  | Eplace _ ty
  | Eref _ _ _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty => ty
  end.

Definition typeof (e: expr) : type :=
  match e with
  | Emoveplace _ ty => ty
  | Epure pe => typeof_pexpr pe
    end.


(* What Tbox corresponds to? *)
(** TODO: Tbox -> None. reference -> None, raw poinetr -> C pointer,
Option<reference> -> C pointer *)
Fixpoint to_ctype (ty: type) : Ctypes.type :=
  match ty with
  | Tunit => Ctypes.type_int32s  (* unit is set to zero *)
  (* | Tbox _  => None *)
  | Tint sz si => Ctypes.Tint sz si noattr
  | Tlong si => Ctypes.Tlong si noattr
  | Tfloat fz => Ctypes.Tfloat fz noattr
  | Tstruct _ id  => Ctypes.Tstruct id noattr
  (* variant = Struct {tag: .. ; f: union} *)
  | Tvariant _ id => Ctypes.Tstruct id noattr
  | Treference _ _ ty
  | Tbox ty => Tpointer (to_ctype ty) noattr
      (* match (to_ctype ty) with *)
      (* | Some ty' =>  *)
      (*     Some (Ctypes.Tpointer ty' attr) *)
      (* | _ => None *)
  (* end *)
  | Tarray ty sz => Ctypes.Tarray (to_ctype ty) sz noattr
  | Tfunction _ _ tyl ty cc =>
      Ctypes.Tfunction (to_ctypelist tyl) (to_ctype ty) cc
  end
    
with to_ctypelist (tyl: typelist) : Ctypes.typelist :=
       match tyl with
       | Tnil => Ctypes.Tnil
       | Tcons ty tyl =>
           Ctypes.Tcons (to_ctype ty) (to_ctypelist tyl)
       end.
                                  

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Slet : ident -> type -> statement -> statement (**r declare a variable. let ident: type in *)
| Sassign : place -> expr -> statement (**r assignment [place' = rvalue]. Downcast cannot appear in LHS *)
| Sassign_variant : place -> ident -> ident -> expr -> statement (**r assign variant to a place *)
| Sbox: place -> expr -> statement        (**r box assignment [place = Box::new(expr)]  *)
| Scall: place -> expr -> list expr -> statement (**r function call, p =
  f(...). The assignee is mandatory, because we need to ensure that
  the return value (may be a box) is received *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Sloop: statement -> statement (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : option expr -> statement.      (**r [return] statement *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue : option ident;
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type); 
  fn_body: statement
}.  

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.


Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc
  end.


(** * Operational Semantics  *)

Definition own_fuel := 10%nat.

(** ** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.


Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env) |}.


(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** ** Ownership environment  *)

(* Only place' can own a memory location *)
Definition own_env := PTree.t (list place).

Definition empty_own_env : own_env := PTree.empty (list place).

(** TODO: Ownership type-state  *)

(* tss for Type-State System *)
(* Class Typestate (op: Type) : Type := { *)
(*     state: Type; *)
(*     init: state; *)
(*     valid: state -> bool; *)
(*     trans: state -> op -> state; *)
(*   }. *)


(* The basic state transitions

      ---------    (→ Init)    ---------
   →  | Unown |       ↔        |  Own  |
      ---------    (← Move)    ---------
          ↓ (Drop)
      ---------
      | Error |
      ---------
 *)
 
Inductive own_state : Type :=
| Own : own_state | Unown : own_state | Ownerror: own_state.

Inductive own_op: Type :=
| Init: own_op | Deinit: own_op.

Definition own_trans (s: own_state) (op: own_op) :=
  match s,op with
  | Own, Deinit => Unown
  | Own, Init => Own
  | Unown, Init => Own
  | _,_ => Ownerror
  end.

Definition own_valid (s: own_state) :=
  match s with
  | Ownerror => false
  | _ => true
  end.

(* Definition own_tss := *)
(*   Build_tss own_op own_state Unown own_valid own_trans. *)


(** Deference a location based on the type  *)

Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs (Vptr b ofs).

(** Memory error in deref_loc  *)

Inductive deref_loc_mem_error (ty: type) (m: mem) (b: block) (ofs: ptrofs) : Prop :=
  | deref_loc_value_error: forall chunk,
      access_mode ty = By_value chunk ->
      ~ Mem.valid_access m chunk b (Ptrofs.unsigned ofs) Readable ->
      deref_loc_mem_error ty m b ofs.


(** Assign a value to a location  *)

Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (* consider a = b ( a and b are struct ) *)
      (* evaluate b is (Vptr b' ofs'), evaluate a is (b,ofs) *)      
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      (* a and b are disjoint or equal *)
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs (Vptr b' ofs') m'.

(** Memory error in assign_loc  *)

Inductive assign_loc_mem_error (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs) : val -> Prop :=
| assign_loc_value_mem_error: forall v chunk,
    access_mode ty = By_value chunk ->
    ~ Mem.valid_access m chunk b (Ptrofs.unsigned ofs) Writable ->
    assign_loc_mem_error ce ty m  b ofs v
| assign_loc_copy_mem_error1: forall b' ofs',
    (* the memory location of the struct to be copied is not readable *)
    access_mode ty = By_copy ->
    ~ Mem.range_perm m b' (Ptrofs.unsigned ofs') ((Ptrofs.unsigned ofs') + (sizeof ce ty)) Cur Readable ->
    assign_loc_mem_error ce ty m b ofs (Vptr b' ofs')
| assign_loc_copy_mem_error2: forall v,
    (* the memory location of the struct to be stored is not writable *)
    access_mode ty = By_copy ->
    Mem.range_perm m b (Ptrofs.unsigned ofs) ((Ptrofs.unsigned ofs) + (sizeof ce ty)) Cur Writable ->
    assign_loc_mem_error ce ty m b ofs v.


(** Prefix of a place  *)

Fixpoint parent_paths (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: parent_paths p'
  | Pderef p' _ =>  p' :: parent_paths p'
  | Pdowncast p' _ _ => p' :: parent_paths p'
  end.

Fixpoint shallow_parent_paths (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: shallow_parent_paths p'
  | Pderef _ _ => nil
  (** FIXMEL: how to handle downcast? *)
  | Pdowncast p' _ _ => p' :: shallow_parent_paths p'
  end.

Fixpoint support_parent_paths (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: support_parent_paths p'
  | Pderef p' _ =>
      match typeof_place p' with
      | Tbox _ 
      | Treference _ Mutable _ =>
          p' :: support_parent_paths p'
      | _ => nil
      end
  | Pdowncast p' _ _ => p' :: support_parent_paths p'
  end.


Definition is_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (parent_paths p2).

Definition is_shallow_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (shallow_parent_paths p2).

Definition is_support_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (support_parent_paths p2).

Definition is_prefix_strict (p1 p2: place) : bool :=
  in_dec place_eq p1 (parent_paths p2).


Fixpoint local_of_place (p: place) :=
  match p with
  | Plocal id _ => id
  | Pfield p' _ _ => local_of_place p'
  | Pderef p' _ => local_of_place p'
  | Pdowncast p' _ _ => local_of_place p'
  end.

Definition is_sibling (p1 p2: place) : bool :=
  Pos.eqb (local_of_place p1) (local_of_place p2)
  && negb (is_prefix p1 p2 && is_prefix p2 p1).

Fixpoint local_type_of_place (p: place) :=
  match p with
  | Plocal id ty => ty
  | Pfield p' ty _ => local_type_of_place p'
  | Pderef p' ty => local_type_of_place p'
  | Pdowncast p' _ _ => local_type_of_place p'
  end.


Definition remove_own (own: own_env) (p: place) : option own_env :=
  let id := local_of_place p in
  match PTree.get id own with
  | Some own_path =>
      let erased := filter (fun (p1: place) => negb (is_prefix p p1)) own_path in
      Some (PTree.set id erased own)
  | None => None
  end.

Definition remove_own_option (own: own_env) (op: option place) : option own_env :=
  match op with
  | None => Some own
  | Some p => remove_own own p
  end.
  

Fixpoint remove_own_list (own: own_env) (pl: list place) : option own_env :=
  match pl with
  | p :: pl' =>
      match remove_own own p with
      | Some own' => remove_own_list own' pl'
      | None => None
      end
  | _ => None
  end.
  

(** Classify function (copy from Cop.v)  *)
Inductive classify_fun_cases : Type :=
| fun_case_f (targs: typelist) (tres: type) (cc: calling_convention) (**r (pointer to) function *)
| fun_default.

Definition classify_fun (ty: type) :=
  match ty with
  | Tfunction _ _ args res cc => fun_case_f args res cc
  (** TODO: do we allow function pointer?  *)
  (* | Treference (Tfunction args res cc) _ => fun_case_f args res cc *)
  | _ => fun_default
  end.
  
Section SEMANTICS.
  
(** ** Evaluation of expressions *)

Section EXPR.

Variable ce: composite_env.
Variable e: env.
Variable m: mem.

(* similar to eval_lvalue in Clight.v *)
Inductive eval_place : place -> block -> ptrofs -> Prop :=
| eval_Plocal: forall id b ty,
    (** TODO: there is no global variable, so we do not consider the
    gloabl environment *)
    e!id = Some (b, ty) ->
    eval_place (Plocal id ty) b Ptrofs.zero
| eval_Pfield_struct: forall p ty b ofs delta id i co bf orgs,
    eval_place p b ofs ->
    typeof_place p = Tstruct orgs id ->
    ce ! id = Some co ->
    field_offset ce i (co_members co) = OK (delta, bf) ->
    eval_place (Pfield p i ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
| eval_Pdowncast: forall  p ty b ofs delta id fid co bf orgs,
    eval_place p b ofs ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    (* Is it considered memory error? No! Because we can write any kind of place to trigger this error. *)
    variant_field_offset ce fid (co_members co) = OK (delta, bf) ->
    eval_place (Pdowncast p fid ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
| eval_Pderef: forall p ty l ofs l' ofs',
    eval_place p l ofs ->
    deref_loc (typeof_place p) m l ofs (Vptr l' ofs') ->
    eval_place (Pderef p ty) l' ofs'.

Inductive eval_place_mem_error : place -> Prop :=
| eval_Pfield_error: forall p ty i,
    eval_place_mem_error p ->
    eval_place_mem_error (Pfield p i ty)
| eval_Pdowncast_error: forall p ty fid,
    eval_place_mem_error p ->
    eval_place_mem_error (Pdowncast p fid ty)
| eval_Pderef_error1: forall p ty,
    eval_place_mem_error p ->
    eval_place_mem_error (Pderef p ty)
| eval_Pderef_error2: forall p l ofs ty,
    eval_place p l ofs ->
    deref_loc_mem_error ty m l ofs ->
    eval_place_mem_error (Pderef p ty)
.


Inductive eval_place_list : list place -> list block -> list ptrofs -> Prop :=
| eval_Pnil: eval_place_list nil nil nil
| eval_Pcons: forall p b ofs lp lb lofs,
    eval_place p b ofs ->
    eval_place_list lp lb lofs ->    
    eval_place_list (p :: lp) (b :: lb) (ofs :: lofs).


Definition int_val_casted (v: val) (ty: type) : Prop :=
  match v, ty with
  | Vint n, Tint sz sg =>
      cast_int_int sz sg n = n
  | _, _ => True
  end.


(* Evaluation of pure expression *)

Inductive eval_pexpr: pexpr -> val ->  Prop :=
| eval_Eunit:
    eval_pexpr Eunit (Vint Int.zero)
| eval_Econst_int:   forall i ty,
    eval_pexpr (Econst_int i ty) (Vint i)
| eval_Econst_float:   forall f ty,
    eval_pexpr (Econst_float f ty) (Vfloat f)
| eval_Econst_single:   forall f ty,
    eval_pexpr (Econst_single f ty) (Vsingle f)
| eval_Econst_long:   forall i ty,
    eval_pexpr (Econst_long i ty) (Vlong i)
| eval_Eunop:  forall op a ty v1 v aty,
    eval_pexpr a v1 ->
    (* Note that to_ctype Tbox = None *)
    to_ctype (typeof_pexpr a) = aty ->
    (** TODO: define a rust-specific sem_unary_operation  *)
    sem_unary_operation op v1 aty m = Some v ->
    eval_pexpr (Eunop op a ty) v
| eval_Ebinop: forall op a1 a2 ty v1 v2 v ty1 ty2,
    eval_pexpr a1 v1 ->
    eval_pexpr a2 v2 ->
    to_ctype (typeof_pexpr a1) = ty1 ->
    to_ctype (typeof_pexpr a2) = ty2 ->
    sem_binary_operation_rust op v1 ty1 v2 ty2 m = Some v ->
    (* For now, we do not return moved place in binary operation *)
    eval_pexpr (Ebinop op a1 a2 ty) v
| eval_Eplace: forall p b ofs ty v,
    eval_place p b ofs ->
    deref_loc ty m b ofs v ->
    (* adhoc: cast int if v is Vint. This premise is only useful if ty
    is type_bool and v is i8 which may be non-zero and non-one
    value. But we want to prove that it is one or zero *)
    (* int_val_casted v ty -> *)
    eval_pexpr (Eplace p ty) v
| eval_Ecktag: forall (p: place) b ofs tag tagz id fid co orgs,
    eval_place p b ofs ->
    (* load the tag *) 
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    field_tag fid co.(co_members) = Some tagz ->
    eval_pexpr (Ecktag p fid) (Val.of_bool (Int.eq tag (Int.repr tagz)))
| eval_Eref: forall p b ofs mut ty org,
    eval_place p b ofs ->
    eval_pexpr (Eref org mut p ty) (Vptr b ofs).

      
(* expression evaluation has two phase: evaluate the value and produce
the moved-out place *)
Inductive eval_expr: expr -> val -> Prop :=
| eval_Emoveplace: forall p ty v,
    eval_pexpr (Eplace p ty) v ->
    eval_expr (Emoveplace p ty) v
(* | eval_Emoveget: forall p fid ty v, *)
(*     eval_pexpr (Eget p fid ty) v -> *)
(*     eval_expr (Emoveget p fid ty) v *)
| eval_Epure: forall pe v,
    eval_pexpr pe v ->
    eval_expr (Epure pe) v.

Inductive eval_exprlist : list expr -> typelist -> list val -> Prop :=
| eval_Enil:
  eval_exprlist nil Tnil nil
| eval_Econs:   forall a bl ty tyl v1 v2 vl,
    (* For now, we does not allow type cast *)
    typeof a = ty ->
    eval_expr a v1 ->
    sem_cast v1 (typeof a) ty = Some v2 ->
    eval_exprlist bl tyl vl ->
    eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

(** Memory error in evaluation of expression  *)


Inductive eval_pexpr_mem_error: pexpr ->  Prop :=
| eval_Eunop_error:  forall op a ty,
    eval_pexpr_mem_error a ->
    eval_pexpr_mem_error (Eunop op a ty)
| eval_Ebinop_error: forall op a1 a2 ty,
    (eval_pexpr_mem_error a1 \/ eval_pexpr_mem_error a2) ->
    eval_pexpr_mem_error (Ebinop op a1 a2 ty)
| eval_Eplace_error1: forall p ty,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Eplace p ty)
| eval_Eplace_error2: forall p b ofs ty,
    eval_place p b ofs->
    deref_loc_mem_error ty m b ofs ->
    eval_pexpr_mem_error (Eplace p ty)
| eval_Ecktag_error1: forall p fid,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Ecktag p fid)
| eval_Ecktag_error2: forall p b ofs fid, 
    eval_place p b ofs ->
    (* tag is not readable *)
    ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    eval_pexpr_mem_error (Ecktag p fid)
| eval_Eref_error: forall p org mut ty,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Eref org mut p ty).

Inductive eval_expr_mem_error: expr -> Prop :=
| eval_Emoveplace_error: forall p ty,
    eval_pexpr_mem_error (Eplace p ty) ->
    eval_expr_mem_error (Emoveplace p ty)
| eval_Epure_mem_error: forall pe,
    eval_pexpr_mem_error pe ->
    eval_expr_mem_error (Epure pe).

Inductive eval_exprlist_mem_error : list expr -> typelist -> Prop :=
| eval_Econs_mem_error1: forall a bl ty tyl,
    eval_expr_mem_error a ->
    eval_exprlist_mem_error (a :: bl) (Tcons ty tyl)
| eval_Econs_mem_error2: forall a bl ty tyl v1,
    eval_expr a v1 ->
    eval_exprlist_mem_error bl tyl ->
    eval_exprlist_mem_error (a :: bl) (Tcons ty tyl)
.




(* The second phase of evaluation of expression *)

(* if [move (downcast p fid)] it means that p is moved *)
Definition moved_place (e: expr) : option place :=
  match e with
  | Emoveplace p _ => Some p
  | _ => None
  end.

Definition moved_place_list (el: list expr) : list place :=
  fold_right
    (fun (elt : expr) (acc : list place) =>
       match moved_place elt with
       | Some p => p :: acc
       | None => acc
       end) nil el.

End EXPR.


(** Continuations *)

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Klet: ident -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: place  -> function -> env -> own_env -> cont -> cont.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop s k => call_cont k
  (* pop Klet *)
  | Klet id k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (ie: own_env)
      (m: mem) : state
  | Callstate
      (vf: val)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state.                          


(** Automatic drop  *)

Definition definite_copy_type (ty: type) :=
  match ty with
  | Tunit
  | Tint _ _
  | Tlong _
  | Tfloat _
  | Tfunction _ _ _ _ _ => true
  | _ => false
  end.


(* normal recursive drop (do not consider own path): used for variant *)
(* It drop the resource assuming there is no partial move *)
Inductive drop_in_place (ce: composite_env) : type -> mem -> block -> ptrofs -> mem -> Prop :=
| drop_in_base: forall m b ofs ty,
    definite_copy_type ty = true ->
    drop_in_place ce ty m b ofs m
| drop_in_struct: forall m b ofs id co m' lb lofs lofsbit lty orgs,
    ce ! id = Some co ->
    (* do not use eval_place_list, directly compute the field offset *)
    field_offset_all ce co.(co_members) = OK lofsbit ->
    lofs = map (fun ofsbit => Ptrofs.add ofs (Ptrofs.repr (fst ofsbit))) lofsbit ->
    lb = repeat b (length co.(co_members)) ->
    lty = map type_member co.(co_members) ->
    drop_in_place_list ce lty m lb lofs m' ->
    drop_in_place ce (Tstruct orgs id) m b ofs m'
| drop_in_variant: forall m b ofs id co m' tag memb fid ofs' bf orgs,
    ce ! id = Some co ->
    (* load tag  *)
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    (* use tag to choose the member *)
    list_nth_z co.(co_members) (Int.unsigned tag) = Some memb ->
    fid = name_member memb ->
    variant_field_offset ce fid co.(co_members) = OK (ofs', bf) ->
    (* drop the selected type *)
    drop_in_place ce (type_member memb) m b (Ptrofs.add ofs (Ptrofs.repr ofs')) m' ->
    drop_in_place ce (Tvariant orgs id) m b ofs m
| drop_in_box: forall ty ty' m m' m'' b ofs b' ofs',
    ty = Tbox ty' ->
    (* The contents in [p] is (Vptr b' ofs') *)
    Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') ->
    drop_in_place ce ty' m b' ofs' m' ->
    (* Free the contents in (b',ofs') *)
    Mem.free m' b' (Ptrofs.signed ofs') ((Ptrofs.signed ofs') + sizeof ce ty') = Some m'' ->
    drop_in_place ce ty m b ofs m''

                    
with drop_in_place_list (ce: composite_env) : list type -> mem -> list block -> list ptrofs -> mem -> Prop :=
| drop_type_list_nil: forall m,
    drop_in_place_list ce nil m nil nil m
| drop_type_list_cons: forall b ty tys' lb' ofs lofs' m m' m'',
    drop_in_place ce ty m b ofs m' ->
    drop_in_place_list ce tys' m' lb' lofs' m'' ->
    drop_in_place_list ce (ty :: tys') m (b :: lb') (ofs :: lofs') m''.

(** Memory error in drop_in_place  *)

Inductive drop_in_place_mem_error (ce: composite_env) : type -> mem -> block -> ptrofs -> Prop :=
| drop_in_box_error1: forall ty ty' m b ofs,
    ty = Tbox ty' ->
    (* The contents in [p] is Unreadable. Use signed or unsigned? *)
    ~ Mem.valid_access m Mptr b (Ptrofs.signed ofs) Readable ->
    drop_in_place_mem_error ce ty m b ofs
| drop_in_box_error2: forall ty ty' m b ofs b' ofs',
    ty = Tbox ty' ->
    Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') ->
    drop_in_place_mem_error ce ty' m b' ofs' ->
    drop_in_place_mem_error ce ty m b ofs
| drop_in_box_error3: forall ty ty'  m m' b ofs b' ofs',
    ty = Tbox ty'  ->
    Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') ->
    drop_in_place ce ty' m b' ofs' m' ->
    ~ Mem.range_perm m' b' (Ptrofs.signed ofs') ((Ptrofs.signed ofs') + sizeof ce ty') Cur Freeable ->
    drop_in_place_mem_error ce ty m b ofs
| drop_in_struct_error: forall m b ofs id  co lb lofs lofsbit lty orgs,
    ce ! id = Some co ->
    (* do not use eval_place_list, directly compute the field offset *)
    field_offset_all ce co.(co_members) = OK lofsbit ->
    lofs = map (fun ofsbit => Ptrofs.add ofs (Ptrofs.repr (fst ofsbit))) lofsbit ->
    lb = repeat b (length co.(co_members)) ->
    lty = map type_member co.(co_members) ->
    drop_in_place_list_mem_error ce lty m lb lofs ->
    drop_in_place_mem_error ce (Tstruct orgs id ) m b ofs
| drop_in_variant_error1: forall m b ofs id  co orgs,
    ce ! id = Some co ->
    ~Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    drop_in_place_mem_error ce (Tvariant orgs id ) m b ofs
| drop_in_variant_error2: forall m b ofs id co tag memb fid ofs' bf orgs,
    ce ! id = Some co ->
    (* load tag  *)
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    (* use tag to choose the member *)
    list_nth_z co.(co_members) (Int.unsigned tag) = Some memb ->
    fid = name_member memb ->
    variant_field_offset ce fid co.(co_members) = OK (ofs', bf) ->
    (* drop the selected type *)
    drop_in_place_mem_error ce (type_member memb) m b (Ptrofs.add ofs (Ptrofs.repr ofs')) ->
    drop_in_place_mem_error ce (Tvariant orgs id ) m b ofs

  
with drop_in_place_list_mem_error (ce: composite_env) : list type -> mem -> list block -> list ptrofs -> Prop :=
| drop_type_list_cons_error1: forall b ty tys' lb' ofs lofs' m,
    drop_in_place_mem_error ce ty m b ofs ->
    drop_in_place_list_mem_error ce (ty :: tys') m (b :: lb') (ofs :: lofs')
| drop_type_list_cons_error2: forall b ty tys' lb' ofs lofs' m m',
    drop_in_place ce ty m b ofs m' ->
    drop_in_place_list_mem_error ce tys' m' lb' lofs' ->
    drop_in_place_list_mem_error ce (ty :: tys') m (b :: lb') (ofs :: lofs')

.


(* It drop the resource assuming there may be partial moved paths *)
Inductive drop_place' (ce: composite_env) (owned: list place) : place -> mem -> block -> ptrofs -> mem -> Prop :=
| drop_base: forall ty (p: place) m b ofs,
    typeof_place p = ty ->
    (* It is not of type [Tbox] *)
    definite_copy_type ty = true ->
    drop_place' ce owned p m b ofs m
| drop_moved: forall  p m b ofs,
    not (In p owned) ->
    drop_place' ce owned p m b ofs m
| drop_struct: forall (p: place) m b ofs id  co m' lb lofs lofsbit fields orgs,
    (* recursively drop all the fields *)
    typeof_place p = Tstruct orgs id  ->
    ce ! id = Some co ->
    fields = map (fun memb => match memb with | Member_plain fid fty => Pfield p fid fty end) co.(co_members) ->
    (* do not use eval_place_list, directly compute the field offset *)
    field_offset_all ce co.(co_members) = OK lofsbit ->
    lofs = map (fun ofsbit => Ptrofs.add ofs (Ptrofs.repr (fst ofsbit))) lofsbit ->
    lb = repeat b (length co.(co_members)) ->
    drop_place_list' ce owned fields m lb lofs m' ->
    drop_place' ce owned p m b ofs m'
| drop_variant: forall (p: place) m b ofs id  m' orgs,
    (* select the type based on the tag value *)
    typeof_place p = Tvariant orgs id  ->
    (* p is in owned, so we just use type to destruct the variant *)
    drop_in_place ce (Tvariant orgs id ) m b ofs m' ->
    drop_place' ce owned p m b ofs m'
| drop_box: forall (p: place)  ty m m' m'' b' b ofs ofs',
    typeof_place p = Tbox ty  ->
    (* The contents in [p] is (Vptr b' ofs') *)
    Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') ->
    drop_place' ce owned (Pderef p ty) m b' ofs' m' ->
    (* Free the contents in (b',ofs') *)
    Mem.free m' b' (Ptrofs.signed ofs') ((Ptrofs.signed ofs') + sizeof ce ty) = Some m'' ->
    drop_place' ce owned p m b ofs m''

with drop_place_list' (ce: composite_env) (owned: list place) : list place -> mem -> list block -> list ptrofs -> mem -> Prop :=
| drop_list_nil: forall m,
    drop_place_list' ce owned nil m nil nil m
| drop_list_cons: forall p lp' b lb' ofs lofs' m m' m'',
    drop_place' ce owned p m b ofs m' ->
    drop_place_list' ce owned lp' m' lb' lofs' m'' ->
    drop_place_list' ce owned (p :: lp') m (b :: lb') (ofs :: lofs') m''.

  
(** Free {*p, **p ,... } according to me  *)
Inductive drop_place (ce: composite_env) (e: env) (ie: own_env) (p: place) (m: mem) : mem -> Prop :=
| drop_gen: forall b ofs m' id owned,
    eval_place ce e m p b ofs ->
    local_of_place p = id ->
    PTree.get id ie = Some owned ->
    drop_place' ce owned p m b ofs m' ->
    drop_place ce e ie p m m'.

Inductive drop_place_list (ce: composite_env) (e: env) (own: own_env) (m: mem) : list place -> mem -> Prop :=
| drop_place_list_base:
    drop_place_list ce e own m nil m
| drop_place_list_cons: forall p lp m' m'',
    drop_place ce e own p m m' ->
    drop_place_list ce e own m' lp m'' ->
    drop_place_list ce e own m (p::lp) m''.


(** A more comprehensive drop implementation  *)
(* Inductive drop_place'' (ce: composite_env) (owned: list place) : place -> mem -> mem -> Prop := *)
(* | drop_base: forall ty p m, *)
(*     typeof_place p = ty -> *)
(*     (* It is not of type [Tbox] *) *)
(*     copy_type ty = true -> *)
(*     drop_place'' ce owned p m m *)
(* | drop_moved: forall  p m, *)
(*     not (In p owned) -> *)
(*     drop_place'' ce owned p m m *)
(* | drop_struct: forall p m id attr co m' fields,  *)
(*     typeof_place p = Tstruct id attr -> *)
(*     ce ! id = Some co -> *)
(*     fields = map (fun memb => match memb with | Member_plain fid fty => Pfield p fid fty end) co.(co_members) -> *)
(*     drop_place_list'' ce owned fields m m' -> *)
(*     drop_place'' ce owned p m m' *)
(* (* | drop_box: forall ty ty' m' m'' b' ofs', *) *)
(* (*     ty = Tbox ty' -> *) *)
(* (*     (* p owns the location it points to *) *) *)
(* (*     In p owned -> *) *)
(* (*     (* The contents in [p] is (Vptr b' ofs') *) *) *)
(* (*     Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') -> *) *)
(* (*     drop_place' owned (Pderef p ty') m b' ofs' m' -> *) *)
(* (*     (* Free the contents in (b',ofs') *) *) *)
(* (*     Mem.free m' b' (Ptrofs.signed ofs') ((Ptrofs.signed ofs') + sizeof ty') = Some m'' -> *) *)
(* (*     drop_place' owned p m b ofs m'' *) *)

(* with drop_place_list'' (ce: composite_env) (owned: list place) : list place -> mem -> mem -> Prop := *)
(* | drop_list_nil: forall m, *)
(*     drop_place_list'' ce owned nil m m *)
(* | drop_list_cons: forall p lp' m m' m'', *)
(*     drop_place'' ce owned p m m' -> *)
(*     drop_place_list'' ce owned lp' m' m'' -> *)
(*     drop_place_list'' ce owned (p :: lp') m m''. *)




(** Ownership path  *)

Fixpoint own_path (fuel: nat) (ce: composite_env) (p: place) (ty: type) : list place :=
  match fuel with
  | O => nil
  | S fuel' =>
      match ty with
      | Tbox ty' =>
          let deref := Pderef p ty' in
          p :: own_path fuel' ce deref ty'
      (* | Treference ty' Mutable _ => *)
      (*     let deref := Pderef p ty' in *)
      (*     p :: init_path deref ty' *)
      | Tstruct _ id =>
          match ce ! id with
          | Some co =>
              let acc flds m :=
                let p' := match m with | Member_plain id ty => (Pfield p id ty) end in
                flds ++ own_path fuel' ce p' ty
              in
              let fields := fold_left acc co.(co_members) nil in
              (* if fields is empty, p is not returned *)
              match fields with
              | nil => nil
              | _ => p :: fields
              end
          | _ => p :: nil
          end
      | Tvariant _ _ =>
          if own_type ce ty then p :: nil
          else nil
      | _ => nil
      end
  end.
  
Let own_path := own_path own_fuel.

(** Allocate memory blocks for function parameters and build the local environment and move environment  *)
Inductive alloc_variables (ce: composite_env) : env -> own_env -> mem ->
                                                list (ident * type) ->
                                                env -> own_env -> mem -> Prop :=
| alloc_variables_nil:
  forall e own m,
    alloc_variables ce e own m nil e own m
| alloc_variables_cons:
  forall e own m id ty vars m1 b1 m2 e2 own1 drops,
    Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
    (* get the initialized path based on ty *)
    own_path ce (Plocal id ty) ty = drops ->
    alloc_variables ce (PTree.set id (b1, ty) e) (PTree.set id drops own) m1 vars e2 own1 m2 ->
    alloc_variables ce e own m ((id, ty) :: vars) e2 own1 m2.

(** Assign the values to the memory blocks of the function parameters  *)
Inductive bind_parameters (ce: composite_env) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ce e m nil nil m
  | bind_paranmeters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ce ty m b Ptrofs.zero v1 m1 ->
      bind_parameters ce e m1 params vl m2 ->
      bind_parameters ce e m ((id, ty) :: params) (v1 :: vl) m2.

Inductive bind_parameters_mem_error (ce: composite_env) (e: env) : mem -> list (ident * type) -> list val -> Prop :=
| bind_parameters_mem_error_cons1: forall m id ty params v1 vl b,
    e ! id = Some (b, ty) ->
    assign_loc_mem_error ce ty m b Ptrofs.zero v1 ->
    bind_parameters_mem_error ce e m ((id, ty) :: params) (v1 :: vl)
| bind_parameters_mem_error_cons2: forall m id ty params v1 vl b m1,
    e ! id = Some (b, ty) ->
    assign_loc ce ty m b Ptrofs.zero v1 m1 ->
    bind_parameters_mem_error ce e m1 params vl ->
    bind_parameters_mem_error ce e m ((id, ty) :: params) (v1 :: vl).


(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (ce: composite_env) (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ce ty) end.

Definition blocks_of_env (ce: composite_env) (e: env) : list (block * Z * Z) :=
  List.map (block_of_binding ce) (PTree.elements e).

(** Return the list of places in local environment  *)

Definition place_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (Plocal id ty) end.

Definition places_of_env (e:env) : list place :=
  List.map place_of_binding (PTree.elements e).
                                  

(** Function entry semantics: the key is to instantiate the move environments  *)
Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (own: own_env) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params)) ->
    alloc_variables ge empty_env empty_own_env m f.(fn_params) e own m1 ->
    bind_parameters ge e m1 f.(fn_params) vargs m' ->
    function_entry ge f vargs m e own m'.

Section SMALLSTEP.

Variable ge: genv.

Inductive step : state -> trace -> state -> Prop :=

| step_assign: forall f e (p: place) ty op k le own own' own'' m1 m2 m3 b ofs v id  orgs,
    (** FIXME: some ugly restriction  *)
    typeof_place p = ty ->
    typeof e = ty ->
    ty <> Tvariant orgs id  ->
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value and the moved place (optional) *)
    eval_expr ge le m1 e v ->
    moved_place e = op ->
    (* update the initialized environment based on [op] *)
    remove_own_option own op = Some own' ->
    (* drop the successors of p (i.e., *p, **p, ...). If ty is not
    owned type, drop_place has no effect. We must first update the me
    and then drop p, consider [ *p=move *p ] *)
    drop_place ge le own' p m1 m2 ->
    (* update the ownership env for p *)
    PTree.set (local_of_place p) (own_path ge p (typeof_place p)) own' = own'' ->
    (* assign to p  *)
    (* note that the type is the expreesion type, consider [a = 1]
    where a is [variant{int,float} *)
    assign_loc ge ty m2 b ofs v m3 ->
    step (State f (Sassign p e) k le own m1) E0 (State f Sskip k le own'' m3) 
         
| step_assign_variant: forall f e (p: place) ty op k le own own' own'' m1 m2 m3 m4 b ofs ofs' v tag bf co id fid enum_id  orgs,
    typeof_place p = ty ->
    typeof e = ty ->
    ty = Tvariant orgs id  ->
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the boxexpr, return the value and the moved place (optional) *)
    eval_expr ge le m1 e v ->
    moved_place e = op ->
    (* update the initialized environment based on [op] *)
    remove_own_option own op = Some own' ->
    (* drop the successors of p (i.e., *p, **p, ...). If ty is not
    owned type, drop_place has no effect. We must first update the me
    and then drop p, consider [ *p=move *p ] *)
    drop_place ge le own' p m1 m2 ->
    (* update the ownership env for p *)
    PTree.set (local_of_place p) (own_path ge p (typeof_place p)) own' = own'' ->
    (* assign to p  *)
    (** different from normal assignment: update the tag and assign value *)
    ge.(genv_cenv) ! id = Some co ->
    field_tag fid co.(co_members) = Some tag ->
    (* set the tag *)
    Mem.storev Mint32 m2 (Vptr b ofs) (Vint (Int.repr tag)) = Some m3 ->
    field_offset ge fid co.(co_members) = OK (ofs', bf) ->
    (* set the value *)
    assign_loc ge ty m3 b (Ptrofs.add ofs (Ptrofs.repr ofs')) v m4 ->
    step (State f (Sassign_variant p enum_id fid e) k le own m1) E0 (State f Sskip k le own'' m4)

| step_box: forall f e (p: place) ty op k le own1 own2 own3 m1 m2 m3 b v,
    typeof e = ty ->
    (* typeof_place p = TSletbox ty attr -> *)
    eval_expr ge le m1 e v ->
    (* allocate the memory block *)
    Mem.alloc m1 0 (sizeof ge ty) = (m2, b) ->
    (* assign the value *)
    assign_loc ge ty m2 b Ptrofs.zero v m3 ->
    (* update the ownership environment *)
    moved_place e = op ->
    remove_own_option own1 op = Some own2 ->
    (* update the ownership env for p *)
    PTree.set (local_of_place p) (own_path ge p ty) own2 = own3 ->
    step (State f (Sbox p e) k le own1 m1) E0 (* may be we can change the effect *) (State f Sskip k le own3 m3)  
         
| step_let: forall f ty id own m1 m2 le1 le2 b k stmt,
    (* allocate the block for id *)
    Mem.alloc m1 0 (sizeof ge ty) = (m2, b) ->
    (* uppdate the local env *)
    PTree.set id (b, ty) le1 = le2 ->
    step (State f (Slet id ty stmt) k le1 own m1) E0 (State f stmt (Klet id k) le2 own m2)

         
(** FIXME: we do not allow initialization in let statement. So that we
can initialize struct *)
(* | step_let: forall f be op v ty id own1 own2 own3 m1 m2 m3 m4 le1 le2 b k stmt, *)
(*     typeof_boxexpr be = ty -> *)
(*     eval_boxexpr ge le1 m1 be v op m2 -> *)
(*     (* update the move environment *) *)
(*     remove_own own1 op = Some own2 -> *)
(*     (* allocate the block for id *) *)
(*     Mem.alloc m2 0 (sizeof ge ty) = (m3, b) -> *)
(*     (* uppdate the local env *) *)
(*     PTree.set id (b, ty) le1 = le2 -> *)
(*     (* update the ownership environment *) *)
(*     PTree.set id (own_path ge (Plocal id ty) ty) own2 = own3 -> *)
(*     (* assign [v] to [b] *) *)
(*     assign_loc ge ty m3 b Ptrofs.zero v m4 -> *)
(*     step (State f (Slet id ty be stmt) k le1 own1 m1) E0 (State f stmt (Klet id k) le2 own3 m3) *)
         
(* | step_call_0: forall f a al optlp k le own1 own2 m vargs tyargs vf fd cconv tyres, *)
(*     classify_fun (typeof a) = fun_case_f tyargs tyres cconv -> *)
(*     eval_expr ge le m a vf -> *)
(*     eval_exprlist ge le m al tyargs vargs -> *)
(*     moved_place_list al = optlp -> *)
(*     (* CHECKME: update the initialized environment *) *)
(*     remove_own_list own1 optlp = Some own2 -> *)
(*     Genv.find_funct ge vf = Some fd -> *)
(*     type_of_fundef fd = Tfunction tyargs tyres cconv -> *)
(*     step (State f (Scall None a al) k le own1 m) E0 (Callstate vf vargs (Kcall None f le own2 k) m) *)
| step_call_1: forall f a al optlp k le own1 own2 m vargs tyargs vf fd cconv tyres p orgs org_rels,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m a vf ->
    eval_exprlist ge le m al tyargs vargs ->
    moved_place_list al = optlp ->
    (* CHECKME: update the move environment *)
    remove_own_list own1 optlp = Some own2 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    step (State f (Scall p a al) k le own1 m) E0 (Callstate vf vargs (Kcall p f le own2 k) m)
                 
(* End of a let statement, free the place and its drop obligations *)
| step_end_let: forall f id k le1 le2 own1 own2 m1 m2 m3 ty b s,
    s = Sskip \/ s = Sbreak \/ s = Scontinue ->
    PTree.get id le1 = Some (b, ty) ->
    (* free {*id, **id, ...} if necessary *)
    drop_place ge le1 own1 (Plocal id ty) m1 m2 ->
    (* free the block [b] of the local variable *)
    Mem.free m1 b 0 (sizeof ge ty) = Some m2 ->
    (* clear [id] in the local env and move env. It is necessary for the memory deallocation in return state *)
    PTree.remove id le1 = le2 ->
    PTree.remove id own1 = own2 ->
    step (State f s (Klet id k) le1 own1 m1) E0 (State f s k le2 own2 m3)

| step_internal_function: forall vf f vargs k m e me m'
    (FIND: Genv.find_funct ge vf = Some (Internal f)),
    function_entry ge f vargs m e me m' ->
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e me m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc)),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')

(** Return cases  *)
| step_return_0: forall e own lp lb m1 m2 f k ,
    places_of_env e = lp ->
    (* drop the lived drop obligations *)
    drop_place_list ge e own m1 lp m2 ->
    blocks_of_env ge e = lb ->
    (* drop the stack blocks *)
    Mem.free_list m1 lb = Some m2 ->
    step (State f (Sreturn None) k e own m1) E0 (Returnstate Vundef (call_cont k) m2)
| step_return_1: forall le a v op own own' lp lb m1 m2 m3 f k ,
    eval_expr ge le m1 a v ->
    moved_place a = op ->
    (* CHECKME: update move environment, because some place may be
    moved out to the callee *)
    remove_own_option own op = Some own' ->
    places_of_env le = lp ->
    drop_place_list ge le own' m1 lp m2 ->
    (* drop the stack blocks *)
    blocks_of_env ge le = lb ->
    Mem.free_list m2 lb = Some m3 ->
    step (State f (Sreturn (Some a)) k le own m1) E0 (Returnstate v (call_cont k) m3)
(* no return statement but reach the end of the function *)
| step_skip_call: forall e own lp lb m1 m2 m3 f k,
    is_call_cont k ->
    places_of_env e = lp ->
    drop_place_list ge e own m1 lp m2 ->
    blocks_of_env ge e = lb ->
    Mem.free_list m2 lb = Some m3 ->
    step (State f Sskip k e own m1) E0 (Returnstate Vundef (call_cont k) m3)
         
(* | step_returnstate_0: forall v m e me f k, *)
(*     step (Returnstate v (Kcall None f e me k) m) E0 (State f Sskip k e me m) *)
| step_returnstate_1: forall (p: place) v b ofs ty m m' m'' e own own' f k,
    (* drop and replace *)
    drop_place ge e own p m m' ->
    (* update the ownership environment *)
    PTree.set (local_of_place p) (own_path ge p (typeof_place p)) own = own' ->
    eval_place ge e m' p b ofs ->
    assign_loc ge ty m' b ofs v m'' ->    
    step (Returnstate v (Kcall p f e own k) m) E0 (State f Sskip k e own' m'')

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e me m,
    step (State f (Ssequence s1 s2) k e me m)
      E0 (State f s1 (Kseq s2 k) e me m)
| step_skip_seq: forall f s k e me m,
    step (State f Sskip (Kseq s k) e me m)
      E0 (State f s k e me m)
| step_continue_seq: forall f s k e me m,
    step (State f Scontinue (Kseq s k) e me m)
      E0 (State f Scontinue k e me m)
| step_break_seq: forall f s k e me m,
    step (State f Sbreak (Kseq s k) e me m)
      E0 (State f Sbreak k e me m)
| step_ifthenelse:  forall f a s1 s2 k e me me' m v1 b ty,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e me m)
      E0 (State f (if b then s1 else s2) k e me' m)
| step_loop: forall f s k e me m,
    step (State f (Sloop s) k e me m)
      E0 (State f s (Kloop s k) e me m)
| step_skip_or_continue_loop:  forall f s k e me m x,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e me m)
      E0 (State f s (Kloop s k) e me m)
| step_break_loop:  forall f s k e me m,
    step (State f Sbreak (Kloop s k) e me m)
      E0 (State f Sskip k e me m)
.


(** Open semantics *)

(** IDEAS: can we check the validity of the input values based on the
function types?  *)
Inductive initial_state: c_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc ctargs ctres vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (** TODO: val_casted_list *)
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    initial_state (cq vf (signature_of_type ctargs ctres tcc) vargs m)
                  (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> c_query -> Prop:=
| at_external_intro: forall vf name sg args k m targs tres cconv orgs org_rels,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name sg) targs tres cconv) ->    
    at_external (Callstate vf args k m) (cq vf sg args m).

Inductive after_external: state -> c_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (cr v m')
      (Returnstate v k m').

Inductive final_state: state -> c_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (cr v m).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.


(** ** Notations of Rustlight program *)

Declare Custom Entry rustlight.
Declare Scope rustlight_scope.
Declare Custom Entry rustlight_aux.
Declare Custom Entry rustlight_place.
Declare Custom Entry rustlight_expr.

Notation "<{ s }>" := s (s custom rustlight_aux) : rustlight_scope.
Notation "s" := s (in custom rustlight_aux at level 0, s custom rustlight) : rustlight_scope.

(* Notations for statement (level > 50) *)
Notation "'if' e 'then' s1 'else' s2 'end'" := (Sifthenelse e s1 s2) (in custom rustlight at level 80, e custom rustlight_expr at level 20, s1 at level 99, s2 at level 99) : rustlight_scope.
Notation "s1 ; s2" := (Ssequence s1 s2) (in custom rustlight at level 99, right associativity) : rustlight_scope.
Notation "'skip'" := Sskip (in custom rustlight at level 0) : rustlight_scope.
Notation "'break'" := Sbreak (in custom rustlight at level 0) : rustlight_scope.
Notation "'continue'" := Scontinue (in custom rustlight at level 0) : rustlight_scope.
Notation "'return0'" := (Sreturn None) (in custom rustlight at level 0) : rustlight_scope.
Notation "'return' e" := (Sreturn (@Some expr e)) (in custom rustlight at level 80, e custom rustlight_expr at level 20) : rustlight_scope.
Notation "'let' x : t 'in' s 'end' " := (Slet x t s) (in custom rustlight at level 80, s at level 99, x global, t global) : rustlight_scope.
Notation "'loop' s 'end'" := (Sloop s) (in custom rustlight at level 80, s at level 99) : rustlight_scope.
Notation "'Box' p := ( e ) " := (Sbox p e) (in custom rustlight at level 80, p custom rustlight_place at level 20, e custom rustlight_expr at level 20) : rustlight_scope.
Notation " p := e " := (Sassign p e) (in custom rustlight at level 80, p custom rustlight_place at level 20, e custom rustlight_expr at level 20) : rustlight_scope.
Notation " p <- f @ l " := (Scall p f l) (in custom rustlight at level 80, p custom rustlight_place at level 20, f custom rustlight_expr at level 20, l custom rustlight_expr at level 20) : rustlight_scope.


(* Notation for place *)

Notation " ( x ) " := x (in custom rustlight_place at level 20) : rustlight_scope.
Notation " x # t " := (Plocal x t) (in custom rustlight_place at level 0, x global, t global) : rustlight_scope.
Notation " ! p " := (Pderef p (deref_type (typeof_pexpr p))) (in custom rustlight_place at level 10, p at level 20) : rustlight_scope.
Notation " p . x < t > " := (Pfield p x t) (in custom rustlight_place at level 10, x global, t global) : rustlight_scope.


(* Notations for expression. Expression is at level 20 *)

Notation " ( x ) " := x (in custom rustlight_expr at level 20) : rustlight_scope.
Notation " { x , .. , y } " := (cons x .. (cons y nil) .. ) (in custom rustlight_expr at level 20) : rustlight_scope.
Notation " e1 < e2 " := ((Ebinop Ole e1 e2 type_bool)) (in custom rustlight_expr at level 15, e2 at level 20, left associativity) : rustlight_scope.
Notation " $ k " := ((Econst_int (Int.repr k) type_int32s)) (in custom rustlight_expr at level 10, k constr) : rustlight_scope.
Notation " e1 * e2 " := ((Ebinop Omul e1 e2 (typeof e1)))  (in custom rustlight_expr at level 15, e2 at level 20, left associativity) : rustlight_scope.
Notation " e1 - e2 " := ((Ebinop Osub e1 e2 (typeof e1)))  (in custom rustlight_expr at level 15, e2 at level 20, left associativity) : rustlight_scope.
Notation " 'copy' p " := ((Eplace p (typeof_place p))) (in custom rustlight_expr at level 20, p custom rustlight_place at level 20) : rustlight_scope.
Notation " 'move' p " := (Emoveplace p (typeof_place p)) (in custom rustlight_expr at level 20, p custom rustlight_place at level 20) : rustlight_scope.
(* TODO: Ecktag and Eget/Emoveget *)


(* Print Grammar constr. *)

Local Open Scope rustlight_scope.

Definition A : ident := 1%positive.
Definition B : ident := 2%positive.
Definition C : ident := 3%positive.
Definition D : ident := 4%positive.
Definition E : ident := 5%positive.


(* Print Custom Grammar rustlight. *)

Definition ident_to_place_int32s (id: ident) : place := Plocal id type_int32s.

Definition place_to_pexpr (p: place) : pexpr := (Eplace p (typeof_place p)).

Definition pexpr_to_expr (pe: pexpr) : expr := Epure pe.

Coercion ident_to_place_int32s : ident >-> place.
Coercion place_to_pexpr: place >-> pexpr.
Coercion pexpr_to_expr: pexpr >-> expr.

Fail Definition test_option_ident_to_expr : option expr  := Some A.
Definition test_option_ident_to_expr : option expr  := @Some expr A.

(* Print Graph. *)
(* Print Coercion Paths ident expr. *)

Definition test : statement :=
  <{ let A : type_int32s in
     A#type_int32s := $1;
     A#type_int32s := $0;
     return (copy A#type_int32s);
     skip; break; return0; return (move A#type_int32s);
     if (($1) < ($0)) then
       B#type_int32s := copy C#type_int32s;
       A#type_int32s := copy B#type_int32s
     else
       A#type_int32s := copy C#type_int32s
     end;
     loop
       A#type_int32s := copy C#type_int32s;
       B#type_int32s := copy A#type_int32s
     end;
     return0
     end }>.

(** ** Pretty printing for Rustlight programs  *)
