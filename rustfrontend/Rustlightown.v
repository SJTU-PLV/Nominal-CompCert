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
Require Import Ctypes Rusttypes Rustlight.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import InitDomain.

Local Open Scope error_monad_scope.


(** Generate drop glue map like RustIR *)


(* Extract composite id to drop glue id list *)
Definition extract_drop_id (g: ident * globdef fundef type) : ident * ident :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => (comp_id, glue_id)
      | None => (1%positive, glue_id)
      end
  | _ => (1%positive, glue_id)
  end.

Definition check_drop_glue (g: ident * globdef fundef type) : bool :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => true
      | None => false
      end
  | _ => false
  end.

Definition generate_dropm (p: program) :=
  let drop_glue_ids := map extract_drop_id (filter check_drop_glue p.(prog_defs)) in
  PTree_Properties.of_list drop_glue_ids.


(** * Operational Semantics  *)

(** ** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.

(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** ** Ownership environment  *)


(** Ownership environment: a pair of deep owned place set and
shallow owned place set (TODO: it should be defined in Rustlight) *)
    
(** own_env is actually init environment which is used to check
every used is initialized. Maybe we should change the name?  *)

(* may be we can use PathMap to optimize it *)
Record own_env :=
  mkown { own_init: PathsMap.t;
          own_uninit: PathsMap.t;
          own_universe: PathsMap.t } .

Definition is_owned (own: own_env) (p: place): bool :=
  let id := local_of_place p in
  let init := PathsMap.get id own.(own_init) in
  let uninit := PathsMap.get id own.(own_uninit) in
  (* no p's prefix in uninit and there is some p's prefix in init *)
  Paths.for_all (fun p' => negb (is_prefix p' p)) uninit
  && Paths.exists_ (fun p' => is_prefix p' p) init.

(* A owned place is deep owned **xor** shallow owned *)

Definition is_deep_owned (own: own_env) (p: place) : bool :=
  (* p is owned and no p's children in the universe *)
  is_owned own p &&
    let id := local_of_place p in
    let universe := PathsMap.get id own.(own_universe) in
    Paths.for_all (fun p' => negb (is_prefix_strict p p')) universe.

Definition is_shallow_owned (own: own_env) (p: place) : bool :=
  is_owned own p &&
    (* There is some p's children in the universe, which means that
    p's ownership may be split. So we only consider p as a partial
    owned place *)
    let id := local_of_place p in
    let universe := PathsMap.get id own.(own_universe) in
    Paths.exists_ (fun p' => is_prefix_strict p p') universe.

(* check that parents of p are not in uninit (slightly different from
   the condition in is_owned) *)
Definition prefix_is_owned (own: own_env) (p: place) : bool :=
  forallb (is_owned own) (parent_paths p).
  (* let id := local_of_place p in *)
  (* let uninit := PathsMap.get id own.(own_uninit) in *)
  (* (* no p's prefix in uninit *) *)
  (* Paths.for_all (fun p' => negb (is_prefix_strict p' p)) uninit. *)

Lemma prefix_owned_implies: forall p p' own,
    prefix_is_owned own p = true ->
    is_prefix_strict p' p = true ->
    is_owned own p' = true.
Proof.
  intros p p' own POWN PFX.
  eapply forallb_forall in POWN; eauto.
  eapply proj_sumbool_true in PFX. auto.
Qed.  
  
(* place with succesive Pdowncast in the end is not a valid owner. For
example, move (Pdowncast p) is equivalent to move p *)
Fixpoint valid_owner (p: place) :=
  match p with
  | Pdowncast p' _ _ => valid_owner p'
  | _ => p
  end.

Definition check_movable (own: own_env) (p: place) : bool :=
  (* the place itself and its children are all owned *)
  let id := local_of_place p in
  let universe := PathsMap.get id (own_universe own) in  
  Paths.for_all (is_owned own) (Paths.filter (is_prefix p) universe).


Fixpoint own_check_pexpr (own: own_env) (pe: pexpr) : bool :=
  match pe with
  | Eplace p _
  | Ecktag p _
  | Eref _ _ p _ =>
      (* we only check p which represents/owns a memory location *)
      if place_owns_loc p then
        (* copy/reference a place also requires that the place is
        movable (all its children are owned, otherwise it is not
        memory safe because the unowned block may be deallocated *)
        check_movable own p
      else
        (* This checking is left for borrow checker *)
        true
  | Eunop _ pe _ =>
      own_check_pexpr own pe
  | Ebinop _ pe1 pe2 _ =>
      own_check_pexpr own pe1 && own_check_pexpr own pe2
  | _ => true
end.          

Definition move_place (own: own_env) (p: place) : own_env :=
  (mkown (remove_place p own.(own_init))
     (add_place own.(own_universe) p own.(own_uninit))
     own.(own_universe)).


(* Move to Rustlight: Check the ownership of expression *)
Definition own_check_expr (own: own_env) (e: expr) : option own_env :=
  match e with
  | Emoveplace p ty =>
      (** FIXME: when to use valid_owner? *)
      let p := valid_owner p in
      if check_movable own p then
        (* consider [a: Box<Box<Box<i32>>>] and we move [*a]. [a] becomes
        partial owned *)
        (* remove p from init and add p and its children to uninit *)
        Some (move_place own p)
      else
        (* Error! We must move a movable place! *)
        None
  | Epure pe =>
      if own_check_pexpr own pe then
        Some own
      else None
  end.

Fixpoint own_check_exprlist (own: own_env) (l: list expr) : option own_env :=
  match l with
  | nil => Some own
  | e :: l' =>
      match own_check_expr own e with
      | Some own1 =>
          own_check_exprlist own1 l'
      | None => None
      end
  end.

(* The dominator of a place [p]: the place's demonator decide the
location of this place *)

Fixpoint place_dominator (p: place) : option place :=
  match p with
  | Pderef p' _ => Some p'
  | Pfield p' _ _ => place_dominator p'
  | Pdowncast p' _ _ => Some p'
  | Plocal _ _ => None
  end.

(* A place's dominator is owned means that this place is the owner of
the location it resides in *)
Definition place_dominator_own (own: own_env) (p: place) : bool :=
  match place_dominator p with
  | Some p' => is_owned own p'
  | None => true
  end.

(* We can use the following function to ensure that the block place
[p] resides in is in the domain of abstracter *)
Definition place_dominator_shallow_own (own: own_env) (p: place) : bool :=
  match place_dominator p with
  | Some p' => is_shallow_owned own p'
  | None => true
  end.


(* Update the ownership environment when assigning to p. We must
ensure that p is not deeply owned because p must be dropped before
this assignment. *)
Definition own_check_assign (own: own_env) (p: place) : option own_env :=
  (* check that the dominator of p is owned (initialized) because we
  need to compute the address of [p] *)
  if place_dominator_own own p then
    Some (mkown (add_place own.(own_universe) p own.(own_init))
            (remove_place p own.(own_uninit))
            own.(own_universe))
  else
    None.             

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
      complete_type ce ty = true ->
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
| eval_Pfield_struct: forall p ty b ofs delta id i co orgs,
    eval_place p b ofs ->
    typeof_place p = Tstruct orgs id ->
    ce ! id = Some co ->
    field_offset ce i (co_members co) = OK delta ->
    eval_place (Pfield p i ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
| eval_Pdowncast: forall  p ty b ofs fofs id fid fty co orgs tag,
    eval_place p b ofs ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    (* check tag and fid *)
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
    variant_field_offset ce fid (co_members co) = OK fofs ->
    (* fty and ty must be equal? *)
    eval_place (Pdowncast p fid ty) b (Ptrofs.add ofs (Ptrofs.repr fofs))
| eval_Pderef: forall p ty l ofs l' ofs',
    eval_place p l ofs ->
    deref_loc (typeof_place p) m l ofs (Vptr l' ofs') ->
    eval_place (Pderef p ty) l' ofs'.

Inductive eval_place_mem_error : place -> Prop :=
| eval_Pfield_error: forall p ty i,
    eval_place_mem_error p ->
    eval_place_mem_error (Pfield p i ty)
| eval_Pdowncast_error1: forall p ty fid,
    eval_place_mem_error p ->
    eval_place_mem_error (Pdowncast p fid ty)
| eval_Pdowncast_error2: forall p ty fid b ofs,
    eval_place p b ofs ->
    ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    eval_place_mem_error (Pdowncast p fid ty)
| eval_Pderef_error1: forall p ty,
    eval_place_mem_error p ->
    eval_place_mem_error (Pderef p ty)
| eval_Pderef_error2: forall p l ofs ty,
    eval_place p l ofs ->
    deref_loc_mem_error (typeof_place p) m l ofs ->
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


(** Allocate memory blocks for function parameters/variables and build
the local environment *)
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


(* Some functions used in generating initial own environment *)

Section WITH_CE.

Variable ce: composite_env.

Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign_variant p _ _ e
  | Sassign p e
  | Sbox p e =>
      collect_place ce p (collect_expr ce e m)
  | Scall p _ al =>
      collect_place ce p (collect_exprlist ce al m)
  | Sreturn (Some e) =>
      collect_expr ce e m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_stmt s1 (collect_stmt s2 (collect_expr ce e m))
  | Sloop s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ extract_vars f.(fn_body) in  
  if list_norepet_dec ident_eq (map fst vars) then
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    (** TODO: add all the parameters and variables to l (may be useless?) *)
    let init_map := fold_right (collect_place ce) (PTree.empty LPaths.t) l in
    Errors.OK (collect_stmt f.(fn_body) init_map)
  else
    Errors.Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil).

End WITH_CE.

(* copy from init analysis *)
Definition init_own_env (ce: composite_env) (f: function) : Errors.res own_env :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let init := fold_right (add_place whole) empty_pathmap pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) (extract_vars f.(fn_body)) in
  let uninit := fold_right (add_place whole) empty_pathmap vl in
  OK (mkown init uninit whole).

(* Use extract_vars to extract the local variables *)

Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (m2: mem) (own: own_env) : Prop :=
| function_entry_intro: forall m1 vars
    (VARS: vars = extract_vars f.(fn_body))
    (NOREP: list_norepet (var_names f.(fn_params) ++ var_names vars))
    (ALLOC: alloc_variables ge empty_env m (f.(fn_params) ++ vars) e m1)
    (BIND: bind_parameters ge e m1 f.(fn_params) vargs m2)
    (* initialize own_env *)
    (INITOWN: init_own_env ge f = OK own),
    function_entry ge f vargs m e m2 own.


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
         
| step_assign_variant: forall f e (p: place) ty op k le own own' own'' m1 m2 m3 m4 b ofs ofs' v tag co id fid enum_id  orgs,
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
    field_offset ge fid co.(co_members) = OK ofs' ->
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

