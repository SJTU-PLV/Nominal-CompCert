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
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LanguageInterface.
Require Import InitDomain.

Local Open Scope error_monad_scope.
Import ListNotations.

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

(** TODO: add some properties in own_env such as init ∪ unint =
universe, init ∩ uninit = ∅ and etc *)
Record own_env :=
  mkown { own_init: PathsMap.t;
          own_uninit: PathsMap.t;
          own_universe: PathsMap.t;

          (* algebraic properties of own_env *)
          own_consistent: forall id,
            LPaths.eq (Paths.union (PathsMap.get id own_init) (PathsMap.get id own_uninit)) (PathsMap.get id own_universe);
          own_disjoint: forall id,
            LPaths.eq (Paths.inter (PathsMap.get id own_init) (PathsMap.get id own_uninit)) Paths.empty;
          (* ∀ p ∈ W, p ∈ I → ∀ p' ∈ W, is_prefix p' p → p' ∈ I *)
          own_wf_init: forall (p: place),
            let id := local_of_place p in
            let init := PathsMap.get id own_init in
            let universe := PathsMap.get id own_universe in
            Paths.For_all (fun p => if Paths.mem p init
                                 then Paths.For_all (fun p' => if is_prefix p' p then Paths.mem p' init = true else True) universe
                                 else True) universe;

          (* ∀ p ∈ W, p ∈ U → ∀ p' ∈ W, is_prefix p p' → p' ∈ U *)
          own_wf_uninit: forall (p: place),
            let id := local_of_place p in
            let uninit := PathsMap.get id own_uninit in
            let universe := PathsMap.get id own_universe in
            Paths.For_all (fun p => if Paths.mem p uninit
                                 then Paths.For_all (fun p' => if is_prefix p p' then Paths.mem p' uninit = true else True) universe
                                 else True) universe;

    }.

Definition is_owned (own: own_env) (p: place): bool :=
  let id := local_of_place p in
  let init := PathsMap.get id own.(own_init) in
  let universe := PathsMap.get id own.(own_universe) in
  (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mustinit *)
  Paths.for_all (fun p' => Paths.mem p' init)
    (Paths.filter (fun p' => is_prefix p' p) universe).

(** Unused: A owned place is deep owned **xor** shallow owned *)

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
  

Program Definition move_place (own: own_env) (p: place) : own_env :=
  {| own_init := (remove_place p own.(own_init));
    own_uninit := (add_place own.(own_universe) p own.(own_uninit));
    own_universe := own.(own_universe) |}.
Next Obligation.
  destruct own. simpl.
  unfold remove_place, add_place.
  clear own_disjoint0 own_wf_init0 own_wf_uninit0.
  generalize (own_consistent0 id). intros WP.
  set (pid := (local_of_place p)) in *.
  do 2 erewrite PathsMap.gsspec.
  destruct (peq id pid).
  - subst.    
    red. red. intros.
    set (I := (PathsMap.get pid own_init0)) in *.
    set (U := (PathsMap.get pid own_uninit0)) in *.
    set (W := (PathsMap.get pid own_universe0)) in *.
    split.
    + intros IN.
      eapply WP. 
      eapply Paths.union_1 in IN. destruct IN as [IN1 | IN2].
      * eapply Paths.filter_1 in IN1.
        eapply Paths.union_2.
        auto.        
        red. Morphisms.solve_proper.
      * eapply Paths.union_1 in IN2. destruct IN2 as [IN3 | IN4].
        -- eapply Paths.union_3. auto.
        -- eapply Paths.filter_1 in IN4.
           eapply WP. auto.
           red. Morphisms.solve_proper.
    + intros IN.
      eapply WP in IN. eapply Paths.union_1 in IN.
      destruct IN as [IN1 | IN2].
      * destruct (negb (is_prefix p a)) eqn: FL.
        -- eapply Paths.union_2.
           eapply Paths.filter_3; auto.
           red. Morphisms.solve_proper.
        -- eapply Paths.union_3. eapply Paths.union_3.
           eapply negb_false_iff in FL.
           eapply Paths.filter_3; auto.
           red. Morphisms.solve_proper.
           eapply WP. eapply Paths.union_2. auto.
      * eapply Paths.union_3.
        eapply Paths.union_2. auto.
  - auto.
Defined.           
Next Obligation.
  destruct own. simpl.
  unfold remove_place, add_place.
  clear own_wf_init0 own_wf_uninit0.
  set (pid := (local_of_place p)) in *.
  generalize (own_disjoint0 pid). intros DIS.
  generalize (own_consistent0 pid). intros CON.
  do 2 erewrite PathsMap.gsspec.
  destruct (peq id pid).
  - subst. red. red. intros.    
    split.
    + intros IN. exfalso.
      eapply Paths.empty_1. eapply DIS.
      instantiate (1 := a).
      eapply Paths.inter_3.
      * eapply Paths.inter_1 in IN.
        eapply Paths.filter_1 in IN. auto.
        red. Morphisms.solve_proper.
      * exploit Paths.inter_1;eauto. intros IN1.
        exploit Paths.inter_2;eauto. intros IN2.
        eapply Paths.union_1 in IN2.
        destruct IN2 as [IN3|IN4].
        -- auto.
        (* IN1 and IN4 are contradict *)
        -- eapply Paths.filter_2 in IN1.
           eapply Paths.filter_2 in IN4.
           rewrite IN4 in IN1. simpl in IN1. congruence.
           red. Morphisms.solve_proper.
           red. Morphisms.solve_proper.
    + intros IN. exfalso.
      eapply Paths.empty_1. eauto.
  - auto.
Defined.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
  
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


(* initialize a place *)
Program Definition init_place (own: own_env) (p: place) : own_env :=
  {| own_init := (add_place own.(own_universe) p own.(own_init));
    own_uninit := (remove_place p own.(own_uninit));
    own_universe := own.(own_universe) |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.


(* Update the ownership environment when assigning to p. We must
ensure that p is not deeply owned because p must be dropped before
this assignment. *)
Definition own_check_assign (own: own_env) (p: place) : option own_env :=
  (* check that the dominator of p is owned (initialized) because we
  need to compute the address of [p] *)
  if place_dominator_own own p then
    Some (init_place own p)
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

(** Some definitions of dropplace and dropstate *)


(** Substate for member drop *)
Inductive drop_member_state : Type :=
| drop_member_comp
    (fid: ident)
    (fty: type)
    (co_ty: type)
    (tys: list type): drop_member_state   
| drop_member_box
    (fid: ident)
    (fty: type)
    (tys: list type): drop_member_state
.

Fixpoint split_fully_own_place (p: place) (ty: type) :=
  match ty with
  | Tbox ty'  =>
      split_fully_own_place (Pderef p ty') ty' ++ [p]
  | Tstruct _ _
  | Tvariant _ _  =>
      [p]
  | _ => nil
  end.


(* Drop place state *)

Inductive drop_place_state : Type :=
| drop_fully_owned_comp
    (* drop the composite and then drop the box *)
    (p: place) (l: list place) : drop_place_state
| drop_fully_owned_box
    (l: list place) : drop_place_state
.

Definition gen_drop_place_state (p: place) : drop_place_state :=
  match split_fully_own_place p (typeof_place p) with
  | nil => drop_fully_owned_box nil
  | p' :: l =>
      match typeof_place p' with
      | Tstruct _ _
      | Tvariant _ _ =>
          drop_fully_owned_comp p' l
      | _ =>
          drop_fully_owned_box (p' :: l)
      end
  end.
          
(** Continuation *)


(* TODO: use some kbreak, kcontinue and kassign etc to record the stmt
after drop. lots of drops before break and continue can be extracted
from continuation *)

(* The action actually need to do after the inserted drop *)
Inductive dropcont : Type :=
(* for [p := q], we insert drop(p) to get [drop(p); p:=q] and the
assignment after this drop is recorde in this Dassign *)
| Dassign: place -> expr -> dropcont
| Dassign_variant : place -> ident -> ident -> expr -> dropcont
| Dbreak
| Dcontinue
(* Dreturn records the return value *)
| Dreturn: val -> dropcont
| Dendlet
.

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: option place -> function -> env -> own_env -> cont -> cont
| Kdropinsert: list place -> dropcont -> cont -> cont
(* used to record Dropplace state *)
| Kdropplace: function -> option drop_place_state -> list (place * bool) -> env -> own_env -> cont -> cont
| Kdropcall: ident -> val -> option drop_member_state -> members -> cont -> cont
| Klet: ident -> type -> cont -> cont
.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq _ k
  | Kloop _ k
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k
  | Kdropinsert _ _ k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(* compute to drop places from continuation: simulate vars in
transl_stmt in RustIRgen *)

Fixpoint cont_vars (k: cont) : list (list (ident * type)) :=
  match k with
  | Klet id ty k1 =>
      list_list_cons (id, ty) (cont_vars k1)
  | Kloop _ k1 =>
      [] :: cont_vars k1
  | Kseq _ k1
  | Kcall _ _ _ _ k1
  | Kdropinsert _ _ k1
  | Kdropcall _ _ _ _ k1
  | Kdropplace _ _ _ _ _ k1 =>
      cont_vars k1
  | Kstop =>
      []
  end.

Definition vars_to_drops ce (vars: list (ident * type)) : list place :=
  map (fun elt => Plocal (fst elt) (snd elt)) (filter (fun elt => own_type ce (snd elt)) vars).

(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (m: mem) : state
(* Simulate drop inertion *)
| Dropinsert
    (f: function)    
    (l: list place)
    (dk: dropcont)
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
(* Simulate elaborate drop *)
| Dropplace
    (f: function)
    (s: option drop_place_state)
    (l: list (place * bool))
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Dropstate
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (m: mem): state
.


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
Program Definition init_own_env (ce: composite_env) (f: function) : Errors.res own_env :=
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
  OK {| own_init := init;
       own_uninit := uninit;
       own_universe := whole |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.



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


Section DROPMEMBER.

Variable ge: genv.

(** Some definitions for dropstate and dropplace *)
(* list of ownership types which are the children of [ty] *)
Fixpoint drop_glue_children_types (ty: type) : list type :=
  match ty with
  | Tbox ty' =>
      drop_glue_children_types ty' ++ [ty]
  | Tstruct _ id 
  | Tvariant _ id  => ty::nil
  | _ => nil
  end.

(* It corresponds to drop_glue_for_member in Clightgen *)
Definition type_to_drop_member_state (fid: ident) (fty: type) : option drop_member_state :=
  if own_type ge fty then
    let tys := drop_glue_children_types fty in
    match tys with
    | nil => None
    | ty :: tys' =>
        match ty with       
        | Tvariant _ id
        | Tstruct _ id =>
            (* provide evidence for the simulation *)
            match ge.(genv_dropm) ! id with
            | Some _ =>
                Some (drop_member_comp fid fty ty tys')
            | None => None
            end
        | _ => Some (drop_member_box fid fty tys)
        end
    end
  else None.

(* Load the value of [ty1] with the address of the starting block
(with type ty_k) from [ty1;ty2;ty3;...;ty_k] where ty_n points to
ty_{n-1} *)
Inductive deref_loc_rec (m: mem) (b: block) (ofs: ptrofs) : list type -> val -> Prop :=
| deref_loc_rec_nil:
    deref_loc_rec m b ofs nil (Vptr b ofs)
| deref_loc_rec_cons: forall ty tys b1 ofs1 v,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 v ->
    deref_loc_rec m b ofs (ty::tys) v
.

Inductive deref_loc_rec_mem_error (m: mem) (b: block) (ofs: ptrofs) : list type -> Prop :=
| deref_loc_rec_error1: forall ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
| deref_loc_rec_error2: forall ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc_mem_error ty m b ofs ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
.


(* big step to recursively drop boxes [Tbox (Tbox (Tbox
...))]. (b,ofs) is the address of the starting block *)
Inductive drop_box_rec (b: block) (ofs: ptrofs) : mem -> list type -> mem -> Prop :=
| drop_box_rec_nil: forall m,
    drop_box_rec b ofs m nil m
| drop_box_rec_cons: forall m m1 m2 b1 ofs1 ty tys,
    (* (b1, ofs1) is the address of [ty] *)
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m (ty :: tys) m2
.

Inductive extcall_free_sem_mem_error: val -> mem -> Prop :=
| free_error1: forall (b : block) (lo : ptrofs) (m : mem),
    ~ Mem.valid_access m Mptr b (Ptrofs.unsigned lo - size_chunk Mptr) Readable ->
    extcall_free_sem_mem_error (Vptr b lo) m
| free_error2: forall (b : block) (lo sz : ptrofs) (m m' : mem),
    Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
    Ptrofs.unsigned sz > 0 ->
    ~ Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable ->
    extcall_free_sem_mem_error (Vptr b lo) m.


Inductive drop_box_rec_mem_error (b: block) (ofs: ptrofs) : mem -> list type -> Prop :=
| drop_box_rec_error1: forall m ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error2: forall m ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem_mem_error (Vptr b1 ofs1) m -> 
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error3: forall m m1 ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec_mem_error b ofs m1 tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
.

End DROPMEMBER.

Section SMALLSTEP.

Variable ge: genv.
  
(* Mostly the same as RustIRsem *)
Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) membs k m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (STRUCT: co2.(co_sv) = Struct),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fid2 fty2 fofs tag orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr cb cofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co2.(co_members) (Int.unsigned tag) = Some (Member_plain fid2 fty2)),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state ge fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) m)
| step_dropstate_box: forall b ofs id co fid fofs m m' tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (DROPB: drop_box_rec ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m) E0
      (Dropstate id (Vptr b ofs) None membs k m')
| step_dropstate_return1: forall b ofs id m f e own k ps s,
    step_drop
      (* maybe we should separate step_dropstate_return to reuse
      step_drop because of the mismatch between Kdropplace and Kcall
      in RustIRown and RUstIRsem *)
      (Dropstate id (Vptr b ofs) None nil (Kdropplace f s ps e own k) m) E0
      (Dropplace f s ps k e own m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k m)
.


Inductive step_drop_mem_error : state -> Prop :=
| step_dropstate_struct_error: forall id1 id2 co1 b1 ofs1 tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m)
| step_dropstate_enum_error1: forall id1 id2 co1 b1 ofs1 tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
    (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)
| step_dropstate_enum_error2: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* error in loading the tag *)
    (TAG: ~ Mem.valid_access m Mint32 cb (Ptrofs.unsigned cofs) Readable),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)      
| step_dropstate_box_error: forall b ofs id co fid fofs m tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (* error in dropping the box chain *)
    (DROPB: drop_box_rec_mem_error ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys),
    step_drop_mem_error
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m)
.


Inductive step_dropplace : state -> trace -> state -> Prop :=
| step_dropplace_init1: forall f p ps k le own m full
    (* p is not owned, so just skip it (How to relate this case with
    RustIRsem because drop elaboration removes this place earlier in
    generate_drop_flag) *)
    (NOTOWN: is_owned own p = false),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f None ps k le own m)
| step_dropplace_init2: forall f p ps k le own m st (full: bool)
    (OWN: is_owned own p = true)
    (DPLACE: st = (if full then gen_drop_place_state p else drop_fully_owned_box [p])),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f (Some st) ps k le (move_place own p) m)
| step_dropplace_box: forall le m m' k ty b' ofs' f b ofs p own ps l
    (* simulate step_drop_box in RustIRsem *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    (* We are dropping p. fp is the fully owned place which is split into p::l *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m) E0
      (Dropplace f (Some (drop_fully_owned_box l)) ps k le own m')
| step_dropplace_struct: forall m k orgs co id p b ofs f le own ps l
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: eval_place ge le m p b ofs),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kdropplace f (Some (drop_fully_owned_box l)) ps le own  k) m)
| step_dropplace_enum: forall m k p orgs co id fid fty tag b ofs f le own ps l
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) nil (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) m)
| step_dropplace_next: forall f ps k le own m,
    step_dropplace (Dropplace f (Some (drop_fully_owned_box nil)) ps k le own m) E0
      (Dropplace f None ps k le own m)
(* return to the dropinsert state because all the dropplace states
come from dropinsert *)
| step_dropplace_return: forall f k le own m l dk,
    step_dropplace (Dropplace f None nil (Kdropinsert l dk k) le own m) E0
      (Dropinsert f l dk k le own m)
.


Inductive step_dropplace_mem_error: state -> Prop :=
| step_dropplace_box_error1: forall le m k f p own ps l
    (* eval_place error *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error2: forall le m k f p own ps l b ofs ty
    (* deref_loc error *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc_mem_error (Tbox ty) m b ofs),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error3: forall le m k f p own ps l b ofs ty b' ofs'
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* free error *)
    (FREE: extcall_free_sem_mem_error (Vptr b' ofs') m),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_comp_error: forall m k p f le own ps l
    (* p is struct or enum *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) 
.


(* small step in dropinsert *)
Inductive step_dropinsert : state -> trace -> state -> Prop :=
(* simulate step_to_dropplace in RustIRown *)
| step_dropinsert_to_dropplace: forall f p le own m drops k universe dk l
    (UNI: own.(own_universe) ! (local_of_place p) = Some universe)
    (SPLIT: split_drop_place ge universe p (typeof_place p) = OK drops),
    (* get the owned place to drop *)
    step_dropinsert (Dropinsert f (p::l) dk k le own m) E0
      (Dropplace f None drops (Kdropinsert l dk k) le own m)
| step_dropinsert_assign: forall f e p k le m1 m2 b ofs v v1 own1 own2 own3
    (* check ownership *)
    (CHKEXPR: own_check_expr own1 e = Some own2)
    (CHKASSIGN: own_check_assign own2 p = Some own3)
    (TYP: forall orgs id, typeof_place p <> Tvariant orgs id),
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    step_dropinsert (Dropinsert f [] (Dassign p e) k le own1 m1) E0
                    (State f Sskip k le own3 m2)
| step_dropinsert_assign_variant: forall f e p ty k le m1 m2 m3 b ofs b1 ofs1 v v1 tag co fid enum_id orgs own1 own2 own3 fofs
    (* check ownership *)
    (CHKEXPR: own_check_expr own1 e = Some own2)
    (CHKASSIGN: own_check_assign own2 p = Some own3)
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (* evaluate the expr, return the value *)
    (EXPR: eval_expr ge le m1 e v)
    (* evaluate the location of the variant in p (in memory m1) *)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* sem_cast to simulate Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* set the value *)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (** different from normal assignment: update the tag and assign value *)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (* eval the location of the tag: to simulate the target statement:
    because we cannot guarantee that store value in m1 does not change    the address of p! (Non-interference is a difficult problem!) *)
    (PADDR2: eval_place ge le m2 p b1 ofs1)
    (* set the tag *)
    (STAG: Mem.storev Mint32 m2 (Vptr b1 ofs1) (Vint (Int.repr tag)) = Some m3),
    step_dropinsert (Dropinsert f [] (Dassign_variant p enum_id fid e) k le own1 m1) E0 (State f Sskip k le own3 m3)
| step_dropinsert_break_seq: forall f s k le own m,
    step_dropinsert (Dropinsert f [] Dbreak (Kseq s k) le own m) E0
      (Dropinsert f [] Dbreak k le own m)
| step_dropinsert_break_let: forall f k le own m id ty,
    (* this variable has been dropped when we meet the break statement *)
    step_dropinsert (Dropinsert f [] Dbreak (Klet id ty k) le own m) E0
      (Dropinsert f [] Dbreak k le own m)
| step_dropinsert_break_loop: forall f s k le own m,
    step_dropinsert (Dropinsert f [] Dbreak (Kloop s k) le own m) E0
      (State f Sskip k le own m)
| step_dropinsert_continue_seq: forall f s k le own m,
    step_dropinsert (Dropinsert f [] Dcontinue (Kseq s k) le own m) E0
      (Dropinsert f [] Dcontinue k le own m)
| step_dropinsert_continue_let: forall f k le own m id ty,
    step_dropinsert (Dropinsert f [] Dcontinue (Klet id ty k) le own m) E0
      (Dropinsert f [] Dcontinue k le own m)
| step_dropinsert_continue_loop: forall f s k le own m,
    step_dropinsert (Dropinsert f [] Dcontinue (Kloop s k) le own m) E0
      (State f s (Kloop s k) le own m)
| step_dropinsert_return: forall f v k le own m1 m2 lb,
    (* free stack blocks *)
    blocks_of_env ge le = lb ->
    Mem.free_list m1 lb = Some m2 ->    
    step_dropinsert (Dropinsert f [] (Dreturn v) k le own m1) E0
      (Returnstate v (call_cont k) m2)
| step_dropinsert_endlet: forall f k le own m,
    step_dropinsert (Dropinsert f [] Dendlet k le own m) E0
      (State f Sskip k le own m)
.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m drops own
    (GENDROP: drops = if own_type ge (typeof_place p) then [p] else []),
    step (State f (Sassign p e) k le own m) E0 (Dropinsert f drops (Dassign p e) k le own m)
| step_assign_variant: forall f e p k le m drops own enum_id fid
    (GENDROP: drops = if own_type ge (typeof_place p) then [p] else []),
    step (State f (Sassign_variant p enum_id fid e) k le own m) E0 (Dropinsert f drops (Dassign_variant p enum_id fid e) k le own m)         
| step_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs own1 own2 own3
    (* check ownership *)
    (CHKEXPR: own_check_expr own1 e = Some own2)
    (CHKASSIGN: own_check_assign own2 p = Some own3),
    typeof_place p = Tbox ty ->
    (* Simulate malloc semantics to allocate the memory block *)
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* evaluate the expression after malloc to simulate*)
    eval_expr ge le m3 e v ->
    (* sem_cast the value to simulate function call in Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (* assign the value to the allocated location *)
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* assign the address to p *)
    eval_place ge le m4 p pb pofs ->
    assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5 ->
    step (State f (Sbox p e) k le own1 m1) E0 (State f Sskip k le own3 m5)
| step_let: forall f ty id own m k s le,
    step (State f (Slet id ty s) k le own m) E0 (State f s (Klet id ty k) le own m)
(* End of a let statement, drop the place *)
| step_end_let: forall f id ty k le m drops own
    (GENDROP: drops = if own_type ge ty then [Plocal id ty] else []),
    step (State f Sskip (Klet id ty k) le own m) E0 (Dropinsert f drops Dendlet k le own m)

(** dynamic drop semantics: simulate the drop elaboration *)
| step_in_dropinsert: forall f l dk k le own m E S
    (SDROP: step_dropinsert (Dropinsert f l dk k le own m) E S),
    step (Dropinsert f l dk k le own m) E S
| step_in_dropplace: forall f s ps k le own m E S
    (SDROP: step_dropplace (Dropplace f s ps k le own m) E S),
    step (Dropplace f s ps k le own m) E S
| step_dropstate: forall id v s membs k m S E
    (SDROP: step_drop (Dropstate id v s membs k m) E S),
    step (Dropstate id v s membs k m) E S

| step_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels own1 own2
    (CHKEXPRLIST: own_check_exprlist own1 al = Some own2),    
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m a vf ->
    eval_exprlist ge le m al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    (* Cannot call drop glue *)
    (forall f', fd = Internal f' -> fn_drop_glue f' = None) ->
    step (State f (Scall p a al) k le own1 m) E0 (Callstate vf vargs (Kcall (Some p) f le own2 k) m)

| step_internal_function: forall vf f vargs k m e m' init_own
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry ge f vargs m e m' init_own),
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e init_own m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')

(** Return cases *)
| step_return_0: forall e f k own drops param_drops m
    (VARDROPS: drops = vars_to_drops ge (concat (cont_vars k)))
    (PARAMDROPS: param_drops = vars_to_drops ge f.(fn_params)),
    step (State f (Sreturn None) k e own m) E0 (Dropinsert f (drops++param_drops) (Dreturn Vundef) k e own m)
| step_return_1: forall le a v v1 m f k own1 own2 drops param_drops
    (CHKEXPR: own_check_expr own1 a = Some own2)
    (EXPR: eval_expr ge le m a v)
    (* sem_cast to the return type *)
    (CAST: sem_cast v (typeof a) f.(fn_return) = Some v1)
    (VARDROPS: drops = vars_to_drops ge (concat (cont_vars k)))
    (PARAMDROPS: param_drops = vars_to_drops ge f.(fn_params)),
    step (State f (Sreturn (Some a)) k le own1 m) E0 (Dropinsert f (drops++param_drops) (Dreturn v1) k le own2 m)

(* no return statement but reach the end of the function *)
| step_skip_call: forall e f k own drops param_drops m
    (CALLCONT: is_call_cont k)
    (VARDROPS: drops = vars_to_drops ge (concat (cont_vars k)))
    (PARAMDROPS: param_drops = vars_to_drops ge f.(fn_params)),
    step (State f Sskip k e own m) E0 (Dropinsert f (drops++param_drops) (Dreturn Vundef) k e own m)

| step_returnstate: forall p v b ofs ty m1 m2 e f k own1 own2
    (CHKASSIGN: own_check_assign own1 p = Some own2),
    eval_place ge e m1 p b ofs ->
    assign_loc ge ty m1 b ofs v m2 ->    
    step (Returnstate v (Kcall (Some p) f e own1 k) m1) E0 (State f Sskip k e own2 m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m own,
    step (State f (Ssequence s1 s2) k e own m)
      E0 (State f s1 (Kseq s2 k) e own m)
| step_skip_seq: forall f s k e m own,
    step (State f Sskip (Kseq s k) e own m)
      E0 (State f s k e own m)
| step_continue_insert_drops: forall f k e m own drops
    (* get the places to insert drop *)
    (DROPS: drops = vars_to_drops ge (hd nil (cont_vars k))),
    step (State f Scontinue k e own m)
      E0 (Dropinsert f drops Dcontinue k e own m)
| step_break_insert_drops: forall f k e m own drops
    (* get the places to insert drop *)
    (DROPS: drops = vars_to_drops ge (hd nil (cont_vars k))),
    step (State f Sbreak k e own m)
      E0 (Dropinsert f drops Dbreak k e own m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty own1 own2
    (CHKEXPR: own_check_expr own1 a = Some own2),
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e own1 m)
      E0 (State f (if b then s1 else s2) k e own2 m)
| step_loop: forall f s k e m own,
    step (State f (Sloop s) k e own m)
      E0 (State f s (Kloop s k) e own m)
| step_skip_loop:  forall f s k e m own,
    step (State f Sskip (Kloop s k) e own m)
      E0 (State f s (Kloop s k) e own m)
.


(** Open semantics *)

Inductive initial_state: rust_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (* This function must not be drop glue *)
    f.(fn_drop_glue) = None ->
    (* how to use it? *)
    val_casted_list vargs targs ->
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    initial_state (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs m)
      (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> rust_query -> Prop:=
| at_external_intro: forall vf name sg args k m targs tres cconv orgs org_rels,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name sg) targs tres cconv) ->
    at_external (Callstate vf args k m) (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args m).

Inductive after_external: state -> rust_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (rsr v m')
      (Returnstate v k m').

Inductive final_state: state -> rust_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (rsr v m).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.
