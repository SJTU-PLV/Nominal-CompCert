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

(** * High-level Rust-like language  *)


(** ** Place (used to build lvalue expression) *)

Inductive place : Type :=
| Plocal : ident -> type -> place
| Pfield : place -> ident -> type -> place (**r access a field of struct or union: p.(id)  *)
.

Definition typeof_place p :=
  match p with
  | Plocal _ ty => ty
  | Pfield _ _ ty => ty
  end.

(** ** Expression *)

Inductive expr : Type :=
| Econst_int: int -> type -> expr       (**r integer literal *)
| Eplace: usekind -> place -> type -> expr (**r use of a variable, the only lvalue expression *)
| Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
| Ebinop: binary_operation -> expr -> expr -> type -> expr. (**r binary operation *)


Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty 
  | Eplace _ _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty => ty
  end.


Fixpoint to_ctype (ty: type) : option Ctypes.type :=
  match ty with
  | Tunit => Some Tvoid 
  | Tint sz si attr => Some (Ctypes.Tint sz si attr)
  | Tfunction tyl ty cc =>
      match to_ctype ty, to_ctypelist tyl with
      | Some ty, Some tyl => Some (Ctypes.Tfunction tyl ty cc)
      | _, _ => None
      end
  | Tstruct id attr => Some (Ctypes.Tstruct id attr)
  | Tunion id attr => Some (Ctypes.Tunion id attr)
  end
    
with to_ctypelist (tyl: typelist) : option (Ctypes.typelist) :=
       match tyl with
       | Tnil => Some (Ctypes.Tnil)
       | Tcons ty tyl =>
           match to_ctype ty, to_ctypelist tyl with
           | Some ty, Some tyl => Some (Ctypes.Tcons ty tyl)
           | _, _ => None
           end
       end.
                                    

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Slet : ident -> type -> expr -> statement -> statement (**r let ident: type = rvalue in *)
  | Sassign : place -> expr -> statement (**r assignment [place = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call, p = f(...). It is a abbr. of let p = f() in *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement.      (**r [return] statement *)


Record function : Type := mkfunction {
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
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal _ fd => type_of_function fd
  | External _ ef typs typ cc =>     
      Tfunction typs typ cc                
  end.


(** * Operational Semantics  *)


(** ** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.


Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env function) |}.


(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** ** Ownership environment  *)

Definition own_env := PTree.t (list place).

Definition empty_own_env : own_env := PTree.empty (list place).

(** access mode for Rust types  *)
Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tunit => By_nothing
  | Tfunction _ _ _ => By_reference
  | Tstruct _ _ => By_copy
  | Tunion _ _ => By_copy
end.

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


(** Assign a value to a location  *)

Inductive assign_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (* consider a = b ( a and b are struct ) *)
      (* evaluate b is (Vptr b' ofs'), evaluate a is (b,ofs) *)      
      (sizeof ty > 0 -> (alignof_blockcopy ty | Ptrofs.unsigned ofs')) ->
      (sizeof ty > 0 -> (alignof_blockcopy ty | Ptrofs.unsigned ofs)) ->
      (* a and b are disjoint or equal *)
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs' + sizeof ty <= Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs + sizeof ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ty m b ofs (Vptr b' ofs') m'.

(** Prefix of a place  *)

Fixpoint is_prefix (p1 p2: place) : bool :=
  match p1, p2 with
  | Plocal id1 _, Plocal id2 _ => Pos.eqb id1 id2
  | Plocal id1 _, Pderef p2' _ => is_prefix p1 p2'
  | Pderef p1' _, Pderef p2' _ => is_prefix p1' p2'
  | _ ,_ => false
  end.

Definition is_prefix_strict (p1 p2: place) : bool :=
  match p2 with
  | Plocal _ _ => false
  | Pderef p2' _  => is_prefix p1 p2'
  end.

Fixpoint local_of_place (p: place) :=
  match p with
  | Plocal id _ => id
  | Pderef p' _ => local_of_place p'
  end.


Definition erase_init_paths (ie: init_env) (p: place) : option init_env :=
  let id := local_of_place p in
  match PTree.get id ie with
  | Some init_path =>
      let erased := filter (fun p1 => negb (is_prefix p p1)) init_path in
      Some (PTree.set id erased ie)
  | None => None
  end.

Definition uninit_env (ie: init_env) (op: option place) : option init_env :=
  match op with
  | Some p =>
      match typeof_place p with
      | Tbox _ => erase_init_paths ie p
      | Treference _ Mutable _ => erase_init_paths ie p
      | _ => Some ie
      end
  | _ => Some ie
  end.

Fixpoint uninit_env_list (ie: init_env) (opl: list (option place)) : option init_env :=
  match opl with
  | op::opl' =>
      match uninit_env ie op with
      | Some ie' => uninit_env_list ie' opl'
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
  | Tfunction args res cc => fun_case_f args res cc
  (** TODO: do we allow function pointer?  *)
  (* | Treference (Tfunction args res cc) _ => fun_case_f args res cc *)
  | _ => fun_default
  end.
  
Section SEMANTICS.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable m: mem.

(* similar to eval_lvalue in Clight.v *)
Inductive eval_place : place -> block -> ptrofs -> Prop :=
| eval_Plocal: forall id l ty,
    (** TODO: there is no global variable, so we do not consider the
    gloabl environment *)
    e!id = Some (l, ty) ->
    eval_place (Plocal id ty) l Ptrofs.zero
| eval_Pderef: forall p ty l ofs l' ofs',
    eval_place p l ofs ->
    deref_loc ty m l ofs (Vptr l' ofs') ->
    eval_place (Pderef p ty) l' ofs'.

(* eval_expr would produce a pair (v, op). Here [op] has type [Option
place], if [op] is equal to [Some p], it means that this expression is
a xvalue expression and the [p] is the place to be moved from.  *)

Inductive eval_expr : expr -> val -> option place ->  Prop :=
| eval_Econst_int:   forall i ty,
    eval_expr (Econst_int i ty) (Vint i) None
| eval_Eunop:  forall op a ty v1 v aty mp,
    eval_expr a v1 mp ->
    (* Note that to_ctype Tbox = None *)
    to_ctype (typeof a) = Some aty ->
    sem_unary_operation op v1 aty m = Some v ->
    eval_expr (Eunop op a ty) v mp
(* undecided global environment *)
(** TODO: remove the composite_env in sem_binary_operation *)
(* | eval_Ebinop: forall op a1 a2 ty v1 v2 v ty1 ty2, *)
(*     eval_expr a1 v1 -> *)
(*     eval_expr a2 v2 -> *)
(*     to_ctype (typeof a1) = Some ty1 -> *)
(*     to_ctype (typeof a2) = Some ty2 -> *)
(*     sem_binary_operation ge op v1 ty1 v2 ty2 m = Some v -> *)
(*     eval_expr (Ebinop op a1 a2 ty) v. *)
| eval_Eplace_copy: forall p b ofs ty m v,
    eval_place p b ofs ->
    deref_loc ty m b ofs v ->
    eval_expr (Eplace Copy p ty) v None
| eval_Eplace_move: forall p b ofs ty m v,
    eval_place p b ofs ->
    deref_loc ty m b ofs v ->
    (* Old design: clear the move environment in the evaluation of expression
    (* (* Before move out a place, we should ensure that it is legal to move it *) *)
    (* legal_move p = true -> *)
    (* (* erase {p, *p, **p, ...} in the move env because after being *)
    (* moved out, [p] no longer owns the location it points to *) *)
    (* erase_move_paths me p = Some me' -> *) *)
    eval_expr (Eplace Move p ty) v (Some p)
| eval_Eref: forall p b ofs mut ty,
    eval_place p b ofs ->
    eval_expr (Eplace mut p ty) (Vptr b ofs) None.

Inductive eval_exprlist : list expr -> typelist -> list val -> list (option place) -> Prop :=
| eval_Enil:
  eval_exprlist nil Tnil nil nil
| eval_Econs:   forall a bl ty tyl v1 v2 vl op opl,
    (* For now, we does not allow type cast *)
    typeof a = ty ->
    eval_expr a v1 op ->
    (* sem_cast v1 (typeof a) ty m = Some v2 -> *) 
    eval_exprlist bl tyl vl opl ->
    eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl) (op :: opl).

Inductive eval_boxexpr : boxexpr -> val -> option place -> mem -> Prop :=
| eval_Rexpr: forall e v op,
    eval_expr e v op ->
    eval_boxexpr (Bexpr e) v op m
| eval_Rbox: forall r v op m' m'' m''' b ty chunk,
    typeof_boxexpr r = ty ->
    eval_boxexpr r v op m' ->
    Mem.alloc m' 0 (sizeof ty) = (m'', b) ->
    access_mode ty = By_value chunk ->
    Mem.store chunk m'' b 0 v = Some m''' ->
    eval_boxexpr (Box r) (Vptr b Ptrofs.zero) op m'''.


End EXPR.




(** Continuations *)

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Klet: ident -> cont -> cont
| Kloop1: statement -> statement -> cont -> cont
| Kloop2: statement -> statement -> cont -> cont
| Kcall: option ident  -> function -> env -> init_env -> cont -> cont.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
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
      (ie: init_env)
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



(** Drop the owned chain of the place [p] until it meets an unowned
type or the place is not in the drop obligations. For example, if
there is a chain "[p] -own-> [*p] -own-> [**p] -mut-> [***p] -own->
[****p]", and the initialized env for [p] is {p, *p, **p, ***p}, then
drop_place' would drop the location pointed by [p] and [*p] because
[**p] is not an owned pointer. *)
Inductive drop_place' (owned: list place) (p: place) (m: mem) (b: block) (ofs: ptrofs) : mem -> Prop :=
| drop_base: forall ty,
    typeof_place p = ty ->
    (* It is not of type [Tbox] *)
    not_owned_type ty = true ->
    drop_place' owned p m b ofs m
| drop_not_own: forall ty,
    not_owned_type ty = false ->
    (* Although p has type [Tbox], p has been moved out *)
    not (In p owned) ->
    drop_place' owned p m b ofs m
| drop_box: forall ty ty' m' m'' b' ofs',
    not_owned_type ty = false ->
    deref_type ty = Some ty' ->
    (* p owns the location it points to *)
    In p owned ->
    (* The contents in [p] is (Vptr b' ofs') *)
    Mem.load Mptr m b (Ptrofs.signed ofs) = Some (Vptr b' ofs') ->
    drop_place' owned (Pderef p ty') m b' ofs' m' ->
    (* Free the contents in (b',ofs') *)
    Mem.free m' b' (Ptrofs.signed ofs') ((Ptrofs.signed ofs') + sizeof ty') = Some m'' ->
    drop_place' owned p m b ofs m''.

(** Free {*p, **p ,... } according to me  *)
Inductive drop_place (e: env) (ie: init_env) (p: place) (m: mem) : mem -> Prop :=
| drop_gen: forall b ofs m' id owned,
    eval_place e m p b ofs ->
    local_of_place p = id ->
    PTree.get id ie = Some owned ->
    drop_place' owned p m b ofs m' ->
    drop_place e ie p m m'.

Inductive drop_place_list (e: env) (ie: init_env) (m: mem) : list place -> mem -> Prop :=
| drop_place_list_base:
    drop_place_list e ie m nil m
| drop_place_list_cons: forall p lp m' m'',
    drop_place e ie p m m' ->
    drop_place_list e ie m' lp m'' ->
    drop_place_list e ie m (p::lp) m''.
  
       

(* Variable function_entry: function -> list val -> mem -> env -> mvenv -> mem -> Prop. *)

(** Transition relation *)

(** [TODEL] If a place [p] owns a location through box, it has the drop
obligations. In other words, if [p] has type [Tbox] then [p] in its
drop obligation list. A special case is the mutable reference, if [p]
has type [&mut T], then we should not terminate the obligation
generation, instead we should generate the obligations for [*p] (i.e.,
skip [p]). For example, if [p:&mut Box<i32> = &mut x] and [*p =
new_box], we should drop *p. Note that when x goes out of scope, it
would drop the [new_box]. *)
(* Fixpoint drop_obligations (p: place) (ty: type) : list place := *)
(*   match ty with *)
(*   | Tbox ty' => *)
(*       let deref := Pderef p ty' in *)
(*       p :: drop_obligations deref ty' *)
(*   | Treference ty' Mutable _ => *)
(*       let deref := Pderef p ty' in *)
(*       drop_obligations deref ty' *)
(*   | _ => nil *)
(*   end. *)

Fixpoint init_path (p: place) (ty: type) : list place :=
  match ty with
  | Tbox ty' =>
      let deref := Pderef p ty' in
      p :: init_path deref ty'
  | Treference ty' Mutable _ =>
      let deref := Pderef p ty' in
      p :: init_path deref ty'
  | _ => nil
  end.
  



(** Allocate memory blocks for function parameters and build the local environment and move environment  *)
Inductive alloc_variables: env -> init_env -> mem ->
                           list (ident * type) ->
                           env -> init_env -> mem -> Prop :=
| alloc_variables_nil:
  forall e ie m,
    alloc_variables e ie m nil e ie m
| alloc_variables_cons:
  forall e ie m id ty vars m1 b1 m2 e2 ie2 drops,
    Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
    (* get the initialized path based on ty *)
    init_path (Plocal id ty) ty = drops ->
    alloc_variables (PTree.set id (b1, ty) e) (PTree.set id drops ie) m1 vars e2 ie2 m2 ->
    alloc_variables e ie m ((id, ty) :: vars) e2 ie2 m2.

(** Assign the values to the memory blocks of the function parameters  *)
Inductive bind_parameters (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_paranmeters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ty m b Ptrofs.zero v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Return the list of places in local environment  *)

Definition place_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => Plocal id ty end.

Definition places_of_env (e:env) : list place :=
  List.map place_of_binding (PTree.elements e).
                                  


(** Function entry semantics: the key is to instantiate the move environments  *)
Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (ie: init_env) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params)) ->
    alloc_variables empty_env empty_init_env m f.(fn_params) e ie m1 ->
    bind_parameters e m1 f.(fn_params) vargs m' ->
    function_entry ge f vargs m e ie m'.
 
Section WITH_GE.

Variable ge: genv.

Inductive step: state -> trace -> state -> Prop :=

| step_assign: forall f be p op k le ie ie' ie'' m1 m2 m3 m4 b ofs ty v,
    typeof_place p = ty ->
    typeof_boxexpr be = ty ->             (* for now, just forbid type casting *)
    (* get the location of the place *)
    eval_place le m1 p b ofs ->
    (* evaluate the boxexpr, return the value and the moved place (optional) *)
    eval_boxexpr le m1 be v op m2 ->
    (* update the initialized environment based on [op] *)
    uninit_env ie op = Some ie' ->
    (* drop the successors of p (i.e., *p, **p, ...). If ty is not
    owned type, drop_place has no effect. We must first update the me
    and then drop p, consider [ *p=move *p ] *)
    drop_place le ie' p m2 m3 ->
    (* update the init env for p *)
    PTree.set (local_of_place p) (init_path p (typeof_place p)) ie' = ie'' ->    
    (* assign to p  *)    
    assign_loc ty m3 b ofs v m4 ->
    step (State f (Sassign p be) k le ie m1) E0 (State f Sskip k le ie'' m4)
         
| step_let: forall f be op v ty id ie1 ie2 ie3 m1 m2 m3 m4 le1 le2 b k stmt,
    typeof_boxexpr be = ty ->
    eval_boxexpr le1 m1 be v op m2 ->
    (* update the move environment *)
    uninit_env ie1 op = Some ie2 ->
    (* allocate the block for id *)
    Mem.alloc m2 0 (sizeof ty) = (m3, b) ->
    (* uppdate the local env *)
    PTree.set id (b, ty) le1 = le2 ->
    (* update the initialized environment *)
    PTree.set id (init_path (Plocal id ty) ty) ie2 = ie3 ->
    (* assign [v] to [b] *)
    assign_loc ty m3 b Ptrofs.zero v m4 ->
    step (State f (Slet id ty be stmt) k le1 ie1 m1) E0 (State f stmt (Klet id k) le2 ie3 m4)
         
| step_call_0: forall f a al optlp k le ie1 ie2 m vargs tyargs vf fd cconv tyres,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr le m a vf None ->
    eval_exprlist le m al tyargs vargs optlp ->
    (* CHECKME: update the initialized environment *)
    uninit_env_list ie1 optlp = Some ie2 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    step (State f (Scall None a al) k le ie1 m) E0 (Callstate vf vargs (Kcall None f le ie2 k) m)         
| step_call_1: forall f a al optlp k le le' ie1 ie2 ie3 m m' b vargs tyargs vf fd cconv tyres id,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr le m a vf None ->
    eval_exprlist le m al tyargs vargs optlp ->
    (* CHECKME: update the move environment *)
    uninit_env_list ie1 optlp = Some ie2 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    (* allocate memory block and update the env/mvenv for id, just like step_let *)
    Mem.alloc m 0 (sizeof tyres) = (m', b) ->
    PTree.set id (b, tyres) le = le' ->
    PTree.set id (init_path (Plocal id tyres) tyres) ie2 = ie3 ->
    step (State f (Scall (Some id) a al) k le ie1 m) E0 (Callstate vf vargs (Kcall (Some id) f le' ie3 k) m')
                 
(* End of a let statement, free the place and its drop obligations *)
| step_end_let: forall f id k le1 le2 me1 me2 m1 m2 m3 ty b,
    PTree.get id le1 = Some (b, ty) ->
    (* free {*id, **id, ...} if necessary *)
    drop_place le1 me1 (Plocal id ty) m1 m2 ->
    (* free the block [b] of the local variable *)
    Mem.free m2 b 0 (sizeof ty) = Some m3 ->
    (* clear [id] in the local env and move env. It is necessary for the memory deallocation in return state *)
    PTree.remove id le1 = le2 ->
    PTree.remove id me1 = me2 ->
    step (State f Sskip (Klet id k) le1 me1 m1) E0 (State f Sskip k le2 me2 m3)

| step_internal_function: forall vf f vargs k m e me m'
    (FIND: Genv.find_funct ge vf = Some (AST.Internal f)),
    function_entry ge f vargs m e me m' ->
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e me m')

(** Return cases  *)
| step_return_0: forall e ie lp lb m1 m2 m3 f k ,
    (* Q1: if there is a drop obligations list {*p ...} but the type
    of p is [&mut Box<T>]. Do we need to drop *p ? Although we need to
    drop [*p] then [*p] is reassign but I don't think it is correct to
    drop *p when at the function return *)
    places_of_env e = lp ->
    (* drop the lived drop obligations *)
    drop_place_list e ie m1 lp m2 ->
    blocks_of_env e = lb ->
    (* drop the stack blocks *)
    Mem.free_list m2 lb = Some m3 ->    
    step (State f (Sreturn None) k e ie m1) E0 (Returnstate Vundef (call_cont k) m3)
| step_return_1: forall le a v op ie ie' lp lb m1 m2 m3 f k ,
    eval_expr le m1 a v op ->
    (* CHECKME: update move environment, because some place may be
    moved out to the callee *)
    uninit_env ie op = Some ie' ->
    places_of_env le = lp ->
    drop_place_list le ie' m1 lp m2 ->
    (* drop the stack blocks *)
    blocks_of_env le = lb ->
    Mem.free_list m2 lb = Some m3 ->
    step (State f (Sreturn (Some a)) k le ie m1) E0 (Returnstate v (call_cont k) m3)
(* no return statement but reach the end of the function *)
| step_skip_call: forall e me lp lb m1 m2 m3 f k,
    is_call_cont k ->
    places_of_env e = lp ->
    drop_place_list e me m1 lp m2 ->
    blocks_of_env e = lb ->
    Mem.free_list m2 lb = Some m3 ->
    step (State f Sskip k e me m1) E0 (Returnstate Vundef (call_cont k) m3)
         
| step_returnstate_0: forall v m e me f k,
    step (Returnstate v (Kcall None f e me k) m) E0 (State f Sskip k e me m)
| step_returnstate_1: forall id v b ty m m' e me f k,
    (* Note that the memory location of the return value has been
    allocated in the call site *)
    PTree.get id e = Some (b,ty) ->
    assign_loc ty m b Ptrofs.zero v m' ->    
    step (Returnstate v (Kcall (Some id) f e me k) m) E0 (State f Sskip k e me m')

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
    eval_expr e m a v1 None ->
    to_ctype (typeof a) = Some ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e me m)
      E0 (State f (if b then s1 else s2) k e me' m)
| step_loop: forall f s1 s2 k e me m,
    step (State f (Sloop s1 s2) k e me m)
      E0 (State f s1 (Kloop1 s1 s2 k) e me m)
| step_skip_or_continue_loop1:  forall f s1 s2 k e me m x,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop1 s1 s2 k) e me m)
      E0 (State f s2 (Kloop2 s1 s2 k) e me m)
| step_break_loop1:  forall f s1 s2 k e me m,
    step (State f Sbreak (Kloop1 s1 s2 k) e me m)
      E0 (State f Sskip k e me m)
| step_skip_loop2: forall f s1 s2 k e me m,
    step (State f Sskip (Kloop2 s1 s2 k) e me m)
      E0 (State f (Sloop s1 s2) k e me m)
| step_break_loop2: forall f s1 s2 k e me m,
    step (State f Sbreak (Kloop2 s1 s2 k) e me m)
      E0 (State f Sskip k e me m)
        
.

(** Open semantics *)

(** IDEAS: can we check the validity of the input values based on the
function types?  *)
Inductive initial_state: c_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc ctargs ctres vargs m,
    Genv.find_funct ge vf = Some (AST.Internal f) ->
    type_of_function f = Tfunction targs tres tcc ->
    (** TODO: val_casted_list *)
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    to_ctypelist targs = Some ctargs ->
    to_ctype tres = Some ctres ->
    initial_state (cq vf (signature_of_type ctargs ctres tcc) vargs m)
                  (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> c_query -> Prop:=
| at_external_intro: forall vf name sg args k m,
    Genv.find_funct ge vf = Some (AST.External (EF_external name sg)) ->    
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

End WITH_GE.

  
Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.
  
