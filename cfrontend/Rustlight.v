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
Require Import Ctypes.
Require Import Cop.

(** * High-level Rust-like language  *)

Inductive usekind : Type :=
| Copy
| Move.                        (**r used for types that are unsafe for copying *)

Inductive mutkind : Type :=
| Immutable
| Mutable.


(** ** Types  *)

Inductive type : Type :=
  | Tunit: type                                    (**r the [unit] type *)
  | Tbox : type -> type                             (**r heap allocated [Box ty] *)
  | Tint: intsize -> signedness -> attr -> type       (**r integer types *)
  | Treference: type -> mutkind -> attr -> type       (**r reference types ([&mut? ty]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.


(** ** Place (Lvalue)  *)

Inductive place : Type :=
| Plocal : ident -> type -> place
| Pderef: place -> type -> place.          (* [*] operand *)

Definition typeof_place p :=
  match p with
  | Plocal _ ty => ty
  | Pderef _ ty => ty
  end.

(** ** Expression *)

Inductive expr : Type :=
| Econst_int: int -> type -> expr       (**r integer literal *)
| Eplace: usekind -> place -> type -> expr (**r use of a variable *)
| Eref: mutkind -> place -> type -> expr         (**r reference operator ([& mut?]) *)
| Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
| Ebinop: binary_operation -> expr -> expr -> type -> expr. (**r binary operation *)

(* evaluate an expr has no side effect. But evaluate an rvalue has side effect *)
Inductive rvalue : Type :=
| Rexpr: expr -> rvalue
| Rbox: rvalue -> rvalue.


Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty 
  | Eplace _ _ ty
  | Eref _ _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty => ty
  end.

Fixpoint typeof_rvalue (r: rvalue) : type :=
  match r with
  | Rexpr e => typeof e
  | Rbox r' => Tbox (typeof_rvalue r')
  end.

Fixpoint to_ctype (ty: type) : option Ctypes.type :=
  match ty with
  | Tunit => Some Tvoid 
  | Tbox _  => None
  | Tint sz si attr => Some (Ctypes.Tint sz si attr)
  | Treference ty mut attr =>
      match to_ctype ty with
      | Some ty => Some (Tpointer ty attr)
      | None => None
      end
  | Tfunction tyl ty cc =>
      match to_ctype ty, to_ctypelist tyl with
      | Some ty, Some tyl => Some (Ctypes.Tfunction tyl ty cc)
      | _, _ => None
      end
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
                                    
Definition copy_safe (ty: type) :=
  match ty with
  | Tbox _ => false
  | Treference _ Mutable _ => false
  | _ => true
  end.

Definition not_owned_type (ty: type) :=
  match ty with
  | Tbox _ => false
  | _ => true
  end.


Definition deref_type (ty: type) : option type :=
  match ty with
  | Tbox ty' => Some ty'
  | Treference ty' _ _ => Some ty'
  | _ => None
  end.
                      


Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Slet : ident -> type -> rvalue -> statement -> statement (**r let ident: type = rvalue in *)
  | Sassign : place -> rvalue -> statement (**r assignment [place = rvalue] *)
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

Definition fundef := AST.fundef function.

Definition program := AST.program fundef type.

(** copy from Ctypes.v *)
Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | AST.Internal fd => type_of_function fd
  | AST.External ef =>
      let sig := ef_sig ef in
      (** TODO *)
      Tfunction Tnil Tunit cc_default                
  end.

(** * Operational Semantics  *)


(** ** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.


Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := PTree.empty composite |}. (** FIXME: for now, we do not support composite environment  *)


(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** ** Move environment  *)

(** It records the drop obligations for a local variable and its
successors. If [x] owns a memory location (i.e., x has type [Tbox],
before freeing [x], we must first free the memory block of [*x]. In a
high level, if a place [p] is in the mvenv, then we should free the
memory location [p] points to when we free [p] *)

Definition mvenv := PTree.t (list place).

Definition empty_mvenv : mvenv := PTree.empty (list place).

(** access mode for Rust types  *)
Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tbox _ => By_value Mptr
  | Tunit => By_nothing
  | Treference _ _ _ => By_value Mptr
  | Tfunction _ _ _ => By_reference

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


(** Size of a type  *)

Definition sizeof (t: type) : Z :=
  match t with
  | Tunit => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tbox _ => if Archi.ptr64 then 8 else 4
  | Treference _ _ _ => if Archi.ptr64 then 8 else 4
  | Tfunction _ _ _ => 1
  end.

Definition alignof_blockcopy (t: type) : Z :=
  match t with
  | Tunit => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tbox _ => if Archi.ptr64 then 8 else 4
  | Treference _ _ _ => if Archi.ptr64 then 8 else 4
  | Tfunction _ _ _ => 1
  end.

(** Assign a value to a location  *)

Inductive assign_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ty > 0 -> (alignof_blockcopy ty | Ptrofs.unsigned ofs')) ->
      (sizeof ty > 0 -> (alignof_blockcopy ty | Ptrofs.unsigned ofs)) ->
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


Definition erase_move_paths (me: mvenv) (p: place) : option mvenv :=
  let id := local_of_place p in
  match PTree.get id me with
  | Some drop_obligations =>
      let erased := filter (fun p1 => negb (is_prefix p p1)) drop_obligations in
      Some (PTree.set id erased me)
  | None => None
  end.

(** If [p:Box<ty>] then p can be moved; If [*p:Box<ty>] and [p:Box<..>] then *p can be moved *)
Definition legal_move (p: place) : bool :=
  match p with
  | Plocal id ty =>
      negb (not_owned_type ty)
  | Pderef p' ty' =>
      match typeof_place p' with
      | Tbox _ => negb (not_owned_type ty')
      | _ => false
      end
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

Inductive eval_place : place -> block -> ptrofs -> Prop :=
| eval_Plocal: forall id l ty,
    e!id = Some (l, ty) ->
    eval_place (Plocal id ty) l Ptrofs.zero
| eval_Pderef: forall p ty l ofs l' ofs',
    eval_place p l ofs ->
    deref_loc ty m l ofs (Vptr l' ofs') ->
    eval_place (Pderef p ty) l' ofs'.

(* side effect: it may change the move environment when evaluating Eplace *)
Inductive eval_expr (me: mvenv) : expr -> val -> mvenv -> Prop :=
| eval_Econst_int:   forall i ty,
    eval_expr me (Econst_int i ty) (Vint i) me
| eval_Eunop:  forall op a ty v1 v aty me',
    eval_expr me a v1 me' ->
    (* Note that to_ctype Tbox = None *)
    to_ctype (typeof a) = Some aty ->
    sem_unary_operation op v1 aty m = Some v ->
    eval_expr me (Eunop op a ty) v me'
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
    eval_expr me (Eplace Copy p ty) v me
| eval_Eplace_move: forall p b ofs ty m v me',
    eval_place p b ofs ->
    deref_loc ty m b ofs v ->
    (* Before move out a place, we should ensure that it is legal to move it *)
    legal_move p = true ->
    (* erase {p, *p, **p, ...} in the move env because after being
    moved out, [p] no longer owns the location it points to *)
    erase_move_paths me p = Some me' ->
    eval_expr me (Eplace Move p ty) v me'
| eval_Eref: forall p b ofs mut ty,
    eval_place p b ofs ->
    eval_expr me (Eplace mut p ty) (Vptr b ofs) me.

Inductive eval_exprlist (me: mvenv) : list expr -> typelist -> list val -> mvenv -> Prop :=
| eval_Enil:
  eval_exprlist me nil Tnil nil me
| eval_Econs:   forall a bl ty tyl v1 v2 vl me' me'',
    (* For now, we does not allow type cast *)
    typeof a = ty ->
    eval_expr me a v1 me' ->
    (* sem_cast v1 (typeof a) ty m = Some v2 -> *) 
    eval_exprlist me' bl tyl vl me'' ->
    eval_exprlist me (a :: bl) (Tcons ty tyl) (v2 :: vl) me''.

Inductive eval_rvalue (me: mvenv) : rvalue -> val -> mvenv -> mem -> Prop :=
| eval_Rexpr: forall e v me',
    eval_expr me e v me' ->
    eval_rvalue me (Rexpr e) v me' m
| eval_Rbox: forall r v me' me'' m' m'' b,
    eval_rvalue me r v me' m' ->
    Mem.alloc m' 0 (sizeof (typeof_rvalue r)) = (m'', b) ->
    eval_rvalue me (Rbox r) (Vptr b Ptrofs.zero) me'' m''.


End EXPR.




(** Continuations *)

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Klet: ident -> cont -> cont
| Kloop1: statement -> statement -> cont -> cont
| Kloop2: statement -> statement -> cont -> cont
| Kcall: option ident  -> function -> env -> mvenv -> cont -> cont.


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
      (me: mvenv)
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
[****p]", and the drop obligations for [p] is {p, *p, ***p}, then
drop_place' would drop the location pointed by [p] and [*p]. *)
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
Inductive drop_place (e: env) (me: mvenv) (p: place) (m: mem) : mem -> Prop :=
| drop_gen: forall b ofs m' id owned,
    eval_place e m p b ofs ->
    local_of_place p = id ->
    PTree.get id me = Some owned ->
    drop_place' owned p m b ofs m' ->
    drop_place e me p m m'.

Inductive drop_place_list (e: env) (me: mvenv) (m: mem) : list place -> mem -> Prop :=
| drop_place_list_base:
    drop_place_list e me m nil m
| drop_place_list_cons: forall p lp m' m'',
    drop_place e me p m m' ->
    drop_place_list e me m' lp m'' ->
    drop_place_list e me m (p::lp) m''.
  
       

(* Variable function_entry: function -> list val -> mem -> env -> mvenv -> mem -> Prop. *)

(** Transition relation *)

(** If a place [p] owns a location through box, it has the drop
obligations. In other words, if [p] has type [Tbox] then [p] in its
drop obligation list. A special case is the mutable reference, if [p]
has type [&mut T], then we should not terminate the obligation
generation, instead we should generate the obligations for [*p] (i.e.,
skip [p]). For example, if [p:&mut Box<i32> = &mut x] and [*p =
new_box], we should drop *p. Note that when x goes out of scope, it
would drop the [new_box]. *)
Fixpoint drop_obligations (p: place) (ty: type) : list place :=
  match ty with
  | Tbox ty' =>
      let deref := Pderef p ty' in
      p :: drop_obligations deref ty'
  | Treference ty' Mutable _ =>
      let deref := Pderef p ty' in
      drop_obligations deref ty'
  | _ => nil
  end.

(** Allocate memory blocks for function parameters and build the local environment and move environment  *)
Inductive alloc_variables: env -> mvenv -> mem ->
                           list (ident * type) ->
                           env -> mvenv -> mem -> Prop :=
| alloc_variables_nil:
  forall e me m,
    alloc_variables e me m nil e me m
| alloc_variables_cons:
  forall e me m id ty vars m1 b1 m2 e2 me2 drops,
    Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
    (* get the drop obligations based on ty *)
    drop_obligations (Plocal id ty) ty = drops ->
    alloc_variables (PTree.set id (b1, ty) e) (PTree.set id drops me) m1 vars e2 me2 m2 ->
    alloc_variables e me m ((id, ty) :: vars) e2 me2 m2.

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
Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (me: mvenv) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params)) ->
    alloc_variables empty_env empty_mvenv m f.(fn_params) e me m1 ->
    bind_parameters e m1 f.(fn_params) vargs m' ->
    function_entry ge f vargs m e me m'.

    
Variable ge: genv.

Inductive step: state -> trace -> state -> Prop :=

| step_assign: forall f rv p k le me me' m1 m2 m3 m4 b ofs ty v,
    typeof_place p = ty ->
    typeof_rvalue rv = ty ->             (* just forbid type casting *)
    not_owned_type ty = false ->
    (* get the location of the place *)
    eval_place le m1 p b ofs ->
    (* evaluate the rvalue, updated the move env and memory (for Box) *)
    eval_rvalue le m1 me rv v me' m2 ->
    (* drop the successors of p (i.e., *p, **p, ...). If ty is not
    owned type, drop_place has no effect *)
    drop_place le me' p m2 m3 ->
    (* assign to p  *)    
    assign_loc ty m3 b ofs v m4 ->
    step (State f (Sassign p rv) k le me m1) E0 (State f Sskip k le me' m4)
         
| step_let: forall f rv v ty id me1 me2 me3 m1 m2 m3 m4 le1 le2 b k stmt,
    typeof_rvalue rv = ty ->
    eval_rvalue le1 m1 me1 rv v me2 m2 ->
    (* allocate the block for id *)
    Mem.alloc m2 0 (sizeof ty) = (m3, b) ->
    (* uppdate the local env *)
    PTree.set id (b, ty) le1 = le2 ->
    (* update the drop obligations environment *)
    PTree.set id (drop_obligations (Plocal id ty) ty) me2 = me3 ->
    (* assign [v] to [b] *)
    assign_loc ty m3 b Ptrofs.zero v m4 ->
    step (State f (Slet id ty rv stmt) k le1 me1 m1) E0 (State f stmt (Klet id k) le2 me3 m4)
         
| step_call_0: forall f a al k le me1 me2 me3 m vargs tyargs vf fd cconv tyres,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr le m me1 a vf me2 ->
    eval_exprlist le m me2 al tyargs vargs me3 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    step (State f (Scall None a al) k le me1 m) E0 (Callstate vf vargs (Kcall None f le me3 k) m)         
| step_call_1: forall f a al k le le' me1 me2 me3 me4 m m' b vargs tyargs vf fd cconv tyres id,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr le m me1 a vf me2 ->
    eval_exprlist le m me2 al tyargs vargs me3 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction tyargs tyres cconv ->
    (* allocate memory block and update the env/mvenv for id, just like step_let *)
    Mem.alloc m 0 (sizeof tyres) = (m', b) ->
    PTree.set id (b, tyres) le = le' ->
    PTree.set id (drop_obligations (Plocal id tyres) tyres) me3 = me4 ->
    step (State f (Scall (Some id) a al) k le me1 m) E0 (Callstate vf vargs (Kcall (Some id) f le' me4 k) m')
                 
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
| step_return_0: forall e me lp lb m1 m2 m3 f k ,
    (* Q1: if there is a drop obligations list {*p ...} but the type
    of p is [&mut Box<T>]. Do we need to drop *p ? Although we need to
    drop [*p] then [*p] is reassign but I don't think it is correct to
    drop *p when at the function return *)
    places_of_env e = lp ->
    (* drop the lived drop obligations *)
    drop_place_list e me m1 lp m2 ->
    blocks_of_env e = lb ->
    (* drop the stack blocks *)
    Mem.free_list m2 lb = Some m3 ->    
    step (State f (Sreturn None) k e me m1) E0 (Returnstate Vundef (call_cont k) m3)
| step_return_1: forall e a v me0 me lp lb m1 m2 m3 f k ,
    eval_expr e m1 me0 a v me ->
    places_of_env e = lp ->
    drop_place_list e me m1 lp m2 ->
    blocks_of_env e = lb ->
    Mem.free_list m2 lb = Some m3 ->
    step (State f (Sreturn (Some a)) k e me m1) E0 (Returnstate v (call_cont k) m3)
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
.

