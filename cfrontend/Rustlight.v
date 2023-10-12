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
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
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

Definition fundef := AST.fundef function.

Definition program := AST.program function type.

(** * Operational Semantics  *)


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
| Kcall: option ident -> function -> env -> mvenv -> cont -> cont.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
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



(** Drop a place and its children based on its type  *)
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
  
Variable function_entry: function -> list val -> mem -> env -> mvenv -> mem -> Prop.

(** Transition relation *)

(** If a place [p] own a location through box, it has the drop obligations. In other words, if the evaluation of [p = v] requires [*p] to be droped, then [*p] must be in the drop obligations *)
Fixpoint drop_obligations (p: place) (ty: type) : list place :=
  match ty with
  | Tbox ty' =>
      let deref := Pderef p ty' in
      deref :: drop_obligations deref ty'
  | Treference ty' Mutable _ =>
      let deref := Pderef p ty' in
      drop_obligations deref ty'
  | _ => nil
  end.

Inductive step: state -> trace -> state -> Prop :=

| step_assign_drop: forall f rv p k le me me' m1 m2 m3 m4 b ofs ty v,
    typeof_place p = ty ->
    typeof_rvalue rv = ty ->             (* just forbid type casting *)
    not_owned_type ty = false ->
    (* get the location of the place *)
    eval_place le m1 p b ofs ->
    (* evaluate the rvalue, updated the move env and memory (for Box) *)
    eval_rvalue le m1 me rv v me' m2 ->
    (* drop the successors of p (i.e., *p, **p, ... *)
    drop_place le me' p m2 m3 ->
    (* assign to p  *)    
    assign_loc ty m3 b ofs v m4 ->
    step (State f (Sassign p rv) k le me m1) E0 (State f Sskip k le me' m4)
         
| step_assign_normal: forall f rv p k le me me' m1 m2 m3 b ofs ty v,
    typeof_place p = ty ->
    typeof_rvalue rv = ty ->
    not_owned_type ty = true ->
    (* get the location of the place *)
    eval_place le m1 p b ofs ->
    (* evaluate the rvalue. rv must be an expression because it is not box type *)
    eval_rvalue le m1 me rv v me' m2 ->
    (* assign to p  *)    
    assign_loc ty m2 b ofs v m3 ->
    step (State f (Sassign p rv) k le me m1) E0 (State f Sskip k le me' m3).

｜ step_let: forall,
    typeof_rvalue rv = ty ->
    eval_rvalue le m1 me1 rv v me2 m2 ->
    (* allocate the block for id *)
    Mem.alloc m2 0 (sizeof ty) = (m3, b) ->
    (* update the local env *)
    PTree.set id (b, ty) le = le' ->
    (* update the drop obligations environment *)
 
    
    step (State f (Slet id ty rv stmt) k le me m1) E0 (State f stmt k le me' m)
    
