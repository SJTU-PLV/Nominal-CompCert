Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.

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

(* Used in Rustlightown and RustIRgen *)
Fixpoint extract_vars (stmt: Rustlight.statement) : list (ident * type) :=
  match stmt with
  | Slet id ty s =>
      (id,ty) :: extract_vars s
  | Rustlight.Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustlight.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustlight.Sloop s =>
      extract_vars s
  | _ => nil
  end.

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

(* Moved place of expressions *)

(* place with succesive Pdowncast in the end is not a valid owner. For
example, move (Pdowncast p) is equivalent to move p *)
Fixpoint valid_owner (p: place) :=
  match p with
  | Pdowncast p' _ _ => valid_owner p'
  | _ => p
  end.

Definition moved_place (e: expr) : option place :=
  match e with
  | Emoveplace p _ => Some (valid_owner p)
  | _ => None
  end.

Fixpoint moved_place_list (al: list expr) : list place :=
  match al with
  | e :: l =>
      match moved_place e with
      | Some p => p :: moved_place_list l
      | None => moved_place_list l
      end
  | nil => nil
  end.

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

Lemma is_prefix_strict_trans p1 p2 p3:
  is_prefix_strict p1 p2 = true ->
  is_prefix_strict p2 p3 = true ->
  is_prefix_strict p1 p3 = true.
Admitted.

Lemma is_prefix_refl: forall p, is_prefix p p = true.
Admitted.


Lemma is_prefix_trans: forall p1 p2 p3, is_prefix p1 p2 = true -> is_prefix p2 p3 = true -> is_prefix p1 p3 = true.
Admitted.

Lemma is_prefix_strict_implies: forall p1 p2,
    is_prefix_strict p1 p2 = true ->
    is_prefix p1 p2 = true.
Admitted.

Lemma is_prefix_strict_not_refl: forall p,
    is_prefix_strict p p = false.
Admitted.

Lemma is_prefix_strict_iff: forall p1 p2,
    is_prefix_strict p1 p2 = true <-> (is_prefix p1 p2 = true /\ p1 <> p2).
Admitted.

Fixpoint local_of_place (p: place) :=
  match p with
  | Plocal id _ => id
  | Pfield p' _ _ => local_of_place p'
  | Pderef p' _ => local_of_place p'
  | Pdowncast p' _ _ => local_of_place p'
  end.

Lemma is_prefix_same_local: forall p1 p2,
    is_prefix p1 p2 = true ->
    local_of_place p1 = local_of_place p2.
Admitted.

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
  
Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.

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
