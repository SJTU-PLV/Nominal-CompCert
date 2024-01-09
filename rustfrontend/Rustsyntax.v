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

(** The rust surface syntax *)

Inductive expr : Type :=
| Eval (v: val) (ty: type)                                  (**r constant *)
| Evar (x: ident) (ty: type)                                (**r variable *)
| Ebox (r: expr) (ty: type)                                 (**r allocate a heap block *)
| Efield (l: expr) (f: ident) (ty: type) (**r access to a member of a struct *)
| Ederef (r: expr) (ty: type)        (**r pointer dereference (unary [*]) *)
| Eunop (op: unary_operation) (r: expr) (ty: type)
(**r unary arithmetic operation *)
| Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
                                           (**r binary arithmetic operation *)
| Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
| Ecall (r1: expr) (rargs: exprlist) (ty: type)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

Definition typeof (e: expr) : type :=
  match e with
  | Eval _ ty
  | Evar _ ty
  | Ebox _ ty
  | Efield _ _ ty
  | Ederef _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty                  
  | Eassign _ _ ty
  | Ecall _ _ ty => ty
end.

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Sdo : expr -> statement            (**r evaluate expression for side effects *)
| Slet: ident -> type -> statement -> statement  (**r [Slet id ty] opens a new scope with one variable of type ty *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Swhile : expr -> statement -> statement   (**r [while] loop *)
| Sloop: statement -> statement                               (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : option expr -> statement     (**r [return] statement *)
| Smatch : expr -> arm_statements -> statement  (**r pattern match statements *)

with arm_statements : Type :=            (**r cases of a [match] *)
  | ASnil: arm_statements
  | AScons: option (ident * ident) -> statement -> arm_statements -> arm_statements.
                      (**r [None] is [default], [Some (fid, id)] is [case fid (id)] *)


Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type); 
  fn_body: statement
}.  

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.


(** Notations for Rustsyntax programs *)


Definition A : ident := 1%positive.
Definition B : ident := 2%positive.
Definition C : ident := 3%positive.
Definition D : ident := 4%positive.
Definition E : ident := 5%positive.

Declare Custom Entry rustsyntax.
Declare Scope rustsyntax_scope.
Declare Custom Entry rustsyntax_aux.

Notation "<{ s }>" := s (s custom rustsyntax_aux) : rustsyntax_scope.
Notation "s" := s (in custom rustsyntax_aux at level 0, s custom rustsyntax) : rustsyntax_scope.

(* Notations for statement *)
Notation "'if' e 'then' s1 'else' s2 'end'" := (Sifthenelse e s1 s2) (in custom rustsyntax at level 89, right associativity) : rustsyntax_scope.
Notation "s1 ; s2" := (Ssequence s1 s2) (in custom rustsyntax at level 90, right associativity) : rustsyntax_scope.
Notation "'do' e" := (Sdo e) (in custom rustsyntax at level 80) : rustsyntax_scope.
Notation "'skip'" := Sskip (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'break'" := Sbreak (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'continue'" := Scontinue (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'return'" := (Sreturn None) (in custom rustsyntax at level 10) : rustsyntax_scope.
Notation "'return' e" := (Sreturn (@Some expr e)) (in custom rustsyntax at level 10) : rustsyntax_scope.
Notation "'let' x : t 'in' s 'end' " := (Slet x t s) (in custom rustsyntax at level 5, x constr at level 99, t constr at level 99) : rustsyntax_scope.
Notation "'loop' s 'end'" := (Sloop s) (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation "'while' e 'do' s 'end'" := (Swhile e s) (in custom rustsyntax at level 20) : rustsyntax_scope.
(** TODO: define the notations for match statement *)

(* Notations for expression *)

Notation " 'Var' x # t " := (Evar x t) (in custom rustsyntax at level 10, x global, t global).
Notation "'Box' < t > ( e )" := (Ebox e t) (in custom rustsyntax at level 10, t global).

Print Grammar constr.
Print Custom Grammar rustsyntax.

Open Scope rustsyntax_scope.

Definition var_a : expr := <{ Var A # type_int32s }>.
Definition box_a : expr := <{ Box< type_int32s >(Var A # type_int32s) }>.


Notation "p := f ( l ) " := (Scall (Some p) f l) (in custom rustsyntax at level 5, p constr at level 99, f constr at level 99, l constr at level 99, no associativity) : rustsyntax_scope.
Notation " f ( l )" := (Scall None f l) (in custom rustsyntax at level 5, f constr at level 99, l constr at level 99, no associativity) : rustsyntax_scope.


(* Print Grammar constr. *)


