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
| Sfor: statement -> expr -> statement -> statement -> statement (**r [for] loop *)
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
