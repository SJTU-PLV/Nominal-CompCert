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
| Eget (l: expr) (f: ident) (ty: type) (**r access to a member of a variant *)
| Etag (l: expr) (ty: type) (**r get the tag of [l] *)
| Euse (l: expr) (ty: type)              (**r l-value used as a r-value *)
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


Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Sdo : expr -> statement            (**r evaluate expression for side effects *)
| Slet: ident -> option expr -> statement         (**r the start of a variable  *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Swhile : expr -> statement -> statement   (**r [while] loop *)
| Sdowhile : expr -> statement -> statement (**r [do] loop *)
| Sfor: statement -> expr -> statement -> statement -> statement (**r [for] loop *)
| Sloop: statement -> statement                               (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : option expr -> statement     (**r [return] statement *)
| Smatch : expr -> stmtlist -> statement  (**r pattern match statements *)

with stmtlist : Type :=
  | Snil
  | Scons (s1: statement) (sl: stmtlist).

                                          
Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type); 
  fn_body: statement
}.  

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.
