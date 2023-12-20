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
Require Import Clight RustlightBase.

(** * Rust Intermediate Rrepresentation  *)

(** To compile Rustlight to RustIR, we replace the scopes (let stmt)
with StorageLive (StorageDead) statements, use CFG to represent the
program (better for analysis) and insert explicit drop operations (so
that the RustIR has no ownership semantics) *)

(** The definitions of place and expression are the same as Rustlight *)

Definition node := positive.

Inductive statement :=
| Sskip : node -> statement
| Sassign : place -> expr -> node -> statement
| Sset : ident -> expr -> node -> statement
| Sstoragelive: ident -> node -> statement
| Sstoragedead: ident -> node -> statement
| Sdrop: place -> node -> statement
| Scall: option place -> expr -> list expr -> node -> statement
| Sifthenelse: expr -> node -> node -> statement
| Sreturn: option expr -> statement.

Definition code: Type := PTree.t statement.

Record function :=
  { fn_return : type;
    fn_callconv: calling_convention;
    fn_params: list (ident * type);
    fn_vars: list (ident * type);
    fn_temps: list (ident * type); (* for drop flag *)
    fn_body: code;
    fn_entryblock : node }.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.


Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External _ ef typs typ cc =>     
      Tfunction typs typ cc                
  end.
