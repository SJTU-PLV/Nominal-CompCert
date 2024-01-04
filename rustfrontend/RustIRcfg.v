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

(** The definitions of place and expression are almost the same as Rustlight *)

Inductive expr : Type :=
| Econst_int: int -> type -> expr       (**r integer literal *)
| Econst_float: float -> type -> expr   (**r double float literal *)
| Econst_single: float32 -> type -> expr (**r single float literal *)
| Econst_long: int64 -> type -> expr    (**r long integer literal *)
| Eplace: usekind -> place -> type -> expr (**r use of a variable, the only lvalue expression *)
| Eget: usekind -> place -> ident -> type -> expr (**r get<fid>(a), variant get operation *)
| Ecktag: place -> ident -> type -> expr           (**r check the tag of variant, e.g. [Ecktag p.(fid)] *)
| Etempvar: ident -> type -> expr                  (**r value of the temporary variable *)
| Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
| Ebinop: binary_operation -> expr -> expr -> type -> expr. (**r binary operation *)



Inductive boxexpr : Type :=
| Bexpr: expr -> boxexpr
| Box: boxexpr -> boxexpr.

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty
  | Econst_float _ ty
  | Econst_single _ ty
  | Econst_long _ ty                
  | Eplace _ _ ty
  | Ecktag _ _ ty
  | Etempvar _ ty
  | Eget _ _ _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty => ty
  end.

Fixpoint typeof_boxexpr (r: boxexpr) : type :=
  match r with
  | Bexpr e => typeof e
  | Box r' => Tbox (typeof_boxexpr r') noattr
  end.


Definition node := positive.

Inductive statement :=
| Sskip : node -> statement
| Sassign : place -> boxexpr -> node -> statement
| Sset : ident -> expr -> node -> statement (* stuck if there is move in expr. TODO: change expr to pure expression in set statement *)
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

Definition successors (stmt: statement) : list node :=
  match stmt with
  | Sskip n => n :: nil
  | Sassign _ _ n => n :: nil
  | Sset _ _ n => n :: nil
  | Sstoragelive _ n => n :: nil
  | Sstoragedead _ n => n :: nil
  | Sdrop _ n => n :: nil
  | Scall _ _ _ n => n :: nil
  | Sifthenelse _ n1 n2 => n1 :: n2 :: nil
  | Sreturn _ => nil
  end.

(** Maximum PC (node number) in the CFG of a function.  All nodes of
  the CFG of [f] are between 1 and [max_pc_function f] (inclusive). *)

Definition max_pc_function (f: function) :=
  PTree.fold (fun m pc i => Pos.max m pc) f.(fn_body) 1%positive.
