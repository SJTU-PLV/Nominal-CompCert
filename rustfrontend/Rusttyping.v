Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Rusttypes RustOp Rustlight.
Require Import Errors Maps.
Require Archi.

Local Open Scope error_monad_scope.

(* This file is not used for now *)

(* To move *)
Definition type_unop (op: unary_operation) (ty: Rusttypes.type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint IBool Signed )
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg )
      | notint_case_l sg => OK (Tlong sg )
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg )
      | neg_case_f => OK (Tfloat F64 )
      | neg_case_s => OK (Tfloat F32 )
      | neg_case_l sg => OK (Tlong sg )
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 )
      end
  end.


Definition numeric_type (ty: type) :=
  match ty with
  (** NB : We do not support i/u8 i/u16 in binary operation otherwise
  we need to consider the signed/zero extension of the result, which
  is conflict with the val_casted properties. A solution is to change
  the definition of sem_add... to consider signed extension after add
  operation. But it is complicated. *)
  | Tint I32 _
  | Tlong _ 
  | Tfloat _ => true
  | _ => false
  end.

Definition numeric_ctype (ty: Ctypes.type) :=
  match ty with
  | Ctypes.Tint I32 _ _
  | Ctypes.Tlong _  _
  | Ctypes.Tfloat _ _ => true
  | _ => false
  end.

Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  (* To avoid complicated type cast, we restrict that ty1 must be
  equal to ty2 in binary operation and both of them are numeric
  type *)
  if type_eq ty1 ty2 then
    if numeric_type ty1 then
      OK ty1
    else Error (msg m)
  else Error (msg m).
  (* match classify_binarith ty1 ty2 with *)
  (* | bin_case_i sg => OK (Tint I32 sg noattr) *)
  (* | bin_case_l sg => OK (Tlong sg noattr) *)
  (* | bin_case_f => OK (Tfloat F64 noattr) *)
  (* | bin_case_s => OK (Tfloat F32 noattr) *)
  (* | bin_default   => Error (msg m) *)
  (* end. *)

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  if type_eq_except_origins ty1 ty2 then
    match ty1 with
    | Tint _ _
    | Tlong _ => OK ty1
    | _ =>  Error (msg m)
    end
  else  Error (msg m).
  (* match classify_binarith ty1 ty2 with *)
  (* | bin_case_i sg => OK (Tint I32 sg noattr) *)
  (* | bin_case_l sg => OK (Tlong sg noattr) *)
  (* | _ => Error (msg m) *)
  (* end. *)

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg )
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg )
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  if type_eq ty1 ty2 then
    if numeric_type ty1 then
      OK type_bool
    else Error (msg m)
  else Error (msg m).

  (* match classify_binarith ty1 ty2 with *)
  (* | bin_default => Error (msg m) *)
  (* | _ => OK (Tint I32 Signed noattr) *)
  (* end. *)

Definition type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd => binarith_type ty1 ty2 "operator infix +"
  | Osub => binarith_type ty1 ty2 "operator infix -"
  | Omul => binarith_type ty1 ty2 "operator infix *"
  | Odiv => binarith_type ty1 ty2 "operator /"
  | Omod => binarith_int_type ty1 ty2 "operator %"
  | Oand => binarith_int_type ty1 ty2 "operator &"
  | Oor => binarith_int_type ty1 ty2 "operator |"
  | Oxor => binarith_int_type ty1 ty2 "operator ^"
  | Oshl => shift_op_type ty1 ty2 "operator <<"
  | Oshr => shift_op_type ty1 ty2 "operator >>"
  | Oeq => comparison_type ty1 ty2 "operator =="
  | One => comparison_type ty1 ty2 "operator !="
  | Olt => comparison_type ty1 ty2 "operator <"
  | Ogt => comparison_type ty1 ty2 "operator >"
  | Ole => comparison_type ty1 ty2 "operator <="
  | Oge => comparison_type ty1 ty2 "operator >="
  end.

