Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Rusttypes RustlightBase.
Require Import Errors Maps.
Require Archi.

Local Open Scope error_monad_scope.

(** Arithmetic and logical operators for the Rust languages *)

(* Redefine some classify_* functions from Cop *)

Definition classify_bool (ty: type) : classify_bool_cases :=
  match ty with
  | Tint _ _ _ => bool_case_i
  | Tfloat F64 _ => bool_case_f
  | Tfloat F32 _ => bool_case_s
  | Tlong _ _ => bool_case_l
  | _ => bool_default
  end.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned _ => notint_case_i Unsigned
  | Tint _ _ _ => notint_case_i Signed
  | Tlong si _ => notint_case_l si
  | _ => notint_default
  end.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned _ => neg_case_i Unsigned
  | Tint _ _ _ => neg_case_i Signed
  | Tfloat F64 _ => neg_case_f
  | Tfloat F32 _ => neg_case_s
  | Tlong si _ => neg_case_l si
  | _ => neg_default
  end.

(* To move *)
Definition type_unop (op: unary_operation) (ty: Rusttypes.type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint I32 Signed noattr)
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg noattr)
      | notint_case_l sg => OK (Tlong sg noattr)
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg noattr)
      | neg_case_f => OK (Tfloat F64 noattr)
      | neg_case_s => OK (Tfloat F32 noattr)
      | neg_case_l sg => OK (Tlong sg noattr)
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 noattr)
      end
  end.

Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
  match ty1, ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => bin_case_i Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => bin_case_i Unsigned
  | Tint _ _ _, Tint _ _ _ => bin_case_i Signed
  | Tlong Signed _, Tlong Signed _ => bin_case_l Signed
  | Tlong _ _, Tlong _ _ => bin_case_l Unsigned
  | Tlong sg _, Tint _ _ _ => bin_case_l sg
  | Tint _ _ _, Tlong sg _ => bin_case_l sg
  | Tfloat F32 _, Tfloat F32 _ => bin_case_s
  | Tfloat _ _, Tfloat _ _ => bin_case_f
  | Tfloat F64 _, (Tint _ _ _ | Tlong _ _) => bin_case_f
  | (Tint _ _ _ | Tlong _ _), Tfloat F64 _ => bin_case_f
  | Tfloat F32 _, (Tint _ _ _ | Tlong _ _) => bin_case_s
  | (Tint _ _ _ | Tlong _ _), Tfloat F32 _ => bin_case_s
  | _, _ => bin_default
  end.

Definition classify_shift (ty1: type) (ty2: type) :=
  match ty1, ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
  | Tint _ _ _, Tlong _ _ => shift_case_il Signed
  | Tlong s _, Tint _ _ _ => shift_case_li s
  | Tlong s _, Tlong _ _ => shift_case_ll s
  | _,_  => shift_default
  end.


Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | bin_case_f => OK (Tfloat F64 noattr)
  | bin_case_s => OK (Tfloat F32 noattr)
  | bin_default   => Error (msg m)
  end.

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg noattr)
  | bin_case_l sg => OK (Tlong sg noattr)
  | _ => Error (msg m)
  end.

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg noattr)
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg noattr)
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_default => Error (msg m)
  | _ => OK (Tint I32 Signed noattr)
  end.

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


(** Try to prove that evaluaiton of expression produces val_casted value *)

Definition typenv := PTree.t type.

Section TYPING.
  
Variable te: typenv.
Variable ce: composite_env.

Lemma wt_int_dec: forall n sz sg, {wt_int n sz sg} + {~ wt_int n sz sg}.
Proof.
  intros. destruct sz, sg;simpl;try eapply Int.eq_dec.
  auto. auto.
Qed.  

Fixpoint wt_place (p: place) : res type :=
  match p with
  | Plocal id ty =>
      match te!id with
      | Some ty' =>
          if type_eq_except_origins ty ty' then
            OK ty
          else Error (msg "local type error")
      | None => Error (msg "local type error")
      end
  | Pderef p ty =>
      do ty' <- wt_place p;
      if type_eq_except_origins ty ty' then
        OK ty
      else Error (msg "deref type error")
  | Pfield p fid ty =>
      do pty <- wt_place p;
      match pty with
      | Tstruct _ sid a =>
          match ce!sid with
          | Some co =>
              do fty <- field_type fid co.(co_members);
              if type_eq_except_origins ty fty then
                OK ty
              else Error (msg "field type error")
          | None => Error (msg "field type error")
          end
      | _ => Error (msg "field type error")
      end
  | Pdowncast p fid ty =>
      do pty <- wt_place p;
      match pty with
      | Tvariant _ sid a =>
          match ce!sid with
          | Some co =>
              do fty <- field_type fid co.(co_members);
              if type_eq_except_origins ty fty then
                OK ty
              else Error (msg "downcast type error")
          | None => Error (msg "downcast type error")
          end
      | _ => Error (msg "downcast type error")
      end
  end.

        
(* strict typing *)
Fixpoint wt_pexpr (pe: pexpr) : res type :=
  match pe with
  | Eunit => OK Tunit
  | Econst_int i (Tint sz sg a) =>
      if wt_int_dec i sz sg then
        OK (Tint sz sg a)
      else Error (msg "const int")
  | Econst_float f (Tfloat F64 a) => OK (Tfloat F64 a)
  | Econst_single f (Tfloat F32 a) => OK (Tfloat F32 a)
  | Econst_long i (Tlong sg a) => OK (Tlong sg a)
  | Eplace p ty =>
      do pty <- wt_place p;
      if type_eq_except_origins ty pty then
        OK ty
      else Error (msg "Eplace type error")
  | Ecktag p fid =>
      OK type_bool
  | Eref orgs mut p ty =>
      do pty <- wt_place p;
      if type_eq_except_origins ty (Treference orgs mut pty (attr_of_type ty)) then
        OK ty
      else Error (msg "Eref type error")
  | Eunop uop pe ty =>
      do ety <- wt_pexpr pe;
      do oty <- type_unop uop ety;
      if type_eq_except_origins ty oty then
        OK ty
      else Error (msg "Eunop type error")
  | Ebinop bop pe1 pe2 ty =>
      do ety1 <- wt_pexpr pe1;
      do ety2 <- wt_pexpr pe2;
      do oty <- type_binop bop ety1 ety2;
      if type_eq_except_origins ty oty then
        OK ty
      else Error (msg "Ebinop type error")
  | _ => Error (msg "other type error in pexpr")
  end.

(* Lemma eval_pexpr_casted: forall pe v, *)
(*     (* wt_pexpr pe -> *) *)
(*     eval_pexpr pe v -> *)
(*     val_casted v (to_ctype (typeof_pexpr pe)). *)
(* Proof. *)
(*   induction pe; intros; simpl.  *)
(*   1-8: admit. *)
(*   - inv H. eapply IHpe in H3. *)
    
    
(*     destruct op;simpl in H1. *)
(*     + unfold sem_notbool, option_map in H1. *)
(*       destruct (bool_val v1 aty m) eqn: BVAL; inv H1. *)
(*       bool_val *)

End TYPING.
