Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
Require Import Integers.

Require Import LanguageInterface.
Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import SymbolTable.

Local Open Scope Z_scope.

Definition _memoized : ident := 54%positive.
Definition _t : ident := 56%positive.
Definition _x : ident := 55%positive.
Definition _t'1 : ident := 59%positive.

Definition v_memoized := {|
  gvar_info := (tarray tint MAX);
  gvar_init := (Init_space (4 * MAX) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition func_f := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _x tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _t
      (Ederef
        (Ebinop Oadd (Evar _memoized (tarray tint 1000)) (Etempvar _x tint)
          (tptr tint)) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _t tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar g_id (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Ebinop Osub (Etempvar _x tint) (Econst_int (Int.repr 1) tint)
                 tint) :: nil))
            (Sset _t
              (Ebinop Oadd (Etempvar _t'1 tint) (Etempvar _x tint) tint)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _memoized (tarray tint 1000))
                (Etempvar _x tint) (tptr tint)) tint) (Etempvar _t tint)))
        Sskip)
      (Sreturn (Some (Etempvar _t tint))))))
|}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((g_id,
   Gfun(External (EF_external "g" int_int_sg )
     (Tcons tint Tnil) tint cc_default)) :: (_memoized, Gvar v_memoized) ::
 (f_id, Gfun(Internal func_f)) :: nil).

Definition public_idents : list ident :=
(f_id :: g_id :: nil).

Definition prog : Clight.program :=
  mkprogram composites global_definitions public_idents main_id Logic.I.

