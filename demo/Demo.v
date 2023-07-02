Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers Intv.

Definition main_id := (77%positive).
Definition f_id := (154%positive).
Definition g_id := (176%positive).
Definition MAX : Z := 1000%Z.

Definition sum (i: int): int :=
  let sumz: Z := fold_rec Z Z.add 0%Z 0%Z (i.(Int.intval) + 1)%Z in
  Int.repr sumz.

Definition int_int_sg : signature := mksignature (AST.Tint :: nil) (Tret AST.Tint) cc_default.

(** * Implementation of M_A *)

Definition _s : positive := 60%positive.
Definition lb0: label := 1%positive.
Definition lb1: label := 2%positive.
Definition lb2: label := 3%positive.

Definition v_s := {|
  gvar_info := tt;
  gvar_init := (Init_int32 (Int.zero) :: Init_int32 (Int.zero) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.
(*
Definition main_id := (77%positive).
Definition f_id := (154%positive).
Definition g_id := (176%positive).
*)
Definition code: list instruction :=
   (* .cfi_startproc *)
   Pallocframe 24 (Ptrofs.repr 16) Ptrofs.zero ::
     (* subq    $16, %rsp *)
     (* .cfi_adjust_cfa_offset    16 *)
     (* leaq    24(%rsp), %rax *)
     (* movq    %rax, 0(%rsp) *)
     Pmov_mr_a (Addrmode (Some RSP) None (inl 8)) RBX ::
     (* movq    %rbx, 8(%rsp) *)

     Pmov_rr RBX RDI ::
     (* movq    %rdi, %rbx *)
     Ptestl_rr RBX RBX ::
     (* testl    %ebx, %ebx *)
     Pjcc Cond_ne lb0 ::
     (* jne    .L100 *)
     Pxorl_r RAX ::
     (* xorl    %eax, %eax *)
     Pjmp_l lb1 ::
     (* jmp    .L101 *)

     Plabel lb0 ::
     (* .L100: *)
     Pmovl_rm RAX (Addrmode None None (inr (_s, Ptrofs.zero))) ::
     (* movl	memoized(%rip), %eax *)
     Pcmpl_rr RBX RAX ::
     (* cmpl	%eax, %ebx *)
     Pjcc Cond_e lb2 ::
     (* je	.L102 *)
     Pleal RDI (Addrmode (Some RBX) None (inl (- 1))) ::
     (* leal    -1(%ebx), %edi *)

     Pcall_s f_id (int_int_sg) ::
     (* call    f *)

     Pleal RAX (Addrmode (Some RAX) (Some (RBX, 1)) (inl 0)) ::
     (* leal    0(%eax,%ebx,1), %eax *)
     Pmovl_mr (Addrmode None None (inr (_s, Ptrofs.zero))) RBX ::
     (*	movl	%ebx, memoized(%rip) *)
     Pmovl_mr (Addrmode None None (inr (_s, Ptrofs.repr 4))) RAX ::
     (*	movl	%eax, (memoized + 4)(%rip) *)
     Pjmp_l lb1 ::
     (* jmp    .L101 *)

     Plabel lb2 ::
     (* .L102: *)
     Pmovl_rm RAX (Addrmode None None (inr (_s, Ptrofs.repr 4))) ::
     (* movl	(memoized + 4)(%rip), %eax *)

     Plabel lb1 ::
     (* .L101: *)
     Pmov_rm_a RBX (Addrmode (Some RSP) None (inl 8)) ::
     (* movq    8(%rsp), %rbx *)
     Pfreeframe 24 (Ptrofs.repr 16) Ptrofs.zero ::
     (* addq    $16, %rsp *)
     Pret ::
       (* ret *)
     nil.

Definition func_g: Asm.function :=
  Asm.mkfunction (int_int_sg) code.

Definition global_definitions : list (ident * globdef fundef unit) :=
((f_id, Gfun(External (EF_external "f" int_int_sg))) ::
  (_s, Gvar v_s) ::
  (g_id, Gfun(Internal func_g)) ::
  nil).

Definition public_idents : list ident :=
(f_id :: g_id :: nil).

Definition M_A: program := mkprogram global_definitions public_idents main_id.

Definition asm_semantics := Asm.semantics M_A.

(** * Clight implementation of M_C *)
Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

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
  (Sifthenelse (Ebinop Oeq (Evar _x tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _t
      (Ederef
        (Ebinop Oadd (Evar _memoized (tarray tint 1000)) (Evar _x tint)
          (tptr tint)) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _t tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar g_id (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Ebinop Osub (Evar _x tint) (Econst_int (Int.repr 1) tint)
                 tint) :: nil))
            (Sset _t
              (Ebinop Oadd (Etempvar _t'1 tint) (Evar _x tint) tint)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _memoized (tarray tint 1000))
                (Evar _x tint) (tptr tint)) tint) (Etempvar _t tint)))
        Sskip)
      (Sreturn (Some (Etempvar _t tint))))))
|}.

Definition composites : list composite_definition := nil.

Definition global_definitions_c : list (ident * globdef fundef type) :=
((g_id,
   Gfun(External (EF_external "g" int_int_sg )
     (Tcons tint Tnil) tint cc_default)) :: (_memoized, Gvar v_memoized) ::
 (f_id, Gfun(Internal func_f)) :: nil).

Definition public_idents_c : list ident :=
(f_id :: g_id :: nil).

Definition M_C : Clight.program :=
  mkprogram composites global_definitions_c public_idents_c main_id Logic.I.

