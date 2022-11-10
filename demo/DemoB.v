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

Definition int_int_sg : signature := mksignature (AST.Tint :: nil) (Tret Tint) cc_default.

Definition _memoized : ident := 60%positive.
Definition lb0: label := 1%positive.
Definition lb1: label := 2%positive.
Definition lb2: label := 3%positive.

Definition v_memoized := {|
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
     Pmovl_rm RAX (Addrmode None None (inr (_memoized, Ptrofs.zero))) ::
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
     Pmovl_mr (Addrmode None None (inr (_memoized, Ptrofs.zero))) RBX ::
     (*	movl	%ebx, memoized(%rip) *)
     Pmovl_mr (Addrmode None None (inr (_memoized, Ptrofs.repr 4))) RAX ::
     (*	movl	%eax, (memoized + 4)(%rip) *)
     Pjmp_l lb1 ::
     (* jmp    .L101 *)

     Plabel lb2 ::
     (* .L102: *)
     Pmovl_rm RAX (Addrmode None None (inr (_memoized, Ptrofs.repr 4))) ::
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

Definition func_g: function :=
  mkfunction (int_int_sg) code.

Definition global_definitions : list (ident * globdef fundef unit) :=
((f_id, Gfun(External (EF_external "f" int_int_sg))) ::
  (_memoized, Gvar v_memoized) ::
  (g_id, Gfun(Internal func_g)) ::
  nil).

Definition public_idents : list ident :=
(f_id :: g_id :: nil).

Definition prog: program := mkprogram global_definitions public_idents main_id.

Definition asm_semantics := Asm.semantics prog.
