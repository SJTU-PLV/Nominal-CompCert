Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers Intv.

(** *Implementation of Server in Asm *)

(* C-level spec : in C code:
L1:
int key;
void encrypt (void ( *complete)(int)), int input){
  int output = input ^ key;
  complete(output);
}

L2:
const int key = 42;
void encrypt (void ( *complete)(int), int input){
  int output = input ^ key;
  complete(output)
}
*)
Definition main_id := (42%positive).
Definition encrypt_id := (1%positive).
Definition key_id := (2%positive).

Definition int__void_sg : signature := mksignature (AST.Tint :: nil) Tvoid cc_default.
Definition int_fptr__void_sg : signature := mksignature (AST.Tany64 :: AST.Tint :: nil) Tvoid cc_default.

(** registers responding to above signatures*)

Require Import Conventions1.
Compute (loc_arguments int__void_sg).
(* = if Archi.win64 then One (Locations.R Machregs.CX) :: nil else One (Locations.R Machregs.DI) :: nil *)
Compute (loc_arguments int_fptr__void_sg).
(*= if Archi.win64
       then One (Locations.R Machregs.CX) :: One (Locations.R Machregs.DX) :: nil
       else One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: nil
*)

(** * Implementation of b1.asm, corresponding to L1 *)

Definition key_def := {|
  gvar_info := tt;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

(*
L1: 
Pallocframe 16 8 0

Pmov RDI RBX //save the function pointer
Pmov key RDI //read key from memory to RDI as argument
Pxor RSI RDI //xor op
Pcall_r RBX

Pfreeframe 16 8 0
Pret

*)
Definition code_b1: list instruction :=
   (* .cfi_startproc *)
   Pallocframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     (* subq    $8, %rsp *)
     (* .cfi_adjust_cfa_offset    8 *)
     (* leaq    16(%rsp), %rax *)
     (* movq    %rax, 0(%rsp) *)
     Pmov_rr RBX RDI ::
     (* movq    %rdi, %rbx *)
     Pmovl_rm RDI (Addrmode None None (inr (key_id, Ptrofs.zero))) ::
     (* movl	memoized(%rip), %rdi *)
     Pxorl_rr RDI RSI ::
     (* xorl  %rsi %rdi *)
     Pcall_r RBX (int__void_sg) ::
     (* callr  RBX *)
     Pfreeframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     (* addq    $8, %rsp *)
     Pret ::
       (* ret *)
     nil.

Definition func_encrypt_b1: Asm.function :=
  Asm.mkfunction (int_fptr__void_sg) code_b1.

Definition global_definitions_b1 : list (ident * globdef fundef unit) :=
  (key_id, Gvar key_def) ::
  (encrypt_id, Gfun(Internal func_encrypt_b1)) ::
  nil.

Definition public_idents : list ident :=
(key_id :: encrypt_id :: nil).

Definition b1: program := mkprogram global_definitions_b1 public_idents main_id.

(** * Implementation of b2.asm, corresponding to L2 *)

Definition key_def_const := {|
  gvar_info := tt;
  gvar_init := Init_int32 (Int.repr 42) :: nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(*
L1: 
Pallocframe 16 8 0

Pmov RDI RBX //save the function pointer
Pmov key RDI //read key from memory to RDI as argument
Pxor RSI RDI //xor op
Pcall_r RBX

Pfreeframe 16 8 0
Pret

*)
Definition code_b2: list instruction :=
   (* .cfi_startproc *)
   Pallocframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     (* subq    $8, %rsp *)
     (* .cfi_adjust_cfa_offset    8 *)
     (* leaq    16(%rsp), %rax *)
     (* movq    %rax, 0(%rsp) *)
     Pmov_rr RBX RDI ::
     (* movq    %rdi, %rbx *)
     Pxorl_ri RDI (Int.repr 42) ::
     (* xorli  42 %rdi *)
     Pcall_r RBX (int__void_sg) ::
     (* callr  RBX *)
     Pfreeframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     (* addq    $8, %rsp *)
     Pret ::
       (* ret *)
     nil.

Definition func_encrypt_b2: Asm.function :=
  Asm.mkfunction (int_fptr__void_sg) code_b2.

Definition global_definitions_b2 : list (ident * globdef fundef unit) :=
  (key_id, Gvar key_def) ::
  (encrypt_id, Gfun(Internal func_encrypt_b2)) ::
  nil.

Definition b2: program := mkprogram global_definitions_b2 public_idents main_id.
