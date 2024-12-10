
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers Intv.


(*
key: .long 42
encrypt:
Pallocframe 16 8 0
Pmov key RAX
Pxor RAX RDI
Pmov RDI (RSI)
Pfreeframe 16 8 0
Pret
*)

Definition main_id := (42%positive).
Definition encrypt_id := (1%positive).
Definition key_id := (2%positive).

Definition int_ptr__void_sg : signature := mksignature (AST.Tint :: AST.Tlong :: nil) Tint cc_default.

Require Import Conventions1.

Definition key_def := {|
  gvar_info := tt;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false |}.

Definition code_b1: list instruction :=
   Pallocframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     Pmovl_rm RAX (Addrmode None None (inr (key_id, Ptrofs.zero))) ::
     Pxorl_rr RDI RAX ::
     Pmov_mr_a (Addrmode (Some RSI) None (inl 0)) RDI ::
     Pfreeframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     Pret ::
     nil.

Definition func_encrypt_b1: Asm.function :=
  Asm.mkfunction (int_ptr__void_sg) code_b1.

Definition global_definitions_b1 : list (ident * globdef fundef unit) :=
  (key_id, Gvar key_def) ::
    (encrypt_id, Gfun(Internal func_encrypt_b1)) ::
  nil.

Definition public_idents : list ident :=
(key_id :: encrypt_id :: nil).

(** Top-level definition of encrypt.s  *)
Definition encrypt_s : program := mkprogram global_definitions_b1 public_idents main_id.
