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
  Int.repr sumz
.

Definition int_int_sg : signature := mksignature (AST.Tint :: nil) (Tret Tint) cc_default.

(*


A.spec                          B.spec 1

SIM (cc_c injp -> cc_c injp)

A.c

                                SIM: cc_compcert -> cc_compcert
cc_compcert -> cc_compcert


A.asm                           B.asm

================================


            AB.spec

         cc_c injp -> cc_c injp

          A.spec + B.spec

         cc_compcert -> cc_compcert

         A.asm + B.asm

===============================

AB.spec

cc_compcert -> cc_compcert

A.asm + B.asm

*)
