Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Encrypt.
Require Import MultiLibs.

(*
2 void encrypt ( int i , int * r ) ;
3 void * server ( void * a ) {
4 int * i = (( Arg * ) a ) -> input ;
5 int * r = (( Arg * ) a ) -> result ;
6 int size = (( Arg * ) a ) -> size ;
7
8 for ( int j = 0; j < size ; j ++) {
9 encrypt ( input [ j ] , result + j ) ;
10 yield () ; }
11 return NULL ;
12 }
*)

(** Declaration of external function [encrypt] *)
Definition func_encrypt_external : fundef :=
  (External (EF_external "encrypt" int_ptr__void_sg)
          (Tcons tint (Tcons (tptr tint)  Tnil))
          Tvoid
          cc_default).

(** Definition of function [server] *)
Definition func_server :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (i,)
  |}
