Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Encrypt.
Require Import MultiLibs.


(*
# define N 5
3 typedef struct {
4 int * input , * result , size ; } Arg ;
5 void * server ( void * a ) ;
6
7 int main () {
8 pthread_t a ;
9 int input [ N ]={1 ,2 ,3 ,4 ,5} , result [ N ];
10 int mask = 0;
11 Arg arg = { input , result , N };
12
13 pthread_create (& a ,0 , server ,& arg ) ;
14 for ( int i = 0; i < N ; i ++)
15 { mask += input [ i ]; yield () ; }
16 pthread_join (a , NULL ) ;
17
18 for ( int i = 0; i < N ; i ++) {
19 result [ i ] = result [ i ] & mask ;
20 printf ( " % d ; " , result [ i ]) ; }
21 }
 *)


