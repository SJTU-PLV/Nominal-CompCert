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


(* Id Definitions *)

(* Compute pthread_create_id. *)
(* = 1002%positive *)

(* Compute pthread_join_id. *)
(* = 1003%positive *)

Definition a_id := 2%positive.
Definition input_id := 3%positive.
Definition result_id := 4%positive.
Definition mask_id := 5%positive.
Definition Arg_id := 106%positive.
Definition arg_id := 6%positive.
Definition i_id := 7%positive.

(*The pthread_t is simply implemented as int *)
Definition a_def :=
  {|
    gvar_info := tint;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false
  |}.

Definition init_input :=
  (Init_int32 (Int.repr 1))
  ::  (Init_int32 (Int.repr 2))
  ::  (Init_int32 (Int.repr 3))
  ::  (Init_int32 (Int.repr 4))
  ::  (Init_int32 (Int.repr 5))
  :: nil.

Definition input_def :=
  {|
    gvar_info := tarray tint 5 ;
    gvar_init := init_input;
    gvar_readonly := false;
    gvar_volatile := false
  |}.

Definition result_def :=
  {|
    gvar_info := tarray tint 5 ;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false
  |}.

Definition mask_def :=
  {|
    gvar_info := tint;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false
  |}.

(* Definition of  struct [Arg] and variable [arg] *)

Definition input_mem_id := 11%positive.
Definition result_mem_id := 12%positive.
Definition size_mem_id := 13%positive.

Definition input_mem := Member_plain input_mem_id (tptr tint).
Definition result_mem := Member_plain result_mem_id (tptr tint).
Definition size_mem := Member_plain size_mem_id (tint).

Program Definition Arg_compo : composite :=
  {|
    co_su := Struct;
    co_members := input_mem :: result_mem :: size_mem :: nil ; 
    co_attr := noattr;
    co_sizeof := 24; (* 8 + 8 + 4 -> 24 = 3*8 *)
    co_alignof := 8;
    co_rank := O;
  |}.
Next Obligation.
  exists 3%nat. reflexivity.
Qed.
Next Obligation.
  exists 3. reflexivity.
Qed.

Definition Arg_def : composite_definition :=
  Composite Arg_id Struct (input_mem :: result_mem :: size_mem :: nil) noattr.

Definition arg_def := mkglobvar
                        (Tstruct Arg_id noattr)
                        (Init_addrof input_id Ptrofs.zero :: Init_addrof result_id Ptrofs.zero :: Init_int32 (Int.repr 5) :: nil)
                        false false.

Definition i_def := mkglobvar tint nil false false.

Definition ptr__ptr_sg := mksignature (AST.Tlong  :: nil) (Tret AST.Tlong) cc_default.

(* Declaration of external function [server] *)
Definition server_id := 8%positive.
Definition func_server_external : fundef :=
  (External (EF_external "server" ptr__ptr_sg)
    (Tcons (tptr Tvoid) Tnil)
    (tptr Tvoid)
    cc_default).

Definition func_main_code : statement := Sskip. (** TODO *)

Definition func_main :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := nil;
    fn_vars := (input_id, tarray tint 5) :: (result_id, tarray tint 5) :: (arg_id, Tstruct Arg_id noattr) :: nil;
    fn_temps := (a_id, tint) :: (mask_id, tint) :: (i_id, tint) :: nil;
    fn_body := func_main_code
  |}.

Definition composites := Arg_def :: nil.

Definition global_defs_client : list (ident * globdef fundef type) :=
  (input_id, Gvar input_def) ::
  (result_id, Gvar result_def) ::
  (arg_id, Gvar arg_def) ::
  (main_id, Gfun (Internal func_main)) ::
  (server_id, Gfun func_server_external) ::
  nil.

Definition public_defs_client : list ident :=
  input_id :: result_id :: arg_id :: main_id :: server_id :: nil.

Program Definition client : Clight.program :=
  mkprogram composites global_defs_client public_defs_client main_id _.
Next Obligation.
  reflexivity.
Qed.
