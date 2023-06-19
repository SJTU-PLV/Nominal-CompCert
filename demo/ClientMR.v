Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Server.

(** * spec in C language *)
(*

int input[N], result[N];
int index;

void request (int r){
  if (index == 0) {
    encrypt (input[index++], request);
  }
  else if (0 < index <= N){
    result [index - 1] = r;
    encrypt (input[index++], request);
  }
  else return;
}
*)

Definition result_id := 4%positive.
Definition request_id := 3%positive.
Definition r_id := 7%positive.

Definition N := 10%positive.

Definition resultN_def :=  {|
  gvar_info := Tarray tint 10 noattr;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition input_id := 10%positive.
Definition inputN_def :=  {|
  gvar_info := tarray tint 10;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition index_id := 11%positive.
Definition index_def :=  {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

(* The call instruction of encrypt with argument input *)
Definition call_encrypt' input :=
  (Scall None
            (*function name and signature*)
            (Evar encrypt_id
               (Tfunction
                  (*argument types*)
                  (Tcons tint (*int*)
                     (Tcons (Tpointer (Tfunction (Tcons tint Tnil) Tvoid cc_default) noattr) (*function pointer*)
                        Tnil))
                  Tvoid cc_default)
            )
            (*arguments*)
            (input :: (Evar request_id (Tfunction (Tcons tint Tnil) Tvoid cc_default)) :: nil)
  ).

(* the expr input[index] *)
Definition input_index :=
  Ederef (Ebinop Oadd (Evar input_id (tarray tint 10)) (Evar index_id tint) (tptr tint)) tint.

Definition result_index :=
  Ederef (Ebinop Oadd (Evar result_id (tarray tint 10)) (Evar index_id tint) (tptr tint)) tint.

(* encrypt (input[index++], request); *)
Definition call_encrypt_indexplus :=
  Ssequence
    (* index = index + 1*)
    (Sassign (Evar index_id tint) (Ebinop Oadd (Evar index_id tint) (Econst_int (Int.repr 1) tint) tint))
    (call_encrypt' input_index).

Definition if_index_eq_0 :=
  Ebinop Oeq (Evar index_id tint) (Econst_int (Int.repr 0) tint) tbool.

Definition if_index_gt_0_le_N :=
  Ebinop Oand
    (Ebinop Ogt (Evar index_id tint) (Econst_int (Int.repr 0) tint) tbool)
    (Ebinop Ole (Evar index_id tint) (Econst_int (Int.repr 10) tint) tbool)
    tbool.

Definition func_request :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (r_id,tint) :: nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body :=
      (Sifthenelse if_index_eq_0 (** index == 0*)
         call_encrypt_indexplus (** encrypt (input[index++], request) *)
         (Sifthenelse if_index_gt_0_le_N (** 0 < index <= N*)
            (Ssequence
               (Sassign (result_index) (Etempvar r_id tint)) (** result[index] = r*)
               call_encrypt_indexplus (** encrypt (input[index++], request) *)
            )
            (Sreturn None) (** return; *)
         )
      )
  |}.

Definition composites : list composite_definition := nil.

Definition func_encrypt_external : fundef :=
  (External (EF_external "encrypt" int_fptr__void_sg)
          (Tcons tint (Tcons (Tpointer (Tfunction (Tcons tint Tnil) Tvoid cc_default) noattr)  Tnil))
          Tvoid
          cc_default).

Definition global_definitions_client : list (ident * globdef fundef type) :=
(encrypt_id,
 Gfun func_encrypt_external) ::
  (request_id, Gfun(Internal func_request)) ::
 (input_id, Gvar inputN_def) ::
 (result_id, Gvar resultN_def) ::
 (index_id, Gvar index_def) ::
 nil.

Definition public_idents_client : list ident :=
(encrypt_id :: request_id :: input_id :: result_id :: index_id :: nil).

Definition client : Clight.program :=
  mkprogram composites global_definitions_client public_idents_client main_id Logic.I.

