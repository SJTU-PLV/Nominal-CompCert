Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Server.

(** * Specification of client.c *)

(*
/* client.c */

int result;

void encrypt(int i, void(*p)(int*));

void process (int *r){
  result = *r;
}

int request (int i){
  encrypt (i,process);
  return i;
}
*)

(** Identifier definitions *)
Definition result_id := 4%positive.
Definition process_id := 3%positive. (*the same as complete in Server definition*)
Definition request_id := 6%positive.

Definition result_def :=  {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition r_id := 7%positive.

(** Definition of the function process *)
Definition tintp := tptr tint.
Definition func_process :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (r_id,tintp) :: nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body :=
      (Ssequence
         (* result = *r; *)
         (Sassign (Evar result_id tint) (Ederef (Evar r_id tintp)  tint))
         (* return; *)
         (Sreturn None)
      )
  |}.

(** Definition of the function request *)
Definition i_id := 8%positive.
Definition func_request :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := (i_id, tint) :: nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body :=
      (Ssequence
         (* encrypt (i,process) *)
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
            ((Evar i_id tint) :: (Evar process_id (Tfunction (Tcons tint Tnil) Tvoid cc_default)) :: nil)
         )
         (Sreturn (Some (Evar i_id tint)))
      )
  |}.

Definition composites : list composite_definition := nil.

(** Declaration of the external function encrypt *)
Definition func_encrypt_external : fundef :=
  (External (EF_external "encrypt" int_fptr__void_sg)
          (Tcons tint (Tcons (Tpointer (Tfunction (Tcons tint Tnil) Tvoid cc_default) noattr)  Tnil))
          Tvoid
          cc_default).

Definition global_definitions_client : list (ident * globdef fundef type) :=
(encrypt_id,
  Gfun func_encrypt_external) ::
 (request_id, Gfun(Internal func_request)) ::
 (process_id, Gfun(Internal func_process)) ::
 (result_id, Gvar result_def) ::
 nil.

Definition public_idents_client : list ident :=
(encrypt_id :: request_id :: process_id :: result_id :: nil).

(** Definition of the client.c *)
Definition client : Clight.program :=
  mkprogram composites global_definitions_client public_idents_client main_id Logic.I.

