Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Server.

(** * spec in C language *)
(*

int result;
void process (int r){
  result = r;
}

void request (int i){
  encrypt (i,process);
}
*)

Definition result_id := 4%positive.
Definition process_id := 5%positive.
Definition request_id := 6%positive.

Definition result_def :=  {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition r_id := 7%positive.

Definition func_process :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (r_id,tint) :: nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body :=
      (Ssequence
         (* result = r; *)
         (Sassign (Evar result_id tint) (Evar r_id tint))
         (* return; *)
         (Sreturn None)
      )
  |}.

Definition i_id := 8%positive.
Definition func_request :=
  {|
    fn_return := Tvoid;
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
         (Sreturn None)
      )
  |}.

Definition composites : list composite_definition := nil.

Definition global_definitions_client : list (ident * globdef fundef type) :=
(encrypt_id,
   Gfun(External (EF_external "encrypt" int_fptr__void_sg)
          (Tcons tint (Tcons (Tpointer (Tfunction (Tcons tint Tnil) Tvoid cc_default) noattr)  Tnil)) tint cc_default)) ::
 (request_id, Gfun(Internal func_request)) ::
 (process_id, Gfun(Internal func_process)) ::
 (result_id, Gvar result_def) ::
 nil.

Definition public_idents_client : list ident :=
(encrypt_id :: request_id :: process_id :: result_id :: nil).

Definition client : Clight.program :=
  mkprogram composites global_definitions_client public_idents_client main_id Logic.I.

