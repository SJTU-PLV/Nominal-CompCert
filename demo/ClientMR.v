Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import Server.

(** * Specification of client_mr.c *)
(*
/* client_mr.c */
int input[N], result[N];
int index;


void request (int *r){
  if (index == 0) {
    index += 1;
    encrypt(input[index - 1], request);
  }
  else if (0 < index < N){
    result[index - 1] = *r;
    index += 1;
    encrypt(input[index - 1], request);
  }
  else {
    result[index - 1] = *r;
    return;
  }
}

===========================
MT-version of request

int input[3], result[3];
int index;


// external function provided by server, i.e. any library
// it will return the result as (pointed by) the argument
// of a given callback function
void encrypt (int input, void(*p)(int*));

// The callback functions
void process1 (int *r){
  result[1] = *r;  
}
void process2 (int *r){
  result[2] = *r;  
}
void process3 (int *r){
  result[3] = *r;  
}

// struct as argument of thread_function
typedef struct {
  int ind;
  void (*callback) (int* __);
} Arg.

// The thread function for subthreads
void* thread_function(void* a){
  Arg* arg = (Arg*) a;
  encrypt(arg->i,arg->callback);
  return NULL;
}

// request function which calls MT primitives
void request(){
  pthread_t thread[3];
  void (*callbacks[3])(int* __) = {process1, process2, process3};

  // create threads
  for (int i = 0 ; i < 3 ; ++i){
      Arg* arg = malloc(sizeof(Arg));
      arg->in = input[i];
      arg->callback = callbacks[i];
      pthread_create(&threads[i], thread_function, (void* __) arg);
  }

  // wait subthreads to complete
  for (int i = 0; i < 3 ; ++ i){\
      pthread_join(threads[i]);

  }
  //complete
  return 0;
}


*)

Section WITH_N.

Variable N: Z. 

Definition result_id := 4%positive.
Definition request_id := 3%positive.
Definition r_id := 7%positive.

Definition resultN_def :=  {|
  gvar_info := Tarray tint N noattr;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition input_id := 10%positive.
Definition inputN_def :=  {|
  gvar_info := tarray tint N;
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

(** The call instruction of encrypt with argument input *)
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

(** The expression input[index-1] *)
Definition input_index :=
  Ederef (Ebinop Oadd (Evar input_id (tarray tint N))
            (Ebinop Osub (Evar index_id tint) (Econst_int (Int.repr 1) tint) tint)
            (tptr tint)) tint.

Definition result_index :=
  Ederef (Ebinop Oadd (Evar result_id (tarray tint N))
            (Ebinop Osub (Evar index_id tint) (Econst_int (Int.repr 1) tint) tint)
            (tptr tint)) tint.

(** encrypt (input[index++], request); *)
Definition call_encrypt_indexplus :=
  Ssequence
    (* index = index + 1*)
    (Sassign (Evar index_id tint) (Ebinop Oadd (Evar index_id tint) (Econst_int (Int.repr 1) tint) tint))
    (call_encrypt' input_index).

Definition if_index_eq_0 :=
  Ebinop Oeq (Evar index_id tint) (Econst_int (Int.repr 0) tint) tbool.

Definition if_index_gt_0_lt_N :=
  Ebinop Oand
    (Ebinop Ogt (Evar index_id tint) (Econst_int (Int.repr 0) tint) tbool)
    (Ebinop Olt (Evar index_id tint) (Econst_int (Int.repr N) tint) tbool)
    tbool.

Definition tintp := tptr tint.

Definition assign_result:=
  (Sassign (result_index) (Ederef (Evar r_id tintp) tint)).

(** Definition of request  *)
Definition func_request :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (r_id,tintp) :: nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body :=
      (Sifthenelse if_index_eq_0 (** index == 0 *)
         call_encrypt_indexplus (** index+=1; encrypt (input[index-1], request) *)
         (Sifthenelse if_index_gt_0_lt_N (** 0 < index < N*)
            (Ssequence
               assign_result (** result[index] = r*)
               call_encrypt_indexplus (** index+=1; encrypt (input[index-1], request) *)
            )
            assign_result (** result[index]=r; *)
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

(** Definition of client_mr  *)
Definition client : Clight.program :=
  mkprogram composites global_definitions_client public_idents_client main_id Logic.I.

End WITH_N.
