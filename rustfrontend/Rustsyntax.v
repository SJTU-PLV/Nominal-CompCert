Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import LanguageInterface.

(** The rust surface syntax *)

Inductive expr : Type :=
| Eval (v: val) (ty: type)                                  (**r constant *)
| Evar (x: ident) (ty: type)                                (**r variable *)
| Ebox (r: expr) (ty: type)                                 (**r allocate a heap block *)
| Efield (l: expr) (f: ident) (ty: type) (**r access to a member of a struct *)
| Ederef (r: expr) (ty: type)        (**r pointer dereference (unary [*]) *)
| Eunop (op: unary_operation) (r: expr) (ty: type)
(**r unary arithmetic operation *)
| Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
                                           (**r binary arithmetic operation *)
| Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
| Ecall (r1: expr) (rargs: exprlist) (ty: type)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

Definition typeof (e: expr) : type :=
  match e with
  | Eval _ ty
  | Evar _ ty
  | Ebox _ ty
  | Efield _ _ ty
  | Ederef _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty                  
  | Eassign _ _ ty
  | Ecall _ _ ty => ty
end.

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Sdo : expr -> statement            (**r evaluate expression for side effects *)
| Slet: ident -> type -> statement -> statement  (**r [Slet id ty] opens a new scope with one variable of type ty *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Swhile : expr -> statement -> statement   (**r [while] loop *)
| Sloop: statement -> statement                               (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : option expr -> statement     (**r [return] statement *)
| Smatch : expr -> arm_statements -> statement  (**r pattern match statements *)

with arm_statements : Type :=            (**r cases of a [match] *)
  | ASnil: arm_statements
  | AScons: option (ident * ident) -> statement -> arm_statements -> arm_statements.
                      (**r [None] is [default], [Some (fid, id)] is [case fid (id)] *)


Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type); 
  fn_body: statement
}.  

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

(* Type of function *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External _ ef typs typ cc =>     
      Tfunction typs typ cc                
  end.

(** Notations for Rustsyntax programs *)

Definition A : ident := 1%positive.
Definition B : ident := 2%positive.
Definition C : ident := 3%positive.
Definition D : ident := 4%positive.
Definition E : ident := 5%positive.
Definition F : ident := 6%positive.
Definition G : ident := 7%positive.
Definition H : ident := 8%positive.
Definition I : ident := 9%positive.


Declare Custom Entry rustsyntax.
Declare Scope rustsyntax_scope.
Declare Custom Entry rustsyntax_aux.

Notation "<{ s }>" := s (s custom rustsyntax_aux) : rustsyntax_scope.
Notation "s" := s (in custom rustsyntax_aux at level 0, s custom rustsyntax) : rustsyntax_scope.

(* uncomment it would disable the pretty-print *)
(* Notation " x " := x (in custom rustsyntax at level 0, x global). (* It indicate that the custom entry should parse global *) *)

(* Notations for statement *)
Notation "'if' e 'then' s1 'else' s2 'endif'" := (Sifthenelse e s1 s2) (in custom rustsyntax at level 80, s1 at level 99, s2 at level 99) : rustsyntax_scope.
Notation "s1 ; s2" := (Ssequence s1 s2) (in custom rustsyntax at level 99, right associativity) : rustsyntax_scope.
Notation "'do' e" := (Sdo e) (in custom rustsyntax at level 80, e at level 20) : rustsyntax_scope.
Notation "'skip'" := Sskip (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'break'" := Sbreak (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'continue'" := Scontinue (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'return0'" := (Sreturn None) (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'return' e" := (Sreturn (@Some expr e)) (in custom rustsyntax at level 80, e at level 20) : rustsyntax_scope.
Notation "'let' x : t 'in' s 'endlet' " := (Slet x t s) (in custom rustsyntax at level 80, s at level 99, x global, t global) : rustsyntax_scope.
Notation "'loop' s 'endloop'" := (Sloop s) (in custom rustsyntax at level 80, s at level 99) : rustsyntax_scope.
Notation "'while' e 'do' s 'endwhile'" := (Swhile e s) (in custom rustsyntax at level 80, e at level 20, s at level 99) : rustsyntax_scope.
Notation "'match' e 'with' 'case' fid 'as' id '=>' stmt 'endmatch' " := (Smatch e (AScons (Some (fid,id)) stmt ASnil)) (in custom rustsyntax at level 80, fid global, id global) : rustsyntax_scope.
Notation "'match' e 'with' 'case' fid1 'as' id1 '=>' stmt1 'case' fid2 'as' id2 '=>' stmt2 'endmatch' " := (Smatch e (AScons (Some (fid1,id1)) stmt1 (AScons (Some (fid2,id2)) stmt2 ASnil))) (in custom rustsyntax at level 80, fid1 global, id1 global, fid2 global, id2 global) : rustsyntax_scope.
(* Notation "'match' e 'with' arm1 ';' arm2 ';' .. ';' arm3 'endmatch' " := (Smatch e (AScons (fst arm1) (snd arm1) (AScons (fst arm2) (snd arm2) .. (AScons (fst arm3) (snd arm3) ASnil) .. ))) (in custom rustsyntax at level 80) : rustsyntax_scope. *)

(* Notations for expression *)

(* expression is at level 20 *)
Notation " ( x ) " := x (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " x # t " := (Evar x t) (in custom rustsyntax at level 0, x global, t global)  : rustsyntax_scope.
Notation "'Box' ( e )" := (Ebox e (Tbox (typeof e) noattr)) (in custom rustsyntax at level 10, e at level 20)  : rustsyntax_scope.
Notation " ! e " := (Ederef e (deref_type (typeof e))) (in custom rustsyntax at level 10, e at level 20) : rustsyntax_scope.
Notation " 'field' '(' e ',' x ',' t ')' " := (Efield e x t) (in custom rustsyntax at level 10, x global, t global, e at level 20) : rustsyntax_scope.
Notation " l := r " := (Eassign l r Tunit) (in custom rustsyntax at level 17, r at level 20) : rustsyntax_scope.
Notation " { x , .. , y } " := (Econs x .. (Econs y Enil) .. ) (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " f @ l " := (Ecall f l) (in custom rustsyntax at level 10, l at level 10) : rustsyntax_scope.
Notation " e1 < e2 " := (Ebinop Ole e1 e2 type_bool) (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " $ k " := (Eval (Vint (Int.repr k)) type_int32s) (in custom rustsyntax at level 10, k constr) : rustsyntax_scope.
Notation " e1 * e2 " := (Ebinop Omul e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " e1 - e2 " := (Ebinop Osub e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.


(* Print Grammar constr. *)
(* Print Custom Grammar rustsyntax. *)

Open Scope rustsyntax_scope.

Definition var_a : expr := <{ A # type_int32s }>.
Definition box_a : expr := <{ Box(A # type_int32s) }>.
(* Definition deref_box_a_global : expr := <{ ! box_a }>. *)
Definition deref_box_a : expr := <{ ! Box(A # type_int32s) }>.

Definition box_int := Tbox type_int32s noattr.

(* test match statement notation *)

Definition match_test :=
  <{ match ($1) with
       case A as A =>
         skip
       case B as C =>
         skip
     endmatch
    }>.
         
(* InitAnalysis Test 1 *)

Definition init_test1_body :=
  <{ let A : box_int in
     do (A#box_int) := Box($3);
     let B : box_int in
     do (B#box_int) := (A#box_int)
     endlet
     endlet }>.

Definition init_test1 :=
  {| fn_return := Tunit;
    fn_callconv := cc_default;
    fn_params := nil;
    fn_body := init_test1_body |}.

(* InitAnalysis Test 2 *)

Definition init_test2_body :=
  <{ let A : box_int in
     do (A#box_int) := (C#box_int);
     let B : box_int in
     do (B#box_int) := (A#box_int)
     endlet
     endlet }>.

Definition init_test2 :=
  {| fn_return := Tunit;
    fn_callconv := cc_default;
    fn_params := (C, box_int) :: nil;
    fn_body := init_test2_body |}.


(* Example 1 *)

Definition ex1_body :=
  <{ do (A#type_int32s) := !(B#box_int);
     let C : box_int in
     if ((A#type_int32s) < !(B#box_int)) then
       do (C#box_int) := (B#box_int)
     else
       do (B#box_int) := Box($3)
     endif
     endlet
    }>.

Definition ex1 : function :=
  {| fn_return := Tunit;
    fn_callconv := cc_default;
    fn_params := (A , type_int32s) :: (B , box_int) :: nil;
    fn_body := ex1_body |}.
                                   

(* Example 2 *)


(* Print Custom Grammar rustsyntax. *)

Definition N : ident := 30%positive.

Definition fact (n: Z) :=
  <{ let N : type_int32s in
     do (N#type_int32s) := $n;
     let A : type_int32s in
     do (A#type_int32s) := $1;
     let B : box_int in
     do (B#box_int) := Box(A#type_int32s);
     while (($0) < (N#type_int32s)) do
       let C : box_int in
       do (C#box_int) := Box(!B#box_int); (* comment it to check the init analysis *)
       do (!(C#box_int)) := (!(B#box_int)) * (N#type_int32s);
       do (N#type_int32s) := (N#type_int32s) - $1;
       do (B#box_int) := (C#box_int)
       endlet
     endwhile;
     return (B#box_int)
     endlet endlet endlet
    }>.

Definition ex2 : function :=
  {| fn_return := box_int;
    fn_callconv := cc_default;
    fn_params := nil;
    fn_body := fact 10 |}.


(* Example 3 *)

Definition fact1 (n: Z) :=
  <{ let N : type_int32s in
     do (N#type_int32s) := $n;
     let A : type_int32s in
     do (A#type_int32s) := $1;
     let B : box_int in
     do (B#box_int) := Box(A#type_int32s);
     while ($1) do
       let C : box_int in
       do (C#box_int) := Box(!B#box_int); (* comment it to check the init analysis *)
       if (($0) < (N#type_int32s)) then
         do (!(C#box_int)) := (!(B#box_int)) * (N#type_int32s);
         do (N#type_int32s) := (N#type_int32s) - $1;
         do (B#box_int) := (C#box_int);
         continue
       else break
       endif
       endlet        
     endwhile;
     return (B#box_int)
     endlet endlet endlet
    }>.

Definition ex3 : function :=
  {| fn_return := box_int;
    fn_callconv := cc_default;
    fn_params := nil;
    fn_body := fact1 10 |}.

(* [list] type *)
Definition list_id := 102%positive.
Definition list_ty := Tvariant list_id noattr.
Definition box_list := Tbox list_ty noattr.

(* Define [pair] composite *)

Definition pair_id := 110%positive.

Definition first_id := 111%positive.

Definition second_id := 112%positive.

Definition pair_first := Member_plain first_id type_int32s.

Definition pair_second_ty := box_list.

Definition pair_second := Member_plain second_id pair_second_ty.

Definition pair_codef : composite_definition :=
  Composite pair_id Struct (pair_first :: pair_second :: nil) noattr.

Definition nil_id := 100%positive.

Definition rnil := Member_plain nil_id Tunit.

Definition cons_id := 101%positive.

Definition rcons (ty: type) := Member_plain cons_id ty.

Definition pair_ty := (Tstruct pair_id noattr).

Definition list_codef : composite_definition :=
  Composite list_id TaggedUnion (rnil :: rcons pair_ty :: nil) noattr.

Definition list_comp_env : res composite_env :=
  build_composite_env (pair_codef :: list_codef :: nil).

(* Compute list_comp_env. *)

Program Definition pair_composite : composite :=
  {| co_sv := Struct;
    co_members := (pair_first :: pair_second :: nil);
    co_attr := noattr;
    co_sizeof := 16;
    co_alignof := 8;
    co_rank := 0 |}.
Next Obligation.
exists 3%nat. auto.
Defined.
Next Obligation.
replace 16 with (2*8) by lia.
eapply Z.divide_factor_r.
Defined.

Program Definition list_composite : composite :=
  {| co_sv := TaggedUnion;
    co_members := (rnil :: rcons pair_ty :: nil);
    co_attr := noattr;
    co_sizeof := 24;
    co_alignof := 8;
    co_rank := 1 |}.
Next Obligation.
exists 3%nat. auto.
Defined.
Next Obligation.
replace 24 with (3*8) by lia.
eapply Z.divide_factor_r.
Defined.

(* Define the program which uses list *)

Definition arm1 := 201%positive.
Definition arm2 := 202%positive.

(* A: box_list, B: int, pop an element and push B, if it is empty, just
push B, return type is box_list *)
Definition pop_and_push :=
  <{ let C: pair_ty in          (* to push *)
     let D: box_list in          (* return value *)
     (* C.1 = B *)
     do (field(C#pair_ty, first_id, type_int32s)) := B#type_int32s;
     match (!(A#box_list)) with
     case nil_id as arm1 =>
       let E: list_ty in       (* convert arm1 to list *)
       let F: box_list in
       do (E#list_ty) := (arm1#Tunit); (* variant assignment *)
       do (F#box_list) := Box(E#list_ty);
       (* C.2 = F *)
       do (field(C#pair_ty, second_id, box_list)) := F#box_list
       endlet
       endlet                                               
     case cons_id as arm2 =>
       (* arm2 has type pair_ty *)
       (* C.2 = arm.2 *)
       do (field(C#pair_ty, second_id, box_list)) := (field(arm2#pair_ty, second_id, box_list))
       (* how to release the popped element *)
      endmatch;
      let G: list_ty in
      do (G#list_ty) := C#pair_ty;
      do (D#box_list) := Box(G#list_ty);
      return (D#box_list)
      endlet endlet endlet
        }>.

Definition pop_and_push_func : function :=
  {| fn_return := box_list;
    fn_callconv := cc_default;
    fn_params := (A, box_list) :: (B, type_int32s) :: nil;
    fn_body := pop_and_push |}.

Definition pop_and_push_fundef : globdef (Rusttypes.fundef function) type :=
  Gfun (Internal pop_and_push_func).

Definition pop_and_push_comp_env : composite_env :=
  PTree.set list_id list_composite (PTree.set pair_id pair_composite (PTree.empty composite)).

(* main function *)


Program Definition pop_and_push_prog : program :=
  {| prog_defs := (300%positive, pop_and_push_fundef) :: nil;
    prog_public := 300%positive :: nil;
    prog_main := 42%positive;
    prog_types := (pair_codef :: list_codef :: nil);
    prog_comp_env := pop_and_push_comp_env;
    prog_comp_env_eq := _ |}.
Next Obligation.
Admitted.


  
