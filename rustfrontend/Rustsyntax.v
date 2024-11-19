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

Import ListNotations.

(** The rust surface syntax *)

Inductive expr : Type :=
| Eval ( v: val) (ty: type)                                  (**r constant *)
| Eunit                     (**r unit expression which evaluated to zero  *)
| Estruct (id: ident) (fl: list ident) (l: exprlist) (ty: type) (**r structure construction  *)
| Eenum (id: ident) (fid: ident) (e: expr) (ty: type)       (**r enum construction  *)
| Evar (x: ident) (ty: type)                                (**r variable *)
| Ebox (r: expr) (ty: type)                                 (**r allocate a heap block *)
| Eref (org: origin) (mut: mutkind) (l: expr) (ty: type)                  (**r &[mut] e *)
| Efield (l: expr) (f: ident) (ty: type) (**r access to a member of a struct *)
| Ederef (r: expr) (ty: type)        (**r pointer dereference (unary [*]) *)
| Eunop (op: unary_operation) (r: expr) (ty: type)
(**r unary arithmetic operation *)
| Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
                                           (**r binary arithmetic operation *)
| Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
| Ecall (r1: expr) (rargs: exprlist) (ty: type)
| Eglobal (id: ident) (ty: type) (**r constant global variable  *)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

Definition typeof (e: expr) : type :=
  match e with
  | Eunit
  | Eassign _ _ _ => Tunit
  | Estruct _ _ _ ty
  | Eenum _ _ _ ty
  | Eval _ ty
  | Evar _ ty
  | Ebox _ ty
  | Eref _ _ _ ty
  | Efield _ _ ty
  | Ederef _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty
  | Ecall _ _ ty => ty
  | Eglobal _ ty => ty
end.

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Sdo : expr -> statement            (**r evaluate expression for side effects *)
| Slet: ident -> type -> option expr -> statement -> statement  (**r [Slet id ty := e] opens a new scope with one variable of type ty *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Swhile : expr -> statement -> statement   (**r [while] loop *)
| Sloop: statement -> statement                               (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : expr -> statement     (**r [return e] statement where e must be a specific return variable (Evar retv) generated in Rustsurface *)
| Smatch : expr -> arm_statements -> statement  (**r pattern match statements *)

with arm_statements : Type :=            (**r cases of a [match] *)
  | ASnil: arm_statements
  | AScons: option (ident * ident) -> statement -> arm_statements -> arm_statements.
                      (**r [None] is [default], [Some (fid, id)] is [case fid (id)] *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue: option ident;   (* It indicates that this function is the drop glue for composite id *)
  (* For now, every function must have a specific return variable *)
  fn_return: (ident * type);
  fn_callconv: calling_convention;  
  fn_params: list (ident * type); 
  fn_body: statement
}.  

(* Since it is a drop glue, the return variable is irrelevant *)
Definition empty_drop_function id := mkfunction [] [] (Some id) (1%positive, Tunit) cc_default [] Sskip.

Definition fundef := Rusttypes.fundef function.

Definition empty_drop_fundef id := Internal (empty_drop_function id).
Definition empty_drop_globdef id : globdef fundef type := Gfun (empty_drop_fundef id).

Definition program := Rusttypes.program function.


(** External function examples  *)

(* printf : args are arguments, targs are the types of arguments *)
(* Definition printf_builtin (args: exprlist) (targs: typelist) :=
  let callcc := mkcallconv (Some 1) false false in
  Ebuiltin (EF_external "printf" (signature_of_type targs type_int32s callcc)) targs args type_int32s. *)


(* Type of function *)

Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (snd (fn_return f)) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc                
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
(* Notation "'return0'" := (Sreturn (Evar ) (in custom rustsyntax at level 0) : rustsyntax_scope. *)
Notation "'return' e" := (Sreturn e) (in custom rustsyntax at level 80, e at level 20) : rustsyntax_scope.
Notation "'let' x : t 'in' s 'endlet' " := (Slet x t None s) (in custom rustsyntax at level 80, s at level 99, x global, t global) : rustsyntax_scope.
Notation "'let' x : t ':=' e 'in' s 'endlet' " := (Slet x t (Some e) s) (in custom rustsyntax at level 80, s at level 99, x global, t global, e at level 20) : rustsyntax_scope.
Notation "'loop' s 'endloop'" := (Sloop s) (in custom rustsyntax at level 80, s at level 99) : rustsyntax_scope.
Notation "'while' e 'do' s 'endwhile'" := (Swhile e s) (in custom rustsyntax at level 80, e at level 20, s at level 99) : rustsyntax_scope.
Notation "'match' e 'with' 'case' fid 'as' id '=>' stmt 'endmatch' " := (Smatch e (AScons (Some (fid,id)) stmt ASnil)) (in custom rustsyntax at level 80, fid global, id global) : rustsyntax_scope.
Notation "'match' e 'with' 'case' fid1 'as' id1 '=>' stmt1 'case' fid2 'as' id2 '=>' stmt2 'endmatch' " := (Smatch e (AScons (Some (fid1,id1)) stmt1 (AScons (Some (fid2,id2)) stmt2 ASnil))) (in custom rustsyntax at level 80, fid1 global, id1 global, fid2 global, id2 global) : rustsyntax_scope.
(* Notation "'match' e 'with' arm1 ';' arm2 ';' .. ';' arm3 'endmatch' " := (Smatch e (AScons (fst arm1) (snd arm1) (AScons (fst arm2) (snd arm2) .. (AScons (fst arm3) (snd arm3) ASnil) .. ))) (in custom rustsyntax at level 80) : rustsyntax_scope. *)

(* Notations for expression *)

(* expression is at level 20 *)
Notation " ( x ) " := x (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " x # t " := (Evar x t) (in custom rustsyntax at level 0, x global, t global)  : rustsyntax_scope.
Notation "'Box' ( e )" := (Ebox e (Tbox (typeof e) )) (in custom rustsyntax at level 10, e at level 20)  : rustsyntax_scope.
Notation " '&' 'mut' e " := (Eref e Mutable (Treference (typeof e) Mutable )) (in custom rustsyntax at level 10, e at level 20)  : rustsyntax_scope.
Notation " '&'  e " := (Eref e Immutable (Treference (typeof e) Immutable )) (in custom rustsyntax at level 10, e at level 20)  : rustsyntax_scope.
Notation " ! e " := (Ederef e (deref_type (typeof e))) (in custom rustsyntax at level 10, e at level 20) : rustsyntax_scope.
Notation " 'field' '(' e ',' x ',' t ')' " := (Efield e x t) (in custom rustsyntax at level 10, x global, t global, e at level 20) : rustsyntax_scope.
Notation " l := r " := (Eassign l r Tunit) (in custom rustsyntax at level 17, r at level 20) : rustsyntax_scope.
Notation " { } " := Enil (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " { x } " := (Econs x Enil ) (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " { x , .. , y } " := (Econs x .. (Econs y Enil) .. ) (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " 'struct' '(' s ',' fids ',' args ',' ty ')' " := (Estruct s fids args ty) (in custom rustsyntax at level 10, s global, fids constr, args at level 20, ty global) : rustsyntax_scope.
Notation " 'enum' '(' s ',' fid ',' arg ',' ty ')' " := (Eenum s fid arg ty) (in custom rustsyntax at level 10, s global, fid global, arg at level 20, ty global) : rustsyntax_scope.
Notation "'Call' f @ l " := (Ecall f l (return_type (typeof f))) (in custom rustsyntax at level 10, l at level 20, f at level 20) : rustsyntax_scope.
Notation " e1 < e2 " := (Ebinop Ole e1 e2 type_bool) (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " $ k " := (Eval (Vint (Int.repr k)) type_int32s) (in custom rustsyntax at level 10, k constr) : rustsyntax_scope.
Notation " 'tt' " := (Eunit) (in custom rustsyntax at level 10) : rustsyntax_scope.
Notation " e1 * e2 " := (Ebinop Omul e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " e1 - e2 " := (Ebinop Osub e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.


(* Print Grammar constr. *)
(* Print Custom Grammar rustsyntax. *)

Open Scope rustsyntax_scope.

Definition var_a : expr := <{ A # type_int32s }>.
Definition box_a : expr := <{ Box(A # type_int32s) }>.
(* Definition deref_box_a_global : expr := <{ ! box_a }>. *)
Definition deref_box_a : expr := <{ ! Box(A # type_int32s) }>.

Definition box_int := Tbox type_int32s.

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
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_return := (1%positive, Tunit);
    fn_drop_glue := None;
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
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := (1%positive, Tunit);
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
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := (1%positive, Tunit);
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
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
        fn_drop_glue := None;
    fn_return := (1%positive, box_int);
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
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
        fn_drop_glue := None;
    fn_return := (1%positive, box_int);
    fn_callconv := cc_default;
    fn_params := nil;
    fn_body := fact1 10 |}.

(* [list] type *)
Definition list_id := 102%positive.
Definition list_ty := Tvariant nil list_id .
Definition box_list := Tbox list_ty .

(* Define [pair] composite *)

Definition list_node_id := 110%positive.

Definition first_id := 111%positive.

Definition second_id := 112%positive.

Definition list_node_first := Member_plain first_id type_int32s.

Definition list_node_second_ty := box_list.

Definition list_node_second := Member_plain second_id list_node_second_ty.

Definition list_node_codef : composite_definition :=
  Composite list_node_id Struct (list_node_first :: list_node_second :: nil) nil nil.

Definition nil_id := 100%positive.

Definition rnil := Member_plain nil_id Tunit.

Definition cons_id := 101%positive.

Definition rcons (ty: type) := Member_plain cons_id ty.

Definition list_node_ty := (Tstruct nil list_node_id ).

Definition list_codef : composite_definition :=
  Composite list_id TaggedUnion (rnil :: rcons list_node_ty :: nil) nil nil.

Definition list_comp_env : res composite_env :=
  build_composite_env (list_node_codef :: list_codef :: nil).

(* Compute list_comp_env. *)

Program Definition list_node_composite : composite :=
  {|co_generic_origins := nil;
    co_origin_relations := nil;
    co_sv := Struct;
    co_members := (list_node_first :: list_node_second :: nil);    
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
  {|co_generic_origins := nil;
    co_origin_relations := nil;
    co_sv := TaggedUnion;
    co_members := (rnil :: rcons list_node_ty :: nil);    
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
(* Definition pop_and_push := *)
(*   <{ let C: list_node_ty in          (* to push *) *)
(*      let D: box_list in          (* return value *) *)
(*      (* C.1 = B *) *)
(*      do (field(C#list_node_ty, first_id, type_int32s)) := B#type_int32s; *)
(*      match (!(A#box_list)) with *)
(*      case nil_id as arm1 => *)
(*        let E: list_ty in       (* convert arm1 to list *) *)
(*        let F: box_list in *)
(*        do (E#list_ty) := (arm1#Tunit); (* variant assignment *) *)
(*        do (F#box_list) := Box(E#list_ty); *)
(*        (* C.2 = F *) *)
(*        do (field(C#list_node_ty, second_id, box_list)) := F#box_list *)
(*        endlet *)
(*        endlet                                                *)
(*      case cons_id as arm2 => *)
(*        (* arm2 has type list_node_ty *) *)
(*        (* C.2 = arm.2 *) *)
(*        do (field(C#list_node_ty, second_id, box_list)) := (field(arm2#list_node_ty, second_id, box_list)) *)
(*        (* how to release the popped element *) *)
(*       endmatch; *)
(*       let G: list_ty in *)
(*       do (G#list_ty) := C#list_node_ty; *)
(*       do (D#box_list) := Box(G#list_ty); *)
(*       return (D#box_list) *)
(*       endlet endlet endlet *)
(*         }>. *)

Definition pop_and_push :=
  <{ let C: list_node_ty in     (* C is head *)
     (* C.1 = B *)
     do (field(C#list_node_ty, first_id, type_int32s)) := B#type_int32s;
     match (!(A#box_list)) with
       case nil_id as arm1 =>       
       (* C.2 = Box(nil(arm1)) *)
       do (field(C#list_node_ty, second_id, box_list)) := Box(enum(list_id, nil_id, arm1#Tunit, list_ty))
       case cons_id as arm2 =>
       (* C.2 = Box(cons(arm2)) *)
       do (field(C#list_node_ty, second_id, box_list)) := Box(enum(list_id, cons_id, arm2#list_node_ty, list_ty))
     endmatch;
     return Box(enum(list_id, cons_id, C#list_node_ty, list_ty))
     endlet }>.
            
Definition pop_and_push_func : function :=
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
        fn_drop_glue := None;
    fn_return := (1%positive, box_list);
    fn_callconv := cc_default;    
    fn_params := (A, box_list) :: (B, type_int32s) :: nil;
    fn_body := pop_and_push |}.

Definition pop_and_push_fundef : globdef (Rusttypes.fundef function) type :=
  Gfun (Internal pop_and_push_func).

Definition pop_and_push_comp_env : composite_env :=
  PTree.set list_id list_composite (PTree.set list_node_id list_node_composite (PTree.empty composite)).

Definition pop_and_push_ident : ident := 300%positive.
Definition pop_and_push_ty : type := Tfunction nil nil (Tcons box_list (Tcons type_int32s Tnil)) box_list cc_default.

Import ListNotations.

(* main function *)
Definition main_body :=
  <{ let A : list_ty := enum(list_id, nil_id, tt, list_ty) in     
     let B : list_node_ty := struct(list_node_id, [first_id;second_id], {$42, Box(A#list_ty)}, list_node_ty) in
     do (A#list_ty) := enum(list_id, cons_id, B#list_node_ty, list_ty);
     let C : box_list := Box(A#list_ty) in
     do (C#box_list) := Call (pop_and_push_ident#pop_and_push_ty) @ {(C#box_list), ($-2)};
     return ($0)
     endlet endlet endlet }>.

Definition main_func : function :=
  {|fn_generic_origins := nil;
    fn_origins_relation := nil;
        fn_drop_glue := None;
    fn_return := (1%positive, type_int32s);
    fn_callconv := cc_default;
    fn_params := nil;
    fn_body := main_body |}.

Definition main_fundef : globdef (Rusttypes.fundef function) type := Gfun (Internal main_func).

Definition main_ident : ident := 301%positive.

Definition pop_and_push_comp_defs := (list_node_codef :: list_codef :: nil).

Definition wf_composites (types: list composite_definition) : Prop :=
  match build_composite_env types with OK _ => True | Error _ => False end.

Definition build_composite_env' (types: list composite_definition)
                                (WF: wf_composites types)
                             : { ce | build_composite_env types  = OK ce }.
Proof.
  revert WF. unfold wf_composites. case (build_composite_env types); intros.
- exists c; reflexivity.
- contradiction.
Defined.

Definition wf_pop_and_push_types : wf_composites pop_and_push_comp_defs.
Proof.
  unfold wf_composites. simpl. auto.
Defined.

(* Comment it because we add drop_glue map in program definitions *)
(* Definition pop_and_push_prog : program := *)
(*   let (ce, EQ) := build_composite_env' pop_and_push_comp_defs wf_pop_and_push_types in *)
(*   {| prog_defs := (pop_and_push_ident, pop_and_push_fundef) :: (main_ident, main_fundef) :: nil; *)
(*     prog_public := pop_and_push_ident :: main_ident :: nil; *)
(*     prog_main := main_ident; *)
(*     prog_types := pop_and_push_comp_defs; *)
(*     prog_comp_env := ce; *)
(*     prog_comp_env_eq := EQ |}. *)


  
(* (* Example 5: test partial ownership transfer *) *)

(* Definition l_id : ident := 101%positive. *)
(* Definition m_id : ident := 102%positive. *)
(* Definition n_id : ident := 103%positive. *)
(* Definition S1_id : ident := 100%positive. *)
(* Definition l_ty : type := box_int. *)
(* Definition m_ty : type := box_int. *)
(* Definition n_ty : type := type_int32s. *)
(* Definition S1 : composite_definition := *)
(*   Composite S1_id Struct ([Member_plain l_id l_ty; Member_plain m_id m_ty; Member_plain n_id n_ty]) noattr nil nil. *)
(* Definition S1_ty : type := Tstruct nil S1_id noattr. *)

(* Definition f_id : ident := 111%positive. *)
(* Definition g_id : ident := 112%positive. *)
(* Definition h_id : ident := 113%positive. *)
(* Definition S2_id : ident := 110%positive. *)
(* Definition box_box_S1 : type := Tbox (Tbox S1_ty noattr) noattr. *)
(* Definition f_ty : type := box_box_S1. *)
(* Definition g_ty : type := box_int. *)
(* Definition h_ty : type := type_int32s. *)
(* Definition S2 : composite_definition := *)
(*   Composite S2_id Struct ([Member_plain f_id f_ty; Member_plain g_id g_ty; Member_plain h_id h_ty]) noattr nil nil. *)
(* Definition S2_ty := Tstruct nil S2_id noattr. *)

(* Definition ex5_comp_defs := [S1; S2]. *)

(* Definition ex5_main_body := *)
(*   <{ let A : S2_ty := struct(S2_id, [f_id;g_id;h_id],                           *)
(*               { Box(Box(struct(S1_id, [l_id;m_id;n_id], {Box($1), Box($2), $3}, S1_ty))), *)
(*                 Box($4), *)
(*                 $5 }, S2_ty) in *)
(*      let B : box_int := field(! ! field(A#S2_ty, f_id, f_ty), l_id, l_ty) in *)
(*      return $0 *)
(*      endlet endlet }>. *)
                    
(* Definition ex5_main_func : function := *)
(*   {|fn_generic_origins := nil; *)
(*     fn_origins_relation := nil; *)
(*     fn_return := type_int32s; *)
(*     fn_callconv := cc_default; *)
(*     fn_params := nil; *)
(*     fn_body := ex5_main_body |}. *)

(* Definition ex5_main_fundef : globdef (Rusttypes.fundef function) type := Gfun (Internal ex5_main_func). *)

(* Definition wf_ex5_comp_types : wf_composites ex5_comp_defs. *)
(* Proof. *)
(*   unfold wf_composites. simpl. auto. *)
(* Defined. *)

(* Definition ex5_prog : program := *)
(*   let (ce, EQ) := build_composite_env' ex5_comp_defs wf_ex5_comp_types in *)
(*   {| prog_defs := (main_ident, ex5_main_fundef) :: nil; *)
(*     prog_public := main_ident :: nil; *)
(*     prog_main := main_ident; *)
(*     prog_types := ex5_comp_defs; *)
(*     prog_comp_env := ce; *)
(*     prog_comp_env_eq := EQ |}. *)
                   
