Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Rusttypes.
Require Import Cop.
Require Import Rustsyntax RustlightBase.
Require Import Errors.


(** * Rustsyntax to Rustlight *)


(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.


Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.

Section SIMPL_EXPR.

Variable ce: composite_env.
  
Local Open Scope gensym_monad_scope.

Definition initial_generator (x: ident) : generator :=
  mkgenerator x nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

(** Use mode of an l-value  *)

Inductive use_mode : Type :=
| Use_copy: use_mode         (**r copy the l-value to other place *)
| Use_deref: use_mode          (**r use the l-value to perform dereference *)
| Use_reference: use_mode.     (**r just use the address of this l-value *)


(** TODO: for_set is useful in reducing the number of temporary
variables, because in most of the time we create a temp var to store
the result of the value expression and return Eplace/Emoveplace. But
with for_set, we can just use the set destination to store the result
of the value expression *)
Inductive destination : Type :=
| For_val
| For_effects
| For_set (p: place).

Definition finish (dst: destination) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_set sd => (sl ++ (Sassign sd a :: nil), a)
  end.


Definition dummy_expr := Econst_int Int.zero type_int32s.

(** ** Translate expression  *)


Section NOTATION.
(* Some ad-hoc solution to utilize the coercion from pexpr(place) to expr *)
Local Notation "( x , y )" := (@pair (list statement) expr x y).
Local Notation "( x ,, y )" := (@pair (list statement) place x y).

Fixpoint transl_value_expr (e: Rustsyntax.expr) : mon (list statement * expr) :=
  match e with
  | Rustsyntax.Eval (Vint n) ty =>
      ret (nil, Econst_int n ty)
  | Rustsyntax.Eval (Vfloat n) ty =>
      ret (nil, Econst_float n ty)
  | Rustsyntax.Eval (Vsingle n) ty =>
      ret (nil, Econst_single n ty)
  | Rustsyntax.Eval (Vlong n) ty =>
      ret (nil, Econst_long n ty)
  | Rustsyntax.Eval _ ty =>
      error (msg "Rustlightgen.transl_expr: Eval")
  | Rustsyntax.Evar id ty =>
      (* use id as value *)
      let p := Plocal id ty in
      (* check if ty is a copy type *)
      if own_type ce ty then
        ret (nil, Emoveplace p ty)
      else
        ret (nil, Eplace p ty)
  | Ederef e ty =>
      (* consider *call_allocate_box() *)
      do (sl, p) <- transl_place_expr e;
      let p' := Pderef p ty in
      if own_type ce ty then
        ret (sl, Emoveplace p' ty)
      else
        ret (sl, Eplace p' ty)
  | Ebox e ty =>
      do (sl, e') <- transl_value_expr e;
      (* Introduce a new variable. The scope of this new variable is
      the statement. *)
      do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let box_stmt := Sbox temp e' in
      ret (sl ++ (box_stmt :: nil), Emoveplace temp ty)
  | Efield e fid ty =>
      do (sl, p) <- transl_place_expr e;
      let p' := Pfield p fid ty in
      if own_type ce ty then
        ret (sl, Emoveplace p' ty)
      else
        ret (sl, Eplace p' ty)
  | Eassign l r ty =>
      let ty1 := Rustsyntax.typeof l in
      let ty2 := Rustsyntax.typeof r in
      (* simple type checking *)
      if type_eq ty1 ty2 then        
        do (sl1, p) <- transl_place_expr l;
        do (sl2, e') <- transl_value_expr r;
        let s := Sassign p e' in
        ret (sl2 ++ sl1 ++ (s :: nil), dummy_expr)
      else
        error (msg "Type mismatch between LHS and RHS in assignment: transl_expr")
  | Ecall ef el ty =>
      do (sl1, ef') <- transl_value_expr ef;
      do (sl2, el') <- transl_exprlist el;
      (* use a temp to store the result of this call *)
      do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let call_stmt := Scall temp ef' el' in
      if own_type ce ty then
        (* if this call is used for effects, the returned expr is useless *)
        ret (sl1 ++ sl2 ++ (call_stmt :: nil), Emoveplace temp ty)
      else
        ret (sl1 ++ sl2 ++ (call_stmt :: nil), Eplace temp ty)      
  | Rustsyntax.Eunop uop e ty =>
      do (sl, e') <- transl_value_expr e;
      match e' with
      | Epure pe' =>
          ret (sl, Eunop uop pe' ty)
      | _ =>
          error (msg "Move in unop: Rustlightgen.transl_expr")
      end
  | Rustsyntax.Ebinop binop e1 e2 ty =>
      do (sl1, e1') <- transl_value_expr e1;
      do (sl2, e2') <- transl_value_expr e2;
      match e1', e2' with
      | Epure pe1', Epure pe2' =>          
          ret (sl1 ++ sl2, Ebinop binop pe1' pe2' ty)
      | _, _ =>
          error (msg "Move in binop: Rustlightgen.transl_expr")
      end      
  end
  
with transl_place_expr (e: Rustsyntax.expr) : mon (list statement * place) :=
  match e with
  | Rustsyntax.Evar id ty =>
      ret (nil,, Plocal id ty)
  | Rustsyntax.Ederef e ty =>
      do (sl, p) <- transl_place_expr e;
      ret (sl,, Pderef p ty)
  | Rustsyntax.Ebox e ty =>
      (* temp = Box(e);
         Plocal temp *)
      do (sl, e') <- transl_value_expr e;
      do temp_id <- gensym ty; (* what is the lifetime of temp? *)
      let temp := Plocal temp_id ty in
      let box_stmt := Sbox temp e' in
      ret (sl ++ (box_stmt :: nil),, temp)
  | Efield e fid ty =>
      do (sl, p) <- transl_place_expr e;
      ret (sl,, Pfield p fid ty)
  | Ecall ef el ty =>
      do (sl1, ef') <- transl_value_expr ef;
      do (sl2, el') <- transl_exprlist el;
      (* use a temp to store the result of this call *)
      do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let call_stmt := Scall temp ef' el' in
      ret (sl1 ++ sl2,, temp)
  | _ => error (msg "It is impossible that this expression is a place expression: Rustlightgen.transl_expr")
  end
    
      
with transl_exprlist (el: Rustsyntax.exprlist) : mon (list statement * list expr) :=
  match el with
  | Rustsyntax.Enil =>
      ret (pair nil nil)
  | Rustsyntax.Econs r1 rl2 =>
      do (sl1, a1) <- transl_value_expr r1;
      do (sl2, al2) <- transl_exprlist rl2;
      ret (pair (sl1 ++ sl2) (a1 :: al2))
  end.

End NOTATION.

Definition value_or_place (e: Rustsyntax.expr) : bool :=
  match e with
  | Rustsyntax.Eval _ _ => true
  | Rustsyntax.Evar _ _ => false
  | Rustsyntax.Ebox _ _ => true
  | Rustsyntax.Efield _ _ _ => false
  | Rustsyntax.Ederef _ _ => false
  | Rustsyntax.Eunop _ _ _ => true
  | Rustsyntax.Ebinop _ _ _ _ => true
  | Rustsyntax.Eassign _ _ _ => true
  | Rustsyntax.Ecall _ _ _ => true
  end.
           
Fixpoint generate_lets (l: list (ident * type)) (body: statement) : statement :=
  match l with
  | nil => body
  | (id, ty) :: l' =>
      Slet id ty (generate_lets l' body)
  end.

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement :=
  makeseq_rec Sskip l.

Definition finish_stmt (sl: list statement) : mon statement :=
  fun (g: generator) =>
    let s := makeseq sl in
    Res (generate_lets (gen_trail g) s)
      (mkgenerator (gen_next g) nil)
      (Ple_refl (gen_next g)).

Definition extract_temps : mon (list (ident * type)) :=
  fun (g: generator) =>
    Res (gen_trail g)
      (mkgenerator (gen_next g) nil)
      (Ple_refl (gen_next g)).


(** Smart constructor for [if ... then ... else]. (copy from SimplExpr.v) *)

Definition eval_simpl_expr (a: expr) : option val := 
  match a with
  | Epure pe =>
      match pe with
      | Econst_int n _ => Some(Vint n)
      | Econst_float n _ => Some(Vfloat n)
      | Econst_single n _ => Some(Vsingle n)
      | Econst_long n _ => Some(Vlong n)
      | _ => None
      end
  | _ => None
  end.

(** TODO: some optimizations  *)
Definition makeif (a: expr) (s1 s2: statement) : statement :=
  (* match eval_simpl_expr a with *)
  (* | Some v => *)
  (*     match bool_val v (typeof a) Mem.empty with *)
  (*     | Some b => if b then s1 else s2 *)
  (*     | None   => Sifthenelse a s1 s2 *)
  (*     end *)
  (* | None => *) Sifthenelse a s1 s2.


Definition transl_if (r: Rustsyntax.expr) (s1 s2: statement) : mon statement :=
  do (sl, a) <- transl_value_expr r;
  do s <- finish_stmt sl;
  ret (Ssequence s (makeif a s1 s2)).

(* the returned gen_trail must be empty to ensure that all the new
introduced variables are declared by let statements *)
Fixpoint transl_stmt (stmt: Rustsyntax.statement) : mon statement :=
  match stmt with
  | Rustsyntax.Sskip =>
      ret Sskip
  | Sdo e =>
      do (sl, _) <- transl_value_expr e;
      (* insert let statements *)
      finish_stmt sl
  | Rustsyntax.Slet id ty stmt' =>
      do s <- transl_stmt stmt';
      ret (Slet id ty s)
  | Rustsyntax.Ssequence s1 s2 =>
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Ssequence s1' s2')
  | Rustsyntax.Sifthenelse e s1 s2 =>
      do (sl, e') <- transl_value_expr e;
      do s' <- finish_stmt sl;
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Ssequence s' (Sifthenelse e' s1' s2'))
  | Swhile e body =>
      do cond <- transl_if e Sskip Sbreak;
      do body' <- transl_stmt body;
      ret (Sloop (Ssequence cond body'))
  | Rustsyntax.Sloop s =>
      do s' <- transl_stmt s;
      ret (Sloop s')
  | Rustsyntax.Sreturn e =>
      match e with
      | Some e =>
          do (sl, e') <- transl_value_expr e;
          do s' <- finish_stmt sl;
          ret (Ssequence s' (Sreturn (Some e')))
      | None =>
          ret (Sreturn None)
      end
  | Rustsyntax.Sbreak =>
      ret Sbreak
  | Rustsyntax.Scontinue =>
      ret Scontinue
  | Rustsyntax.Smatch e arm_body =>
      (** FIXME: too complicated  *)
      (* we want to store e into a place *)
      let ty := Rustsyntax.typeof e in
      match ty with
      | Tvariant id _ =>
          match ce!id with
          | Some co =>
              if value_or_place e then
                (* let .. (generate_lets)
                   cond_sl; (eval_cond)
                   let temp;                  -| 
                   temp = e'; (assign_temp)    |-> temp_decl_arm
                   if cktag(temp,fid1) ...    _|  *)
                do temp_id <- gensym ty;
                let temp := Plocal temp_id ty in
                do (cond_sl, e') <- transl_value_expr e;
                let eval_cond := makeseq cond_sl in
                let assign_temp := Sassign temp e' in
                (* clear the temps in state *)
                do temps <- extract_temps;
                do arm_stmt <- transl_arm_statements arm_body temp (own_type ce ty) co;
                (* concat the condition statements and generate let stmts *)
                let temp_decl_arm := Slet temp_id ty (Ssequence assign_temp arm_stmt) in
                ret (generate_lets temps temp_decl_arm)
              else
                do (cond_sl, p) <- transl_place_expr e;
                let eval_cond := makeseq cond_sl in
                do temps <- extract_temps;
                do arm_stmt <- transl_arm_statements arm_body p (own_type ce ty) co;
                ret (generate_lets temps (Ssequence eval_cond arm_stmt))                
          | None => error (msg "Variant type does not exist: Rustlightgen.simpl_stmt")
          end
      | _ => error (msg "Type error in match: Rustlightgen.simpl_stmt")
      end        
  end

with transl_arm_statements (sl: arm_statements) (p: place) (moved: bool) (co: composite) : mon statement :=
  match sl with
  | ASnil => ret Sskip
  | AScons ids arm sl' =>
      do arm' <- transl_stmt arm;
      match ids with
      | Some (fid, temp_id) =>
          match find (fun elt => ident_eq (name_member elt) fid) co.(co_members) with
          | Some m =>              
              (* if cond then
                   let temp: ty;
                   temp = Eget(p, fid, ty);
                   arm'
                else else_stmt *)
              do else_stmt <- transl_arm_statements sl' p moved co;
              let ty := type_member m in
              let cond := Ecktag p fid type_bool in                              
              let destruct_place := if moved then Emoveget p fid ty else (Epure (Eget p fid ty)) in
              let assign_temp := Sassign (Plocal temp_id ty) destruct_place in
              let then_stmt := Slet temp_id ty (Ssequence assign_temp arm') in              
              ret (Sifthenelse cond then_stmt else_stmt)
          | _ => error (msg "Cannot find the member: Rustlightgen.transl_arm_statements")
          end
      | None =>
          (* default arm: else_stmt is useless *)
          ret arm'
      end
  end.

(* Extract the let declared variables *)
Fixpoint extract_vars (stmt: Rustsyntax.statement) : list (ident * type) :=
  match stmt with
  | Rustsyntax.Slet id ty s =>
      (id,ty) :: extract_vars s
  | Rustsyntax.Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustsyntax.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustsyntax.Sloop s =>
      extract_vars s
  | _ => nil
  end.


Open Scope error_monad_scope.

Definition transl_function (f: Rustsyntax.function) : Errors.res function :=
  let vars := var_names (f.(Rustsyntax.fn_params) ++ (extract_vars f.(Rustsyntax.fn_body))) in
  let next_temp := Pos.succ (fold_left (fun acc elt => Pos.max acc elt) vars 1%positive) in
  let init_gen := initial_generator next_temp in
  match transl_stmt f.(Rustsyntax.fn_body) init_gen with
  | Res stmt _ _ =>
      Errors.OK (mkfunction f.(Rustsyntax.fn_return)
                            f.(Rustsyntax.fn_callconv)
                            f.(Rustsyntax.fn_params)
                            stmt)
  | Err msg => Errors.Error msg
  end.

Definition transl_fundef (fd: Rustsyntax.fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f;
      Errors.OK (Internal tf)
  | External _ ef targs tres cconv =>
      Errors.OK (External _ ef targs tres cconv)
  end.

End SIMPL_EXPR.

Open Scope error_monad_scope.

Definition transl_program (p: Rustsyntax.program) : Errors.res program :=
  do p1 <- transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  Errors.OK
    {| prog_defs := p1.(AST.prog_defs);
    prog_public := p1.(AST.prog_public);
    prog_main := p1.(AST.prog_main);
    prog_types := p.(prog_types);
    prog_comp_env := p.(prog_comp_env);
    prog_comp_env_eq := p.(prog_comp_env_eq) |}.


(** TO DELETE  *)

(* Definitions for compilation *)

Definition empty_ce := PTree.empty composite.

Definition init_gen := initial_generator 10%positive.
