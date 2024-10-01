Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight Rustlightown RustIR.
Require Import Errors.
Require Import InitDomain InitAnalysis RustIRcfg.

Import ListNotations.
Local Open Scope error_monad_scope.

Section INIT.

Variable init uninit universe: PathsMap.t.
  
Fixpoint move_check_pexpr (pe : pexpr) : bool :=
  match pe with
  | Eplace p _ | Ecktag p _ => must_movable init uninit universe p
  | Eref _ _ _ _ => false
  | Eunop _ pe0 _ => move_check_pexpr pe0
  | Ebinop _ pe1 pe2 _ => move_check_pexpr pe1 && move_check_pexpr pe2
  | _ => true
  end.
  
Definition move_check_expr (e : expr) :=
  match e with
  | Emoveplace p _ => must_movable init uninit universe p
  | Epure pe => move_check_pexpr pe
  end.

Definition move_check_exprlist (l : list expr) :=
  forallb move_check_expr l.
          
Definition move_check_assign (p : place) :=
  match place_dominator p with
  | Some p' => must_init init uninit p'
  | None => true
  end.

End INIT.

Definition move_check_stmt (an : IM.t * IM.t * PathsMap.t) (stmt : statement) : Errors.res statement :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      match stmt with
      | Sassign p0 e
      | Sassign_variant p0 _ _ e
      | Sbox p0 e =>
          if move_check_expr mayinit mayuninit universe e
          then
            if move_check_assign mayinit mayuninit p0
            then OK stmt
            else Error (msg "move_check_assign error")
          else Error (msg "move_check_expr error")
      | Scall p0 _ el =>
          if move_check_exprlist mayinit mayuninit universe el
          then
            if move_check_assign mayinit mayuninit p0
            then OK stmt
            else Error (msg "move_check_assign error")
          else Error (msg "move_check_exprlist error")
      | _ => OK stmt
      end
  (* impossible *)
  | _, _ => OK stmt
  end.

Definition move_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  do analysis_res <- analyze ce f cfg entry;
  do _ <- transl_on_cfg get_init_info analysis_res move_check_stmt f.(fn_body) cfg;
  OK tt.
                                                                    
Definition transf_fundef (ce : composite_env) (id : ident) (fd : fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match move_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error ([MSG "In function "; CTX id; MSG " , in pc "] ++ msg)
      end
  | External orgs rels ef targs tres cconv => OK (External orgs rels ef targs tres cconv)
  end.

Definition transl_globvar := fun (_ : ident) (ty : type) => OK ty.

Definition move_check_program (p : program) :=
  do p1 <- (transform_partial_program2 (transf_fundef (prog_comp_env p)) transl_globvar p);
   OK
     {|
     prog_defs := AST.prog_defs p1;
     prog_public := AST.prog_public p1;
     prog_main := AST.prog_main p1;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
