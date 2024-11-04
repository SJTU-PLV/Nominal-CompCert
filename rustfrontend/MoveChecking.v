Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight Rustlightown RustIR.
Require Import Errors.
Require Import InitDomain InitAnalysis RustIRcfg.
Require Import Wfsimpl.

Import ListNotations.
Local Open Scope error_monad_scope.

(* A strong must_movable definition to simplify the proof *)

Definition removeR {V: Type} (m1 m2: PTree.t V) :=
  exists id v, m2 ! id = Some v
          /\ m1 = PTree.remove id m2.

Lemma well_founded_removeR {V: Type} : well_founded (@removeR V).
Proof.
  eapply well_founded_lt_compat with (f := fun m => PTree_Properties.cardinal m).
  unfold removeR. intros x y (id & v & GET & RM). subst.
  eapply PTree_Properties.cardinal_remove. eauto.
Qed.  

Lemma PTree_removeR {V: Type} : forall id v (m: PTree.t V),
    m ! id = Some v ->
    removeR (PTree.remove id m) m.
Proof.
  intros. red. exists id, v.
  auto.
Qed.

Section REC.

  Variable ce: composite_env.
  Variable rec: forall (ce': composite_env), (removeR ce' ce) -> PathsMap.t -> PathsMap.t -> PathsMap.t -> place -> type -> bool.

  Fixpoint must_movable' (init uninit universe: PathsMap.t) (p: place) (ty: type) : bool :=
    match ty with
    | Tbox ty1 =>
        if must_init init uninit universe p then
          must_movable' init uninit universe (Pderef p ty1) ty1
        else false
    | Tstruct _ id =>
        match get_composite ce id with
        | co_some i co P _ =>
            if must_init init uninit universe p then
              (* This place must be full so that it is sem_wt *)
              if is_full universe p then
                true
              else false
            else
              (* the whole struct is not in the universe, so we must
              check its sub-fields *)
              let fields_types := map (fun '(Member_plain fid fty) => (Pfield p fid fty, fty)) co.(co_members) in
              (** All sub-fields must be movable *)
              forallb (fun '(fp, ft) => rec (PTree.remove i ce) (PTree_removeR _ _ _ P) init uninit universe fp ft) fields_types                      
        | co_none =>
            (* type error *) false
        end
    | Tvariant _ id =>
        (* may be not required *)
        match ce ! id with
        | Some _ =>
            must_init init uninit universe p && is_full universe p
        | None => false
        end
    (* scalar type is movable if it is init *)
    | Tunit
    | Tint _ _
    | Tlong _
    | Tfloat _ => must_init init uninit universe p
    (* other types are unsupported to move *)
    | _ => false
    end.

End REC.
  
(* well_founded_lt_compat *)
(*   NoDup_incl_length *)
(*     get_composite *)
(*     list_norepet implies NoDup *)

(*     PTree.elements_remove *)

Definition must_movable_fix ce := Fix (@well_founded_removeR composite) must_movable' ce.

Definition must_movable ce init uninit universe p := must_movable_fix ce init uninit universe p (typeof_place p).


Definition scalar_type (ty: type) : bool :=
  match ty with
  | Tunit
  | Tint _ _
  | Tlong _
  | Tfloat _
  | Tfunction _ _ _ _ _
  | Tarray _ _
  | Treference _ _ _ => true
  | _ => false
  end.


Section INIT.

Variable ce: composite_env.
Variable init uninit universe: PathsMap.t.
  
Fixpoint move_check_pexpr (pe : pexpr) : bool :=
  match pe with
  | Eplace p ty =>
      if scalar_type ty then
        (* dominators are init means that the location if p is valid;
           the children of p is init means that the value of p is
           semantically wel-typed *)
        dominators_must_init init uninit universe p && must_init init uninit universe p
      else
        (* For now only support copy a scalar type value *)
        false
  | Ecktag p _ =>
      (* type of p must be enum *)
      match typeof_place p with
      | Tvariant _ _ =>
          dominators_must_init init uninit universe p && must_init init uninit universe p
      | _ => false
      end
  (** Eref is unsupported *)
  | Eref _ _ _ _ => false
  | Eunop _ pe0 _ => move_check_pexpr pe0
  | Ebinop _ pe1 pe2 _ => move_check_pexpr pe1 && move_check_pexpr pe2
  | _ => true
  end.

Definition move_check_expr (e : expr) :=
  match e with
  | Emoveplace p _ =>      
      if place_eq p (valid_owner p) then
        (* p is not downcast ... *)                
        dominators_must_init init uninit universe p && must_movable ce init uninit universe p
      else
        (* p is downcast, we just check its valid_owner is init *)
        dominators_must_init init uninit universe p &&
        must_init init uninit universe (valid_owner p) && is_full universe (valid_owner p)    
  | Epure pe => move_check_pexpr pe
  end.

Definition move_check_exprlist (l : list expr) :=
  forallb move_check_expr l.
          
Definition move_check_assign (p : place) :=
  dominators_must_init init uninit universe p.

End INIT.

Definition move_check_stmt ce (an : IM.t * IM.t * PathsMap.t) (stmt : statement) : Errors.res statement :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      match stmt with
      | Sassign p0 e
      | Sassign_variant p0 _ _ e
      | Sbox p0 e =>
          if move_check_expr ce mayinit mayuninit universe e
          then
            if move_check_assign mayinit mayuninit universe p0
            then OK stmt
            else Error (msg "move_check_assign error")
          else Error (msg "move_check_expr error")
      | Scall p0 _ el =>
          if move_check_exprlist ce mayinit mayuninit universe el
          then
            if move_check_assign mayinit mayuninit universe p0
            then OK stmt
            else Error (msg "move_check_assign error")
          else Error (msg "move_check_exprlist error")
      | _ => OK stmt
      end
  (* impossible *)
  | _, _ => OK stmt
  end.

Definition check_expr ce (an : IM.t * IM.t * PathsMap.t) (e: expr) : Errors.res unit :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      if move_check_expr ce mayinit mayuninit universe e then
        OK tt
      else
        Error (msg "move_check_expr error")
  | _, _ => OK tt
  end.

Definition move_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  do analysis_res <- analyze ce f cfg entry;
  do _ <- transl_on_cfg get_init_info analysis_res (move_check_stmt ce) (check_expr ce) f.(fn_body) cfg;
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
