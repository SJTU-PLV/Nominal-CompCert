Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import AST.
Require Import Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes RustlightBase RustIR.
Require Import InitDomain.

Local Open Scope list_scope.
            
Section COMP_ENV.

Variable ce : composite_env.

Fixpoint collect_pexpr (pe: pexpr) (m: PathsMap.t) : PathsMap.t :=
  match pe with
  | Eplace p _
  | Ecktag p _
  | Eref _ _ p _ =>
      (* we only check p which represents/owns a memory location *)
      if place_owns_loc p then
        collect_place ce p m
      else m
  | Eunop _ pe _ =>
      collect_pexpr pe m
  | Ebinop _ pe1 pe2 _ =>
      collect_pexpr pe2 (collect_pexpr pe1 m)
  | _ => m
end.          


Definition collect_expr (e: expr) (m: PathsMap.t) : PathsMap.t :=
  match e with
  | Emoveplace p _ =>
      collect_place ce p m
  | Epure pe =>
      collect_pexpr pe m
  end.

Fixpoint collect_exprlist (l: list expr) (m: PathsMap.t) : PathsMap.t :=
  match l with
  | nil => m
  | e :: l' =>
      collect_exprlist l' (collect_expr e m)
  end.


Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign_variant p _ _ e
  | Sassign p e
  | Sbox p e =>
      collect_place ce p (collect_expr e m)
  | Scall p _ al =>
      collect_place ce p (collect_exprlist al m)
  | Sreturn (Some e) =>
      collect_expr e m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_stmt s1 (collect_stmt s2 (collect_expr e m))
  | Sloop s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  if list_norepet_dec ident_eq (map fst vars) then
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    (** TODO: add all the parameters and variables to l (may be useless?) *)
    let init_map := fold_right (collect_place ce) (PTree.empty LPaths.t) l in
    Errors.OK (collect_stmt f.(fn_body) init_map)
  else
    Errors.Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil).

End COMP_ENV.

(* S is the whole set, flag = true indicates that it computes the MaybeInit set *)
Definition transfer (S: PathsMap.t) (flag: bool) (f: function) (cfg: rustcfg) (pc: node) (before: PathsMap.t) : PathsMap.t :=
  if PathsMap.beq before PathsMap.bot then PathsMap.bot
  else
    match cfg ! pc with
    | None => PathsMap.bot
    | Some (Inop _) => before
    | Some (Icond _ _ _) => before
    | Some Iend => before
    | Some (Isel sel _) =>
        match select_stmt f.(fn_body) sel with
        | None => PathsMap.bot
        | Some s =>
        match s with
        | Sassign p e
        | Sassign_variant p _ _ e
        | Sbox p e =>
            let p' := moved_place e in
            if flag then
              add_place S p (remove_option p' before)
            else
              remove_place p (add_option S p' before)
        | Scall p _ al =>
            let pl := moved_place_list al in
            if flag then
              add_place S p (fold_right remove_place before pl)
            else
              remove_place p (fold_right (add_place S) before pl)
        | Sreturn (Some e) =>
            let p' := moved_place e in
            if flag then
              remove_option p' before
            else
              add_option S p' before
        | _ => before
        end
        end
    end.

Module DS := Dataflow_Solver(PathsMap)(NodeSetForward).

Local Open Scope error_monad_scope.

(* The analyze returns the MaybeInit and MaybeUninit sets *)
Definition analyze (ce: composite_env) (f: function) : Errors.res (PTree.t PathsMap.t * PTree.t PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let maybeInit := fold_right (add_place whole) empty_pathmap pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := fold_right (add_place whole) empty_pathmap vl in
  (* generate selector-based CFG for analysis *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry maybeInit in
let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry maybeUninit in
  match initMap, uninitMap with
  (* we only want the PTree because [None] represent the unreachable
  node *)
  | Some (_, initMap), Some (_, uninitMap) => Errors.OK (initMap, uninitMap)
  | _, _ => Errors.Error (msg "Error in initialize analysis")
  end.
  
