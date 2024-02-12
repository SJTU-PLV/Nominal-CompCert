Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import AST.
Require Import Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes RustlightBase RustIR.

Local Open Scope list_scope.

Lemma is_prefix_refl: forall p, is_prefix p p = true.
Admitted.


Lemma is_prefix_trans: forall p1 p2 p3, is_prefix p1 p2 = true -> is_prefix p2 p3 = true -> is_prefix p1 p3 = true.
Admitted.


Module Place <: DecidableType.DecidableType.
  Definition t := place.
  Definition eq := @eq t.
  Definition eq_dec := place_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Place.

Module Paths := FSetWeakList.Make(Place).

Module LPaths := LFSet(Paths).

(* why we need this PathsMap, instead of just a set? *)
Module PathsMap := LPMap1(LPaths).

(** Collect places : if [p] is in the collection, do nothing; if [p]'s
ancestor is in the collection, add the siblings and the siblings of
[p]'s parents to the collection until this ancestor; if [p] and all
its parent are not in the collection, just add [p] to the
collection. *)

Definition places_of_members (p: place) (mems: members) :=
  fold_left (fun acc elt =>
               let elt' := match elt with
                           | Member_plain fid ty =>
                               Pfield p fid ty
                           end in
               Paths.add elt' acc) mems Paths.empty.
            
Section COMP_ENV.

Variable ce : composite_env.

(* siblings of p *)
Definition siblings (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' fid _ =>
      match typeof_place p' with
      | Tstruct id _ =>
          match ce!id with
          | Some co =>
              let siblings := places_of_members p' co.(co_members) in
              let siblings' := Paths.diff siblings (Paths.singleton p) in
              siblings'
          | _ => Paths.empty
          end
      | _ => Paths.empty
      end
  | Pderef p' _ => Paths.empty      
  end.
                                                        

Fixpoint parents (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' _ _ => Paths.add p' (parents p')
  | Pderef p' _ => Paths.add p' (parents p')
  end.


(* The whole set [S] and a place [p] s.t. [p] ∈ [S]:

1. If [p] is [Plocal id ty]: if [ty] = [Tstruct], it means that [p]'s
   children are not mentioned in this function and [p] is only moved
   or assigned entirely; if [ty] = [Tbox] and their are no [p]'s
   successors in [S], it means that [p] can be drop with its drop
   glue, otherwise, we should check [*p]'s initialized information to
   determine how to drop the subpath of [p].

 ___________                                                  
|_f_|_g_|_h_|
             
2. If [p] is [Pfield p' fid ty], it means that [p] and its disjoint
   siblings (e.g., [a] and [b]) which construct continious memory are
   in [S]. [p'] must be not in [S] to avoid ambiguity.

   The complicated case is that if [p] is [**a.f] which means that
   [**a.g] and [**a.h] are in [S], but what about [*a]?

3. If [p] is [Pderef p' ty], it means that [p'] is also in [S],
   because we have to consider how to drop [p']. If [p'] is not in
   [S], we don't how the initialized information about it.


Note: if [p] ∉ [S] then [p] must not be mentioned in the function. *)


Fixpoint own_path_box (p: place) (ty: type) :=
  match ty with
  | Tbox ty' _ =>
      let p' := Pderef p ty' in
      Paths.add p (own_path_box p' ty')
  | _ => Paths.empty
  end.

(** The core function of adding a place [p] to the whole set [l] *)
(* add [p] to the paths [l]: If [p] is [Pderef p' ty], then
recursively add p' and its parents to paths [l]; If [p] is [Pfield p'
fid ty], then add [p']'s siblings and [p']'s parent to paths [l]*)
Fixpoint collect (p: place) (l: Paths.t) : Paths.t :=
  if own_type ce (typeof_place p) then
    (** FIXME: WHY? If there are some children of [p] in [l], do
    nothing. *)
    if Paths.is_empty (Paths.filter (fun elt => is_prefix p elt) l) then
      match p with
      | Plocal _ _ =>
          Paths.add p l
      | Pfield p' _ _ =>
          (* difficult case: assume p = [**(a.f).g], p' = [**(a.f)], l = ∅ *)
          let l' := collect p' l in (* l' = {**(a.f), *(a.f), a.f, a.h} *)
          let siblings := siblings p in (* sib = {**(a.f).k, **(a.f).l} *)
          (* l'\{p'} ∪ siblings ∪ {p} *)
          (* ret = {*(a.f), a.f, a.h, **(a.f).k, **(a.f).l, **(a.f).f} *)
          (* we can see that each element occupies a memory location *)
          Paths.union (Paths.remove p' l') (Paths.add p siblings)
      | Pderef p' ty =>
          (* If type of [p] is [Tbox^n<T>] then add its n children to [l] *)
          (* let children := own_path_box p ty in *)
          (* let l' := Paths.union l children in *)
          Paths.add p (collect p' l)
      end
    else l
  else l.

    
Definition collect_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in
  PathsMap.set id (collect p l) m.

Definition collect_option_place (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with
  | Some p => collect_place p m
  | None => m
  end.


Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign p e  =>
      collect_place p (collect_option_place (moved_place e) m)
  | Sbox p e =>
      collect_place p (collect_option_place (moved_place e) m)
  | Scall p _ al =>
      let pl := moved_place_list al in
      let m' := fold_right collect_place m pl in
      collect_place p m'
  | Sreturn (Some e) =>
      collect_option_place (moved_place e) m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_option_place (moved_place e) (collect_stmt s1 (collect_stmt s2 m))
  | Sloop s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  if list_norepet_dec ident_eq (map fst vars) then
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    (** TODO: add all the parameters and variables to l (may be useless?) *)
    let init_map := fold_right collect_place (PTree.empty LPaths.t) l in
    Errors.OK (collect_stmt f.(fn_body) init_map)
  else
    Errors.Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil).
        
End COMP_ENV.

(* Kill function *)
Definition remove_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in  
  let rm := Paths.filter (fun elt => is_prefix p elt) l in
  PathsMap.set id (Paths.diff l rm) m.

Definition remove_option (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with 
  | Some p => remove_place p m
  | None => m
  end.

(* Gen function: if add {p' | is_prefix p p' /\ p' ∈ S} to m[id]. Here
[S] is the whole set *)
Definition add_place (S: PathsMap.t) (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in
  let whole := PathsMap.get id S in
  let add := Paths.filter (fun elt => is_prefix p elt) whole in
  PathsMap.set id (Paths.union l add) m.

Definition add_option (S: PathsMap.t) (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with
  | Some p => add_place S p m
  | None => m
  end.

    
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
Definition analyze (ce: composite_env) (f: function) : Errors.res (PMap.t PathsMap.t * PMap.t PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  let maybeInit := fold_right (add_place whole) (PTree.empty LPaths.t) pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := fold_right (add_place whole) (PTree.empty LPaths.t) vl in
  (* generate selector-based CFG for analysis *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry maybeInit in
  let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry maybeUninit in
  match initMap, uninitMap with
  | Some initMap, Some uninitMap => Errors.OK (initMap, uninitMap)
  | _, _ => Errors.Error (msg "Error in initialize analysis")
  end.
  
