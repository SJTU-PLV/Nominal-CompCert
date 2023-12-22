Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import AST.
Require Import Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes RustlightBase RustIR.

Local Open Scope list_scope.

(* similart to is_prefix, but is_prefix p *p = true and contains p *p
= false. Because contains represents the memory inclusion between p1
and p2 *)
Fixpoint contains (p1 p2: place) : bool :=
  match p1, p2 with
  | Plocal id1 _, Plocal id2 _ => Pos.eqb id1 id2
  | Plocal id1 _, Pfield p2' _ _ => contains p1 p2'
  | Pfield p1' _ _, Pfield p2' _ _ => contains p1' p2'
  | _, _ => false
  end.

Lemma contains_refl: forall p, is_prefix p p = true.
Admitted.


Lemma contains_trans: forall p1 p2 p3, contains p1 p2 = true -> is_prefix p2 p3 = true -> contains p1 p3 = true.
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
  end.
                                                        

Fixpoint parents (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' _ _ => Paths.add p' (parents p')
  end.

Definition collect (p: place) (l: Paths.t) : Paths.t :=
  if own_type own_fuel ce (typeof_place p) then
    if Paths.mem p l then l
    else  
      let l' := Paths.filter (fun p' => contains p' p) l in    
      if Paths.is_empty l' then Paths.add p l
      else
        let parents := Paths.add p (parents p) in
        let siblings := Paths.fold (fun elt acc => Paths.union acc (siblings elt)) parents Paths.empty in
        Paths.union (Paths.diff l l') (Paths.add p siblings)
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

Fixpoint collect_expr (e: expr) : option place :=
  match e with
  | Eplace Move p _
  | Eget Move p _ _ =>
      Some p
  (* | Ecktag p _ _ => ?? *)
  | Eunop _ e _ => collect_expr e
  | Ebinop _ e1 e2 _ =>
      match collect_expr e1, collect_expr e2 with
      | Some p, None => Some p
      | None, Some p => Some p
      | _, _ => None
      end
  | _ => None          
  end.

Definition collect_exprlist (el: list expr) : list place :=
  fold_right
    (fun (elt : expr) (acc : list place) =>
       match collect_expr elt with
       | Some p => p :: acc
       | None => acc
       end) nil el.


Definition collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign p e _ =>
      collect_place p (collect_option_place (collect_expr e) m)
  | Scall op _ al _ =>
      let pl := collect_exprlist al in
      let m' := fold_right collect_place m pl in
      collect_option_place op m'
  | Sreturn (Some e) =>
      collect_option_place (collect_expr e) m
  | _ => m
  end.

Definition collect_func (f: function) : res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  if list_norepet_dec ident_eq (map fst vars) then
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    let init_map := fold_right collect_place (PTree.empty LPaths.t) l in
    let (_ ,stmts) := split (PTree.elements f.(fn_body)) in
    OK (fold_right collect_stmt init_map stmts)
  else
    Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil).
        
End COMP_ENV.

(* Kill function *)
Definition remove_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in  
  let rm := Paths.filter (fun elt => contains p elt) l in
  PathsMap.set id (Paths.diff l rm) m.

Definition remove_option (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with 
  | Some p => remove_place p m
  | None => m
  end.

(* Gen function: if add {p' | contains p p' /\ p' ∈ S} to m[id]. Here
[S] is the whole set *)
Definition add_place (S: PathsMap.t) (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in
  let whole := PathsMap.get id S in
  let add := Paths.filter (fun elt => contains p elt) whole in
  PathsMap.set id (Paths.union l add) m.

Definition add_option (S: PathsMap.t) (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with
  | Some p => add_place S p m
  | None => m
  end.

    
(* S is the whole set, flag = true indicates that it computes the MaybeInit set *)
Definition transfer (S: PathsMap.t) (flag: bool) (f: function) (pc: node) (before: PathsMap.t) : PathsMap.t :=
  if PathsMap.beq before PathsMap.bot then PathsMap.bot
  else
    match f.(fn_body)!pc with
    | None => PathsMap.bot
    | Some s =>
        match s with
        | Sassign p e _ =>
            let p' := collect_expr e in
            if flag then
              add_place S p (remove_option p' before)
            else
              remove_place p (add_option S p' before)
        | Scall op _ al _ =>
            let pl := collect_exprlist al in
            if flag then
              add_option S op (fold_right remove_place before pl)
            else
              remove_option op (fold_right (add_place S) before pl)
        | Sreturn (Some e) =>
            let p' := collect_expr e in
            if flag then
              remove_option p' before
            else
              add_option S p' before
        | _ => before
        end
    end.
                                      
Module DS := Dataflow_Solver(PathsMap)(NodeSetForward).


(* The analyze returns the MaybeInit and MaybeUninit sets *)
Definition analyze (ce: composite_env) (f: function) : option (PMap.t PathsMap.t * PMap.t PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  let (_, stmts) := split (PTree.elements f.(fn_body)) in (* there may be some unreachable nodes, does it matter? *)
  let whole := fold_right (collect_stmt ce) (PTree.empty LPaths.t) stmts in
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  let maybeInit := fold_right (add_place whole) (PTree.empty LPaths.t) pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := fold_right (add_place whole) (PTree.empty LPaths.t) vl in
  let initMap := DS.fixpoint f.(fn_body) successors (transfer whole true f) f.(fn_entryblock) maybeInit in
  let uninitMap := DS.fixpoint f.(fn_body) successors (transfer whole false f) f.(fn_entryblock) maybeUninit in
  match initMap, uninitMap with
  | Some initMap, Some uninitMap => Some (initMap, uninitMap)
  | _, _ => None
  end.
  
