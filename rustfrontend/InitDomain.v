Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import AST.
Require Import Errors.
Require Import FSetWeakList DecidableType.
(** TODO: Rustlightbase also depends on InitDomain *)
Require Import Rusttypes Rustlight.

Local Open Scope list_scope.
Local Open Scope error_monad_scope.
Import ListNotations.


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
            
Section COMP_ENV.

Variable ce : composite_env.

(* get { p.1, p.2 ...} which are own types *)
Definition places_of_members (p: place) (mems: members) :=
  fold_left (fun acc elt =>
               match elt with
               | Member_plain fid ty =>
                   if own_type ce ty then
                     Paths.add (Pfield p fid ty) acc
                   else acc
               end) mems Paths.empty.

(* siblings of p *)
Definition siblings (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' fid _ =>
      match typeof_place p' with
      | Tstruct _ id =>
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
  | Pdowncast _ _ _ => Paths.empty
  end.
                                                        

Fixpoint parents (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' _ _ => Paths.add p' (parents p')
  | Pderef p' _ => Paths.add p' (parents p')
  | Pdowncast p' _ _ => Paths.add p' (parents p')
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
  | Tbox ty' =>
      let p' := Pderef p ty' in
      Paths.add p (own_path_box p' ty')
  | _ => Paths.empty
  end.

(* place [p] owns a memory location and we need to check its value is
initialized *)
Fixpoint place_owns_loc (p: place) : bool :=
  match p with
  | Plocal _ _ => true
  (* What about x: &mut Box<i32> ? We must check that p is an owned
  chain! *)
  | Pderef p' (Tbox _) => place_owns_loc p'
  | Pfield p' _ _ => place_owns_loc p'
  | Pdowncast p' _ _ => place_owns_loc p'
  | _ => false
  end.

(** The core function of adding a place [p] to the whole set [l] *)
(* add [p] to the paths [l]: If [p] is [Pderef p' ty], then
recursively add p' and its parents to paths [l]; If [p] is [Pfield p'
fid ty], then add [p']'s siblings and [p']'s parent to paths [l]*)
Fixpoint collect (p: place) (l: Paths.t) : Paths.t :=
  if place_owns_loc p then
    (** FIXME: WHY? If there are some children of [p] in [l], do
      nothing. Because [p] may have been split into sub-fields and we
      have collected p (see Pderef and Pfield cases). *)
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
      (** FIXME: we treat enum as a whole location  *)
      | Pdowncast p' _ _ => collect p' l
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

(* General collect functions *)

Fixpoint collect_pexpr (pe: pexpr) (m: PathsMap.t) : PathsMap.t :=
  match pe with
  | Eplace p _
  | Ecktag p _
  | Eref _ _ p _ =>
      (* we only check p which represents/owns a memory location *)
      if place_owns_loc p then
        collect_place p m
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
      collect_place p m
  | Epure pe =>
      collect_pexpr pe m
  end.

Fixpoint collect_exprlist (l: list expr) (m: PathsMap.t) : PathsMap.t :=
  match l with
  | nil => m
  | e :: l' =>
      collect_exprlist l' (collect_expr e m)
  end.


End COMP_ENV.

(* Kill function *)
Definition remove_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in  
  let rm := Paths.filter (fun elt => negb (is_prefix p elt)) l in
  PathsMap.set id rm m.


Definition remove_option (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with 
  | Some p => remove_place p m
  | None => m
  end.

(* Gen function: it add {p' | is_prefix p p' /\ p' ∈ S} to m[id]. Here
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


(* split places for drop statement based on the places appear in the
universe *)
Section SPLIT.
Variable universe: Paths.t.
  
Variable ce: composite_env.

Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> place -> type -> res (list (place * bool)).

(* Return the list of split places associated with a flag that
indicates whether this place is fully owned or not (if it is init) *)
(** Some property: the output places must be in universe so that we
can check whether this place is initialized or not. So the fully owned
flag is necessary *)
Fixpoint split_drop_place' (p: place) (ty: type) : res (list (place * bool)) :=
  match ty with
  | Tstruct _ id =>
      (* p in universe indicates that p is fully owned/moved (no p's
      children mentioned in this function) *)
      if Paths.mem p universe then
        OK [(p, true)]
      else
        match get_composite ce id with
        | co_some _ i co P =>
            let children := map (fun elt => match elt with
                                         | Member_plain fid fty =>
                                             (Pfield p fid fty, fty) end)
                              co.(co_members) in
            let foldf '(subfld, fty) acc :=
              do drops <- acc;
              do drops' <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) subfld fty;
              OK (drops' ++ drops) in
            fold_right foldf (OK nil) children
        | co_none _ => Error[CTX id; MSG ": Unfound struct id in composite_env or wrong recursive data: split_drop_place"]
        end
  | Tvariant _ id =>
       if Paths.mem p universe then
        OK [(p, true)]
      else
        (* we must ensure that no p's children in universe? *)
        Error ([MSG "place is "; CTX (local_of_place p); MSG ": enum does not exist in the universe set: split_drop_place"])
  | Tbox ty =>
      if Paths.mem p universe then
        (* p must be not fully owned *)
        if Paths.exists_ (fun p' => is_prefix_strict p p') universe then
          do drops <- split_drop_place' (Pderef p ty) ty;
          OK (drops ++ [(p, false)])
        else
          (* p is fully owned if it is initialized *)
          OK [(p, true)]
      else
        Error ([MSG "place is "; CTX (local_of_place p); MSG ": Box does not exist in the universe set: split_drop_place"])
  (* Is it correct? Error or Ignore? Consider that we always reach here *)
  | _ => OK []
   (* Error [MSG ": Normal types do not need drop: split_drop_place"] *)
  end.

End SPLIT.

Require Import Wfsimpl.

(* To ensure the soundness of init analysis which uses big step
analysis in Sdrop *)
Definition check_drops_complete (universe: Paths.t) (p: place) (drops: list place) : bool :=
  (* all places in the universe which are children of p must in drops *)
  Paths.for_all (fun p1 => in_dec place_eq p drops) (Paths.filter (fun p1 => is_prefix p p1) universe).

Definition split_drop_place (ce: composite_env) (universe: Paths.t) (p: place) (ty: type) : res (list (place * bool)) :=
  do drops <- Fixm (@PTree_Properties.cardinal composite) (split_drop_place' universe) ce p ty;
  if check_drops_complete universe p (fst (split drops)) then
    OK drops
  else Error (msg "there is some place in universe but not in the split places (split_drop_place) ").

(** Specification of split_drop_place  *)

(* similar to sound_split_drop_place in BorrowCheckSafe.v *)
Inductive split_places_ordered : list place -> Prop :=
| split_places_ordered_nil: split_places_ordered []
| split_places_ordered_cons: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun p1 => is_prefix p p1 = false) l ->
    split_places_ordered l ->
    split_places_ordered (p :: l)
.


Record split_drop_place_spec (universe: Paths.t) (r: place) (drops: list (place * bool)) : Prop :=
  { split_sound: forall p, In p (fst (split drops)) -> Paths.In p universe;
    split_complete: forall p, Paths.In p universe -> In p (fst (split drops));
    split_ordered: split_places_ordered (fst (split drops));
    (** TODO: current implementation does not guarantee this property.*)
    split_correct_full: forall p,
      In (p,true) drops ->
      (* no p's children in universe if p is full *)
      Paths.For_all (fun p1 => is_prefix_strict p p1 = false) universe;
  }.
            
Lemma split_drop_place_meet_spec: forall ce universe p drops,
    split_drop_place ce universe p (typeof_place p) = OK drops ->
    split_drop_place_spec universe p drops.
Admitted.

(** Properties of split_drop_place *)

Lemma split_drop_place_eq_universe: forall ce u1 u2 p ty,
    Paths.Equal u1 u2 ->
    split_drop_place ce u1 p ty = split_drop_place ce u2 p ty.
Admitted.

