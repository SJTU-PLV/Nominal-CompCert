Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice.
Require Import Rusttypes RustlightBase RustIR.
Require Import Errors.
Require Import StkborDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on abstract interpretation *)

(* Abstract symbol environment *)

Record aenv := build_aenv
{ aenv_symbtbl: PlaceMap.t (option ablock);
  aenv_nextblock: ablock; }.

Definition init_aenv := build_aenv (PlaceMap.init (@None ablock)) 1%positive.


Section COMPOSITE_ENV.

Variable ce: composite_env.

(* case1: [p] is an owner or a slice of an owner. If [p] stores a location to
another owner (memory block) then add [*p] to the result *)
(* case2: [p] is a parameter or a slice of a paramerer. If [p] stores a
location (box or reference) to another place (memory block) then add
[*p] to the result *)
Fixpoint owner_places' (fuel: nat) (var_or_param: bool) (p: place) : res (list place) :=
  match fuel with
  | O => Error [CTX (local_of_place p); MSG ": running out of fuel (owenr_places')"]
  | S fuel' =>
      let rec := owner_places' fuel' var_or_param in
      match typeof_place p with
      | Tbox ty' _ =>
          (* [*p] is also an owner *)
          let p' := Pderef p ty' in
          do l <- rec p';
          OK (p' :: l)
      | Tstruct id _ =>
          match ce!id with
          | Some co =>
              let fields := map (fun '(Member_plain fid ty') => Pfield p fid ty') co.(co_members) in
              do l <- fold_right_bind fields rec;
              OK (concat l)
          | None => Error [CTX id; MSG ": there is no struct with this ident (owner_place')"]
          end
      | Treference ty' _ _ =>
          if var_or_param then
            OK nil
          else
            (* this place is parameter, so we allocate ablock for it *)
            let p' := Pderef p ty' in
            do l <- rec p';
            OK (p' :: l)
      | _ => OK nil
      end
  end.

Definition owner_place (var_or_param: bool) (var: ident * type) :=
  let (id, ty) := var in
  let p := Plocal id ty in
  do l <- owner_places' (PTree_Properties.cardinal ce) var_or_param p;
  OK (p :: l).


(* add a place which occupies a memory block *)
Definition add_place (env: aenv) (p: place) : aenv :=
  build_aenv (PlaceMap.set p (Some env.(aenv_nextblock)) env.(aenv_symbtbl)) (Pos.succ env.(aenv_nextblock)).

Definition add_variable (var_or_param: bool) (env: aenv) (var : ident * type) :=
  do places <- owner_place var_or_param var;
  OK (fold_left add_place places env).

(* allocate ablocks for all variables *)
Definition add_variables (env: aenv) (vars : list (ident * type)) :=
  fold_left (fun acc elt => do acc' <- acc; add_variable true acc' elt) vars (OK env).

(* allocate ablocks for all parameters *)
Definition add_params (env: aenv) (params : list (ident * type)) :=
  fold_left (fun acc elt => do acc' <- acc; add_variable false acc' elt) params (OK env).


(** Initialize the abstract memory from parameters *)

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at "; CTX pc; MSG " : "].

Section AENV.

Variable e: aenv.

(* initialize an ablock: set the init aval and update the bor_tree the place points to *)
(* [p] is related to (b,ph) *)
Fixpoint init_place (fuel: nat) (p: place) (b: ablock) (ph: path) (m: amem) (next_tag: positive) : res (amem * positive) :=
  match fuel with
  | O => Error [CTX (local_of_place p); MSG ": running out of fuel (init_place)"]
  | S fuel' =>
      match typeof_place p with
      | Tstruct id _ =>
          match ce!id with
          | Some co =>
              (* accumulate the next tag *)              
              let f acc '(Member_plain fid ty') :=
                do (m, nt) <- acc;
                do (m', nt') <- init_place fuel' (Pfield p fid ty') b (ph ++ [Rfield fid]) m nt;
                OK (m', nt') in
              (* init all fields *)
              fold_left f co.(co_members) (OK (m, next_tag))
          | None => Error [CTX id; MSG ": no such composite (init_place) "]
          end
      | Tvariant id _ =>
          (* we do not know the discriminate of this variant *)
          let v := Venum LIdents.bot nil in
          do m' <- store m b ph v;
          OK (m', next_tag)
      | Tbox ty' _  | Treference ty' Mutable _ =>
          (* generate a abstract pointer with next_tag *)
          let p' := Pderef p ty' in
          (* find the ablock of p' *)
          match PlaceMap.get p' e.(aenv_symbtbl) with
          | Some b' =>
              (* update the borrow tree in b' (push next_tag) *)
              let t := Textern next_tag in
              do m' <- create_reference_from_owner Mutable b' nil t m;
              let v := Ptr (Aptrs.singleton (b', nil, t)) in
              (* store the abstract pointer to (b, ph) *)
              do m'' <- store m b ph v;
              OK (m'', Pos.succ next_tag)
          | None =>
              Error [CTX (local_of_place p); MSG ": there is no abstract block for this place (init_place)"]
          end
      | Treference ty' Immutable _ =>
          (* generate a abstract pointer with next_tag *)
          let p' := Pderef p ty' in
          (* find the ablock of p' *)
          match PlaceMap.get p' e.(aenv_symbtbl) with
          | Some b' =>
              (* update the borrow tree in b' (push next_tag) *)
              let t := Textern next_tag in
              do m' <- create_reference_from_owner Immutable b' nil t m;
              let v := Ptr (Aptrs.singleton (b', nil, t)) in
              (* store the abstract pointer to (b, ph) *)
              do m'' <- store m b ph v;
              OK (m'', Pos.succ next_tag)
          | None =>
              Error [CTX (local_of_place p); MSG ": there is no abstract block for this place (init_place)"]
          end
      | Tfunction _ _ _ => Error [CTX (local_of_place p); MSG ": unsupported function type (init_place)"]
      | _ =>
          (* store scalar to (b,ph) *)
          do m' <- store m b ph Scalar;
          OK (m', next_tag)
      end
  end.

Definition init_places_acc (acc: res (amem * positive)) (p: place) : res (amem * positive) :=
  do (m, nt) <- acc;
  match PlaceMap.get p e.(aenv_symbtbl) with
  | Some b =>
      init_place (PTree_Properties.cardinal ce) p b [] m nt
  | None =>
      Error [CTX (local_of_place p); MSG ": there is no abstract block for this place (init_place_acc)"]
  end.


(** The analysis ASSUME that the parameters are all initialized values (i.e., not Vbot) *)
Definition init_params (m: amem) (params : list (ident * type)) : res amem :=
  (* get all the places from parameters list *)
  do l <- fold_right_bind params (owner_place false);
  do (m, nt) <- fold_left init_places_acc (concat l) (OK (m, 1%positive));
  OK m.

Definition allocate_place_acc (acc: res amem) (p: place) : res amem :=
  do m <- acc;
  match PlaceMap.get p e.(aenv_symbtbl) with
  | Some b =>
      allocate_ablock ce m (typeof_place p) b
  | None =>
      Error [CTX (local_of_place p); MSG ": there is no abstract block for the place with this id (allocate_vars)"]
  end.

(* allocate blocks for variables *)
Definition allocate_vars (m: amem) (vars: list (ident * type)) :=
  do l <- fold_right_bind vars (owner_place true);
  fold_left allocate_place_acc (concat l) (OK m).

(* allocate blocks for parameters *)
Definition allocate_params (m: amem) (params: list (ident * type)) :=
  do l <- fold_right_bind params (owner_place false);
  fold_left allocate_place_acc (concat l) (OK m).

(** transfer function (place, pure expression, expression and statement *)

(* the returned place must own a whole memory block and the path is
the the location of p in p' *)
Fixpoint owner_path (p: place) : place * path :=
  match p with
  | Pfield p' fid _ =>
      let (p'', ph) := owner_path p' in
      (p'', ph ++ [Rfield fid])
  | _ => (p, [])
  end.

Definition aptr_of_aval (v: aval) : option LAptrs.t :=
  match v with
  | Ptr l => Some l
  | _ => None
  end.
  

(* There may be many possiblity for the memory location of a place.
[access] is the later action (e.g., the case that [p] in the RHS of a
assignment, [access] would be Awrite) for p *)
Fixpoint transfer_place (pc: node) (access: access_kind) (p: place) (m: amem) : res ((LAptrs.t + (ablock * path)) * amem) :=
  match p with
  | Plocal id ty =>
      (* p is an owner, we do not need to check its permission *)
      match PlaceMap.get p e.(aenv_symbtbl) with
      | Some b =>
          OK (inr (b,[]), m)
      | None =>
          Error (error_msg pc ++ [MSG "cannot get the memory block of place "; CTX id])
      end
  | Pderef p' ty =>
      (* get the (block,path) of p' *)
      do (l, m') <- transfer_place pc access p' m;
      match l with
      | inl ptrs =>
          (* It means that [p'] is accessed by these pointers, if we
          want to write [p], these pointers must have writable
          permission for [p']. So the we load values (by checking the
          permissin [access]) from all the abstract pointers. *)
          do (v, m'') <- load_aptrs m' ptrs access;
          match aptr_of_aval v with
          | Some ptrs' => OK (inl ptrs', m'')
          (* We can also ignore this error, but for now, we report it *)
          | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"])
          end            
      | inr (b, ph) =>
          (* It means that p' is an owner *)
          do (v, m'') <- load_owner m' b ph access;
          match aptr_of_aval v with
          | Some l => OK (inl l, m'')
          | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"])
          end
      end
  | Pfield p' fid ty =>
      (* we do not perform access when evaluating field *)
      do (l, m') <- transfer_place pc access p' m;
      match l with
      | inl ptrs =>
          (* we want to update the path in each pointer but we have no
          map function for Aptrs.t, so we use fold function *)
          let ptrs' := Aptrs.fold (fun '(b, ph, t) ptrs => Aptrs.add (b, ph ++ [Rfield fid], t) ptrs) ptrs Aptrs.empty in
          OK (inl ptrs', m')
      | inr (b, ph) =>
          OK (inr (b, ph ++ [Rfield fid]), m')
      end
  end.


(* return an abstract value and the updated abstract memory *)
Fixpoint transfer_pure_expr (pc: node) (pe: pexpr) (m: amem) : res (aval * amem) :=
  match pe with
  | Eunit
  | Econst_int _ _
  | Econst_float _ _
  | Econst_single _ _
  | Econst_long _ _ => OK (Scalar, m)
  | Eplace p ty =>
      (** Do we need to check that whether we should move this place
      instead of copy it, e.g., p is of box type *)
      (* evaluate this place *)
      do (r, m') <- transfer_place pc p m;
      match r with
      | inl ptrs =>
          (* the location of p is obtained from pointers *)
          match load_aptrs m' ptrs with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      | inr (b,ph) =>
          (* p is an owner *)
          match load_owner m' b ph with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      end
  | Eref p mut ty =>
      (* create a reference with tag [Tintern pc], so it means that
      there must be at most one reference be created in a pc *)
      (* evaluate place with access [mut] *)
      do (r, m') <- transfer_place pc (access_of_mutkind mut) p m;
      let new_tag := Tintern pc in
      match r with
      | inl ptrs =>
          (* for each (b,ph,t) ∈ ptrs, create a new ptr (b,ph,new_tag)
          from tag [t] *)
          do (ptrs', m'') <- create_reference_from_ptrs mut ptrs new_tag m';
          OK (Ptr ptrs', m'')
      | inr (b, ph) =>
          (* create a pointer (b,ph, new_tag) *)
          do (ptr, m'') <- create_reference_from_owner mut b ph new_tag m';
          OK (Ptr (Aptrs.singleton ptr), m'')
      end
  | Eget p fid ty =>
      

  end
Definition transfer (f: function) (cfg: rustcfg) (pc: node) (before: AM.t) : AM.t :=
  match before with
  (* If pred is unreacable, so this pc is unreacable, set to Bot *)
  | AM.Bot => AM.Bot
  | AM.Err msg => AM.Err msg     (* Error propagation *)
  | AM.State m =>                (* Update the abstract state *)
      match cfg ! pc with
      | None => AM.bot
      | Some (Inop _) => before
      | Some (Icond _ _ _) => before
      | Some Iend => before
      | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => AM.bot
          | Some s =>
              match s with
              | Sassign p e =>
                  
        end
    end.
            
End AENV.

Definition borrow_check (f: function) : res unit :=
  (* init abstract environment *)
  do env0 <- add_params init_aenv f.(fn_params);
  do env1 <- add_variables env0 f.(fn_vars);
  (* allocate ablocks *)
  do m0 <- allocate_params env1 init_amem f.(fn_params); 
  do m1 <- allocate_vars env1 m0 f.(fn_vars);
  (* initialize amem *)
  do m2 <- init_params env1 m1 f.(fn_params);
  (* forward dataflow *)
  OK tt.


End COMPOSITE_ENV.


