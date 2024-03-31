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

Module RUST_TYPE <: EQUALITY_TYPE.
  Definition t := type.
  Definition eq := type_eq.
End RUST_TYPE.
  
Module TyMap := EMap(RUST_TYPE).

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at "; CTX pc; MSG " : "].


Section SHALLOW_INIT.

Let t := TyMap.t (option ablock) ->
         type ->
         ablock ->
         path ->
         amem ->
         positive ->
         positive ->
         res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)).
  
Variable ce: composite_env.
  
Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> t.

Definition shallow_initialize' (shr_map: TyMap.t (option ablock)) (ty: type) (b: ablock) (ph: path) (m: amem) (next_extern: positive) (next_tag: positive) :  res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)) :=
  match ty with
  | Tunit
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tfunction _ _ _ =>
      do m' <- store m b ph Scalar;
      OK (m', next_extern, next_tag, shr_map, [])
  | Tbox ty' _
  | Treference ty' Mutable _ =>
      (* allocate an external block for ty' *)
      do (b', m1) <- alloc_external_block ce m ty' next_extern;
      (* update the borrow tree in b' *)
      do (ap, m2) <- create_reference_from_owner Mutable b' [] (Textern next_tag) m1;
      (* the abstract pointer is (b', [], Textern next_tag) *)
      let av := Ptr (Aptrs.singleton ap) in
      do m3 <- store m2 b ph av;
      (* initialize b' *)
      OK (m3, Pos.succ next_extern, Pos.succ next_tag, shr_map, [(b', ty')])
  | Treference ty' Immutable _ =>
      (* if [&ty'] has appeared and has been allocated *)
      match TyMap.get ty' shr_map with
      | Some b' =>
          (* update the borrow tree in b' *)
          (** TODO: here we do not consider annoated origins and
              there subset relation, so we just push tag on top of the
              onwer. If we have t1 ⊆ t2 then we can push t2 on top of
              t1 *)
          do (ap, m') <- create_reference_from_owner Immutable b' [] (Textern next_tag) m;
          let av := Ptr (Aptrs.singleton ap) in
          do m'' <- store m' b ph av;
          (** FIXME: do we need to update the contents in b'? I
              think we do not need to do that because b' must be
              already initialized *)
          OK (m'', next_extern, Pos.succ next_tag, shr_map, [])
      | None =>
          (* allocate an external block for ty' *)
          do (b', m1) <- alloc_external_block ce m ty' next_extern;
          (* update the borrow tree in b' *)
          do (ap, m2) <- create_reference_from_owner Immutable b' ph (Textern next_tag) m1;
          (* the abstract pointer is (b', [], Textern next_tag) *)
          let av := Ptr (Aptrs.singleton ap) in
          do m3 <- store m2 b [] av;
          (* initialize b', remember to use a new shr_map *)              
          OK (m3, Pos.succ next_extern, Pos.succ next_tag, TyMap.set ty' (Some b') shr_map, [(b', ty')])
      end
  | Tstruct id _ =>
      match @get_composite ce id with
      | co_some _ i co P =>
          let f acc '(Member_plain fid ty') :=
            do r1 <- acc;              
            let '(m1, next_extern1, next_tag1, shr_map1, l1) := r1 in
            (* shallow initialize this field *)
            do r2 <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) shr_map ty' b (ph ++ [Rfield fid]) m1 next_extern1 next_tag1;
            let '(m2, next_extern2, next_tag2, shr_map2, l2) := r2 in
            OK (m2, next_extern2, next_tag2, shr_map2, l1 ++ l2) in
          fold_left f co.(co_members) (OK (m, next_extern, next_tag, shr_map, []))
      | co_none _ =>
          Error [CTX id; MSG ": cannot get this struct type, maybe it is used in a wrong recursive manner? (shallow initialize)"]
      end
  | Tvariant id _ =>
      match @get_composite ce id with
      | co_some _ i co P =>
          let f acc '(Member_plain fid ty') :=
            do r1 <- acc;              
            let '(m1, next_extern1, next_tag1, shr_map1, l1) := r1 in
            (* shallow initialize this field *)
            do r2 <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) shr_map ty' b (ph ++ [Renum fid]) m1 next_extern1 next_tag1;
            let '(m2, next_extern2, next_tag2, shr_map2, l2) := r2 in
            OK (m2, next_extern2, next_tag2, shr_map2, l1 ++ l2) in
          fold_left f co.(co_members) (OK (m, next_extern, next_tag, shr_map, []))
      | co_none _ =>
          Error [CTX id; MSG ": cannot get this enum type, maybe it is used in a wrong recursive manner? (shallow initialize)"]
      end
  end.          

End SHALLOW_INIT.

Import Wfsimpl.

Definition shallow_initialize ce : TyMap.t (option ablock) ->
                                   type ->
                                   ablock ->
                                   path ->
                                   amem ->
                                   positive ->
                                   positive ->
                                   res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)) :=
  Fixm (@PTree_Properties.cardinal composite) shallow_initialize' ce.

Section COMPOSITE_ENV.

Variable ce: composite_env.  

(** Deeply initialize an abstract block [b] for a function parameter
with type [ty]. Do not know how to specify the recursive parameters *)

Fixpoint deep_initialize (fuel: nat) (shr_map: TyMap.t (option ablock)) (rec_map: TyMap.t (option aval)) (ty: type) (b: ablock) (m: amem) (next_extern: positive) (next_tag: positive) : res (amem * positive * positive * TyMap.t (option ablock)) :=
  match fuel with
  | O => Error [MSG "Running out of fuel (deep_initialize)"]
  | S fuel' =>
      (* check whether ty is a recursive type and is associated with an
         initial abstract value *)
      match TyMap.get ty rec_map with
      | Some v =>
          (* use v to initialize b *)
          do m' <- store m b [] v;
          OK (m', next_extern, next_tag, shr_map)
      | None =>       
          (* invoke shallow initialize *)
          do r <- shallow_initialize ce shr_map ty b [] m next_extern next_tag;
          let '(m1, next_extern1, next_tag1, shr_map1, l) := r in
          (* update the recursive map if [ty] is a composite *)
          do recv <- load m1 b [];
          let rec_map1 := match ty with
                          | Tstruct _ _
                          | Tvariant _ _ => TyMap.set ty (Some recv) rec_map
                          | _ => rec_map
                          end in
          (* recursively deep initialize the (b, ty) in l *)
          let f acc '(b, ty) :=
            do r1 <- acc;
            let '(m1, next_extern1, next_tag1, shr_map1) := r1 in
            deep_initialize fuel' shr_map1 rec_map1 ty b m1 next_extern1 next_tag1 in
          fold_left f l (OK (m1, next_extern1, next_tag1, shr_map1))
      end
  end.
            
Definition deep_fuel := 100%nat.             


(* initialize the parameters *)

Definition init_param (m: amem) (param: ident * type) (shr_map: TyMap.t (option ablock)) (next_extern: positive) (next_tag: positive) : res (amem * positive * positive * TyMap.t (option ablock)) :=
  let (id, ty) := param in
  (* allocate a stack block for param so that we can use id to get the
  content of this parameter *)
  do (b, m') <- alloc_stack_block ce m ty id;
  (* deep initialize this parameter *)
  deep_initialize deep_fuel shr_map (TyMap.init None) ty b m' next_extern next_tag.

Definition init_params_acc acc (param: ident * type) :=
  do r1 <- acc;
  let '(m1, next_extern1, next_tag1, shr_map1) := r1 in
  init_param m1 param shr_map1 next_extern1 next_tag1.

Definition init_params (m: amem) (params: list (ident * type)) : res amem :=
  do r <- fold_left init_params_acc params (OK (m, 1%positive, 1%positive, TyMap.init None));
  let '(m', _, _, _) := r in
  OK m'.


(** transfer function (place, pure expression, expression and statement *)

Definition aptr_of_aval (v: aval) : option LAptrs.t :=
  match v with
  | Ptr l => Some l
  | _ => None
  end.
  

(* There may be many possiblity for the memory location of a place.
[access] is the later action (e.g., the case that [p] in the RHS of a
assignment, [access] would be Awrite) for Print -. *)
(* The return abstract value may be Vtop (an example is that a field
of a enum is not initialized but in fact it is impossible to evaluate
this branch) but we do not report use of undefined value in the
bastract interpretation, because it is irrelevant issue *)
(** After investigating Miri, I find that the evaluation of place is
considered a read access *)
Fixpoint transfer_place' (pc: node) (p: place') (m: amem) : res ((aval + (ablock * path)) * amem) :=
  match p with
  | Plocal id ty =>
      (* p is an owner, we do not need to check its permission *)
      (* The block local variable is always stack block *)
      OK (inr (Stack id,[]), m)
  | Pderef p' ty =>
      (* get the (block,path) of p' *)
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          (* It means that [p'] is accessed by these pointers (an
          example is [**a], here *a is an abstract pointer, its
          evaluation return ptrs). If we want to write [p], these
          pointers must have writable permission for [p']. So the we
          load values (by checking the permissin [access]) from all
          the abstract pointers. *)
          (** Follow Miri: read access  *)
          do (v', m'') <- load_aval m' v Aread;
          OK (inl v', m'')
          (* match aptr_of_aval v with *)
          (* | Some ptrs' => OK (inl ptrs', m'') *)
          (* (* We can also ignore this error, but for now, we report it *) *)
          (* | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"]) *)
          (* end *)
      | inr (b, ph) =>
          (* It means that p' is an owner *)
          do (v, m'') <- load_owner m' b ph Aread;
          OK (inl v, m'')
          (* match aptr_of_aval v with *)
          (* | Some l => OK (inl l, m'') *)
          (* | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"]) *)
          (* end *)
      end
  | Pfield p' fid ty =>
      (* we do not perform access when evaluating field *)
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          match v with
          | Ptr ptrs =>
              (* we want to update the path in each pointer but we have no *)
              (* map function for Aptrs.t, so we use fold function *)
              let ptrs' := Aptrs.fold (fun '(b, ph, t) ptrs => Aptrs.add (b, ph ++ [Rfield fid], t) ptrs) ptrs Aptrs.empty in
              OK (inl (Ptr ptrs'), m')
          | _ =>
              OK (inl Vtop, m')
          end
      | inr (b, ph) =>
          OK (inr (b, ph ++ [Rfield fid]), m')
      end
  end.

Definition transfer_place (pc: node) (p: place) (m: amem) : res ((aval + (ablock * path)) * amem) :=
  match p with
  | Place p' =>
      transfer_place' pc p' m
  | Pdowncast p' fid ty =>
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          match v with
          | Ptr ptrs =>
              (* we want to update the path in each pointer but we have no *)
              (* map function for Aptrs.t, so we use fold function *)
              let ptrs' := Aptrs.fold (fun '(b, ph, t) ptrs => Aptrs.add (b, ph ++ [Renum fid], t) ptrs) ptrs Aptrs.empty in
              OK (inl (Ptr ptrs'), m')
          | _ =>
              OK (inl Vtop, m')
          end
      | inr (b, ph) =>
          OK (inr (b, ph ++ [Renum fid]), m')
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
      instead of copy it, e.g., p is of box type. Or it requires a
      separate checking? *)
      (* evaluate this place. Why the access is read? *)
      do (r, m') <- transfer_place pc p m;
      match r with
      | inl v =>
          (* the location of p is obtained from pointers *)
          load_aval m' v Aread
      | inr (b,ph) =>
          (* p is an owner *)
          match load_owner m' b ph Aread with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      end
  | Eref p mut ty =>
      (* create a reference with tag [Tintern pc], so it means that
      there must be at most one reference be created in a pc *)
      (* evaluate place with access [mut] *)
      do (r, m') <- transfer_place pc p m;
      let new_tag := Tintern pc in
      match r with
      | inl v =>
          (* if v is not pointer, the Eref is evaluated to Vtop *)
          match v with
          | Ptr ptrs =>
              (* for each (b,ph,t) ∈ ptrs, create a new ptr (b,ph,new_tag)
                 from tag [t] *)
              do (ptrs', m'') <- create_reference_from_ptrs mut ptrs new_tag m';
              OK (Ptr ptrs', m'')
          | _ =>
              OK (Vtop, m')
          end
      | inr (b, ph) =>
          (* create a pointer (b,ph, new_tag) *)
          do (ptr, m'') <- create_reference_from_owner mut b ph new_tag m';
          OK (Ptr (Aptrs.singleton ptr), m'')
      end
  | Ecktag p _ _ =>
      (** Is match statement is considered an access to the place? The
      answer is yes in Rust borrow checker (see borrowck_enum.rs). But
      here we do not consider it be a read access. *)
      OK (Scalar, m)
  | Eunop uop pe _ =>
      do (v, m') <- transfer_pure_expr pc pe m;
      (* uop can only be applied to scalar *)
      match v with
      | Scalar => OK (Scalar, m')
      | _ => OK (Vtop, m')
      end
  | Ebinop binop pe1 pe2 _ =>
      do (v1, m1) <- transfer_pure_expr pc pe1 m;
      do (v2, m2) <- transfer_pure_expr pc pe2 m1;
      match v1, v2 with
      | Scalar, Scalar => OK (Scalar, m2)
      | _, _ => OK (Vtop, m2)
      end          
  end.


Definition transfer_expr (pc: node) (e: expr) (m: amem) : res (aval * amem) :=
  match e with
  | Epure pe =>
      transfer_pure_expr pc pe m
  | Emoveplace p ty =>
      (* In the abstract interpretation, move is considered a normal
      copy operation and we do not perform any operation in its
      children. We do not have retag like stacked borrow, does it
      matter? *)
      do (r, m') <- transfer_place pc p m;
      match r with
      | inl v =>
          (* the location of p is obtained from pointers *)
          load_aval m' v Aread
      | inr (b,ph) =>
          (* p is an owner *)
          match load_owner m' b ph Aread with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      end
  end.


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


Definition borrow_check (f: function) : res unit :=
  (* allocate ablocks *)
  do m0 <- allocate_params env1 init_amem f.(fn_params); 
  do m1 <- allocate_vars env1 m0 f.(fn_vars);
  (* initialize amem *)
  do m2 <- init_params m1 f.(fn_params);
  (* forward dataflow *)
  OK tt.


End COMPOSITE_ENV.


