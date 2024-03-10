Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Rusttypes RustlightBase.

Import ListNotations.
Scheme Equality for list.
Open Scope error_monad_scope.

(** The abstract domain for static analysis based on stacked borrow *)

(* map from a place (with primitive type) to element *)

(** TODO: implement this placemap  *)
Declare Module PlaceMap : TREE.

(* Module PlaceMap <: TREE. *)
(*   Definition elt := place. *)
(*   Definition elt_eq := place_eq. *)
 
(*   Definition t (A: Type) : Type := PTree.t (list (place * A)). *)

(*   Definition empty (A: Type) := PTree.empty (list (place * A)). *)

(*   Definition get {A} (p: place) (m: t A) : option A := *)
(*     match PTree.get (local_of_place p) m with *)
(*     | Some l => *)
(*         match find (fun elt => place_eq p (fst elt)) l with *)
(*         | Some (_, a) => Some a *)
(*         | None => None *)
(*         end *)
(*     | None => None *)
(*     end. *)

(*   Definition set {A} (p: place) (x: A) (m: t A) : t A := *)
(*     let id := (local_of_place p) in *)
(*     let l' := *)
(*       match PTree.get id m with *)
(*       | Some l => *)
(*           if in_dec place_eq p (fst (split l)) then *)
(*             map (fun '(p', a) => if place_eq p p' then (p, x) else (p, a)) l *)
(*           else *)
(*             (p, x) :: l *)
(*       | None => *)
(*           (p, x) :: nil *)
(*       end in *)
(*     PTree.set id l' m. *)
        
(*   Definition remove {A} (p: place) (m: t A) : t A := *)
(*     let id := (local_of_place p) in *)
(*     match PTree.get id m with *)
(*     | Some l => *)
(*         let l' := filter (fun '(p', a) => if place_eq p p' then false else true) l in *)
(*         PTree.set id l' m *)
(*     | None => *)
(*         m *)
(*     end. *)

(*   (** TODO  *) *)
(*   Axiom gempty: *)
(*     forall (A: Type) (i: elt), get i (empty A) = None. *)
(*   Axiom gss: *)
(*     forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x. *)
(*   Axiom gso: *)
(*     forall (A: Type) (i j: elt) (x: A) (m: t A), *)
(*     i <> j -> get i (set j x m) = get i m. *)
(*   Axiom gsspec: *)
(*     forall (A: Type) (i j: elt) (x: A) (m: t A), *)
(*     get i (set j x m) = if elt_eq i j then Some x else get i m. *)
(*   Axiom grs: *)
(*     forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None. *)
(*   Axiom gro: *)
(*     forall (A: Type) (i j: elt) (m: t A), *)
(*     i <> j -> get i (remove j m) = get i m. *)
(*   Axiom grspec: *)
(*     forall (A: Type) (i j: elt) (m: t A), *)
(*     get i (remove j m) = if elt_eq i j then None else get i m. *)


(*   Section BOOLEAN_EQUALITY. *)
    
(*     Variable A: Type. *)
(*     Variable beqA: A -> A -> bool. *)

(*     Definition beq_listA (l1 l2 : list (place * A)) : bool := *)
(*       list_beq (place * A) (fun '(p1, a1) '(p2, a2) => if place_eq p1 p2 then beqA a1 a2 else false) l1 l2. *)
    
(*     Definition beq (m1 m2: t A) : bool := *)
(*       PTree.beq beq_listA m1 m2. *)

(*     Axiom beq_correct: *)
(*       forall m1 m2, *)
(*       beq m1 m2 = true <-> *)
(*       (forall (x: elt), *)
(*        match get x m1, get x m2 with *)
(*        | None, None => True *)
(*        | Some y1, Some y2 => beqA y1 y2 = true *)
(*        | _, _ => False *)
(*        end). *)

(*   End BOOLEAN_EQUALITY. *)


  
(* End PlaceMap. *)

(* block id *)
Definition ablock : Type := positive.

Definition tag : Type := positive.

(* Definition of path *)
Inductive refseg : Type :=
| Rfield (fid: ident).

Definition path : Type := list refseg.

(* abstract pointer *)
Definition aptr : Type := ablock * path.

(* abstract value *)

Inductive aval : Type :=
| Vbot
| Scalar
| Ptr (l: list (aptr * tag))
| Vstruct (t: PTree.t aval)
| Venum (l: list ident) (t: PTree.t aval)
.

(* abstract block *)

(* Record ablock : Set := mkablock *)
(*   { ab_contents : ZTree.t aval; *)
(*     ab_borstk : ZTree borstk }. *)


(* borrow stack *)

Inductive access_kind : Type :=
| Aread
| Awrite.

Inductive bor_item : Type :=
| Share (t: tag)
| Unique (t: tag)
| Bopaque.

Definition borstk : Type := list bor_item.

(* The borrow stacks inside one abstract block *)
Inductive block_borstk : Type :=
| Batomic (stk: borstk)
| Bstruct (stkl: PTree.t block_borstk).


(* abstract memory *)

Record amem : Type := build_amem
  { am_contents : PTree.t aval;
    am_borstk : PTree.t block_borstk;
    am_nextblock : ablock;
    am_nexttag : tag }.


Section COMPOSITE_ENV.

Variable ce: composite_env.  

(* some general function for fold *)
Definition fold_right_bind {A B: Type} (l: list B) (f: B -> res A) : res (list A) :=
  fold_right (fun elt acc => do acc' <- acc; do r <- f elt; OK (r :: acc')) (OK nil) l.
  
(* Divide the place [p] into the smallest place which is primitive
type. The choose of fuel is the length of the composite environment *)
Fixpoint divide_places' (fuel: nat) (ty: type) (p: place) : res (list place) :=
  match fuel with
  | O => Error [CTX (local_of_place p);  MSG ": running out of fuel in children_places'"]
  | S fuel' =>
      let rec := divide_places' fuel' in
      match ty with
      | Tstruct id _ =>
          match ce ! id with
          | Some co =>
              let f memb := match memb with
                            | Member_plain fid ty' =>
                                rec ty' (Pfield p fid ty')    
                            end in
              do l' <- fold_right_bind co.(co_members) f;
              OK (concat l')
          | None =>
              Error [CTX id; MSG ": unknown struct identifier in children_places'"]
          end
      | _ => OK [p]
      end
  end.
          
            
Definition divide_places (p: place) :=
  divide_places' (PTree_Properties.cardinal ce) (typeof_place p) p.
  

Fixpoint load_path (p: path) (v: aval) : res aval :=
  match p, v with
  | [], _ => OK v
  | (Rfield fid) :: p', Vstruct t =>
      match PTree.get fid t with
      | Some v' => load_path p' v'
      | None => Error [CTX fid; MSG ": location in this field id has no valid value, load path"]
      end
  | _, _ =>  Error [MSG "Path and anstract value mismatches, load path"]
  end.
              
(* load the avals from a place *)
Definition load (m: amem) (p: aptr) : res aval :=
  let (b, ph) := p in
  match PTree.get b m.(am_contents) with
  | Some v =>
      load_path ph v
  | None =>
      Error [CTX b; MSG ": this block is unallocated, load"]
  end.


Fixpoint update_path (p: path) (m: aval) (v: aval): res aval :=
  match p, m with
  | [], _ => OK v
  | (Rfield fid) :: p', Vstruct t =>
      match PTree.get fid t with
      | Some t' =>
          (* replace p' in t' with v *)
          do m' <- update_path p' t' v;
          OK (Vstruct (PTree.set fid m' t))
      | None =>
          match p' with
          | [] => OK (Vstruct (PTree.set fid v t))
          (* access undefined value *)
          | _ => Error [CTX fid; MSG ": this field has no valid abstract value, update_path"]
          end
      end
  | _, _ => Error [MSG "Path and anstract value mismatches, load path"]
  end.

Definition store (m: amem) (p: aptr) (v: aval) : res amem :=
  let (b, ph) := p in
  match PTree.get b m.(am_contents) with
  | Some bv =>
      do bv' <- update_path ph bv v;
      OK (build_amem (PTree.set b bv' m.(am_contents))
              m.(am_borstk)
                  m.(am_nextblock)
                      m.(am_nexttag))
  | None => Error [CTX b; MSG ": this block is unallocated, store"]
  end.

Fixpoint init_aval_and_borstk' (fuel: nat) (ty: type) : res (aval * block_borstk) :=
  match fuel with
  | O => Error [MSG "Running out of fuel in aval_of_type'"]
  | S fuel' =>
      let rec := init_aval_and_borstk' fuel' in
      match ty with
      | Tstruct id _ =>
          match ce!id with
          | Some co =>              
              let f memb acc :=
                match memb with
                | Member_plain fid ty' =>
                    do (val_tree, bor_tree) <- acc;
                    do (v', stk') <- rec ty';
                    OK (PTree.set fid v' val_tree, PTree.set fid stk' bor_tree)
                end in
              do (v, sb) <- fold_right f (OK (PTree.empty aval, PTree.empty block_borstk)) co.(co_members);
              OK (Vstruct v, Bstruct sb)
          | None => Error [CTX id; MSG ": no such composite, init_avl_of_type'"]
          end
      | _ =>
          OK (Vbot, Batomic [])
      end
  end.
                
Definition init_aval_and_borstk (ty: type) : res (aval * block_borstk) :=
  init_aval_and_borstk' (PTree_Properties.cardinal ce) ty.

(* alloc a new block with type [ty] *)
Definition alloc (m: amem) (ty: type) : res (ablock * amem) :=
  do (v, stk) <- init_aval_and_borstk ty;
  let b := m.(am_nextblock) in
  OK (b, build_amem (PTree.set b v m.(am_contents)) (PTree.set b stk m.(am_borstk)) (Pos.succ b) m.(am_nexttag)).

                             
(* free an abstract block *)
Definition free (m: amem) (b: ablock) : amem :=
  build_amem (PTree.remove b m.(am_contents)) (PTree.remove b m.(am_borstk)) m.(am_nextblock) m.(am_nexttag).


(** Some definitions for stacked borrow rules *)

Fixpoint find_granting_aux (stk: list bor_item) (access: access_kind) (t: tag) (idx: nat) : res nat :=
  match stk with
  | [] => Error [MSG "There is no such tag in this borrow stack (find_granting_aux): "; CTX t]
  | i :: stk' =>
      match i, access with
      | Share t', Aread
      | Unique t', _ =>
          if Pos.eqb t t' then OK idx
          else find_granting_aux stk' access t (S idx)
      (** TODO: how to handle when encounting barrier in the borrow
      stack. *)
      | _ , _ => find_granting_aux stk' access t (S idx)
      end
  end.

Definition find_granting (stk: list bor_item) (access: access_kind) (t: tag) : res nat :=
  find_granting_aux stk access t O.

Fixpoint pop_until (stk: list bor_item) (idx: nat) (access: access_kind) : res (list bor_item) :=
  match stk, idx with
  | _, O => OK stk
  | i :: stk', S idx' =>
      match i, access with
      | Share _, Aread => OK stk
      | _, _ => pop_until stk' idx' access
      end
  | _, _ => Error [MSG "Pop an empty stack in pop_until"]
  end.
      
(* access the memory location and update the borrow stack *)
(** TODO: consider ownership access  *)
Definition access (stk: list bor_item) (access: access_kind) (t: tag) : res (list bor_item) :=
  do idx <- find_granting stk access t;
  pop_until stk idx access.

(* push item *)
Definition push_item (stk: list bor_item) (t: tag) (access: access_kind) : list bor_item :=
  match access with
  | Aread =>
      Share t :: stk
  | Awrite =>
      Unique t :: stk
  end.

(** Update borrow stacks while creating new reference *)

(* How to handle the merge of abstract memory? *)
