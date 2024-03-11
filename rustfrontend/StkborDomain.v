Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice.
Require Import Rusttypes RustlightBase.
Require Import RustIR.

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
Definition ablock : Type := PlaceMap.elt.

Inductive tag : Type :=
| Tintern (pc: node)       (**r internal tag created in location [pc] *)
| Textern (t: positive)         (**r external tag for function arguments *)
.

Lemma tag_eq : forall (t1 t2 : tag), {t1 = t2} + {t1 <> t2}.
Proof.
  generalize Pos.eq_dec. intros.
  decide equality.
Qed.

(* Definition of path *)
Inductive refseg : Type :=
| Rfield (fid: ident).

Lemma refseg_eq: forall (r1 r2: refseg), {r1 = r2} + {r1 <> r2}.
Proof.
  generalize ident_eq. intros.
  decide equality.
Qed.

Definition path : Type := list refseg.

Definition path_eq := List.list_eq_dec refseg_eq.

(* abstract pointer *)
Definition aptr : Type := (ablock * path) * tag.

Lemma aptr_eq : forall (p1 p2 : aptr), {p1 = p2} + {p1 <> p2}.
Proof.
  generalize PlaceMap.elt_eq path_eq tag_eq. intros.
  decide equality.
  decide equality.
Qed.

Module APTR <: DecidableType.DecidableType.
  Definition t := aptr.
  Definition eq := @eq t.
  Definition eq_dec := aptr_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End APTR.

Module Aptrs := FSetWeakList.Make(APTR).

(* It represent a set of abstract pointers, which is used to indicate
the possible values *)
Module LAptrs := LFSet(Aptrs).

Module IDENT <: DecidableType.DecidableType.
  Definition t := ident.
  Definition eq := @eq t.
  Definition eq_dec := ident_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End IDENT.

Module Idents := FSetWeakList.Make(APTR).

(* It represent a set of abstract pointers, which is used to indicate
the possible values *)
Module LIdents := LFSet(Aptrs).

(* abstract value *)

Inductive aval : Type :=
| Vbot
| Scalar
| Ptr (l: LAptrs.t)
| Vstruct (t: PTree.t aval)
| Venum (l: LIdents.t) (t: PTree.t aval)
.


Module LAval <: SEMILATTICE.
  
  Definition t := aval.
  
  Inductive eq' : aval -> aval -> Prop :=    
  | Ebot : eq' Vbot Vbot
  | Escalar : eq' Scalar Scalar
  | Eptr : forall l1 l2, LAptrs.eq l1 l2 -> eq' (Ptr l1) (Ptr l2)
  | Estruct : forall t1 t2 p v1 v2,
      t1 ! p = Some v1 ->
      t2 ! p = Some v2 ->
      eq' v1 v2 ->
      eq' (Vstruct t1) (Vstruct t2)
  | Eenum : forall t1 t2 p v1 v2 l1 l2,
      t1 ! p = Some v1 ->
      t2 ! p = Some v2 ->
      eq' v1 v2 ->
      LIdents.eq l1 l2 ->
      eq' (Venum l1 t1) (Venum l2 t2).

  Definition eq := eq'.
  
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Fixpoint beq (x y : aval) : bool :=
    match x,y with
    | Vbot, Vbot => true
    | Scalar, Scalar => true
    | Ptr l1, Ptr l2 => LAptrs.beq l1 l2
    | Vstruct t1, Vstruct t2 =>
        PTree.beq beq t1 t2
    | Venum l1 t1, Venum l2 t2 =>
        LIdents.beq l1 l2 && PTree.beq beq t1 t2
    | _, _ => false
    end.
  
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Inductive ge' : aval -> aval -> Prop :=
  | Gbot : forall v, ge' v Vbot
  | Gscalar: ge' Scalar Scalar
  | Gptr: forall l1 l2,
      LAptrs.ge l1 l2 ->
      ge' (Ptr l1) (Ptr l2)
  | Gstruct: forall t1 t2 p v1 v2,
      t1 ! p = Some v1 ->
      t2 ! p = Some v2 ->
      ge' v1 v2 ->
      ge' (Vstruct t1) (Vstruct t2)
  | Genum: forall t1 t2 l1 l2 v1 v2 p,
      t1 ! p = Some v1 ->
      t2 ! p = Some v2 ->
      ge' v1 v2 ->
      LIdents.ge l1 l2 ->
      ge' (Venum l1 t1) (Venum l2 t2).

  Definition ge := ge'.
  
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Definition bot := Vbot.

  Axiom ge_bot: forall x, ge x bot.
  
  Fixpoint lub (x y: aval) : aval :=
    let rec (x y : option aval) : option aval :=
      match x, y with
      | Some x, Some y => Some (lub x y)
      | _, _ => None
      end in
    match x,y with
    | Vbot, Vbot => Vbot
    | Scalar, Scalar => Scalar
    | Ptr l1, Ptr l2 => Ptr (LAptrs.lub l1 l2)
    | Vstruct t1, Vstruct t2 =>
        Vstruct (PTree.combine rec t1 t2)
    | Venum l1 t1, Venum l2 t2 =>
        Venum (LIdents.lub l1 l2) (PTree.combine rec t1 t2)
    | _, _ => Vbot
    end.
  
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.  

End LAval.


Module TAG <: DecidableType.DecidableType.
  Definition t := tag.
  Definition eq := @eq t.
  Definition eq_dec := tag_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End TAG.

Module Tags := FSetWeakList.Make(TAG).

(** Unused  *)
(* It represent a set of abstract pointers, which is used to indicate
the possible values *)
Module LTags := LFSet(Tags).

(* borrow stack *)

Inductive access_kind : Type :=
| Aread
| Awrite.

Inductive bor_item : Type :=
| Share (l: Tags.t)             (**r set of tags  *)
| Unique (t: tag)
.

Definition bor_item_eqb (i1 i2: bor_item) : bool :=
  match i1, i2 with
  | Share t1, Share t2 => Tags.equal t1 t2
  | Unique t1, Unique t2 => tag_eq t1 t2
  | _, _ => false
  end.


(* borrow tree which represents conditional branch *)
Inductive bor_tree : Type :=
| Bleaf
| Bnode (i: bor_item) (t: bor_tree)
| Bcond (t1 t2: bor_tree).

Fixpoint combine_bor_tree (t1 t2: bor_tree) :=
  match t1, t2 with
  | Bleaf, _ => Bleaf
  | _, Bleaf => Bleaf
  | Bnode i1 t1, Bnode i2 t2 =>
      if bor_item_eqb i1 i2 then
        Bnode i1 (combine_bor_tree t1 t2)
      else
        (* two items are not equal, so we create a condition node *)
        Bcond t1 t2
  | Bcond t11 t12, Bcond t21 t22 =>
      Bcond (combine_bor_tree t11 t21) (combine_bor_tree t12 t22)
  | _, _ => Bleaf                (** TODO  *)
  end.
        
Definition borstk : Type := list LBorItems.t.

Fixpoint combine_borstk' (s1 s2: borstk) : borstk :=
  match s1, s2 with
  | i1 :: s1', i2 :: s2' =>
      if BorItems.eq_dec i1 i2 then i1 :: combine_borstk' s1' s2'
      else BorItems.union i1 i2 :: combine_borstk' s1' s2'
  | [], _ => s2
  | _, [] => s1
  end.

Definition combine_borstk (s1 s2: borstk) : borstk :=
  rev (combine_borstk' (rev s1) (rev s2)).

(** TODO *)
Declare Module LBorstk : SEMILATTICE.


(* The borrow stacks inside one abstract block *)
Inductive block_borstk : Type :=
| Batomic (stk: borstk)
| Bstruct (stkl: PTree.t block_borstk).

(** TODO  *)
Declare Module LBlockStk : SEMILATTICE.

(* abstract memory *)

Record amem : Type := build_amem
  { am_contents : PTree.t aval;
    am_borstk : PTree.t block_borstk }.


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
