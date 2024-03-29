Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice.
Require Import Rusttypes RustlightBase RustIR.
Require Import Errors.


Import ListNotations.
Scheme Equality for list.
Open Scope error_monad_scope.

(** The abstract domain for static analysis based on stacked borrow *)

(* map from a place (with primitive type) to element *)

(** TODO: implement this placemap  *)

Module PlaceMap <: MAP.
  Definition elt := place.
  Definition elt_eq := place_eq.
 
  Definition t (A: Type) : Type := (A * PTree.t (list (place * A))).

  Definition init {A: Type} (x: A) := (x, PTree.empty (list (place * A))).

  Definition find_elt {A} (p:place) (l: list (place * A)) :=
    find (fun elt => place_eq p (fst elt)) l.
  
  Definition get {A} (p: place) (m: t A) : A :=
    match PTree.get (local_of_place p) (snd m) with
    | Some l =>
        match find_elt p l with
        | Some (_, a) => a
        | None => fst m
        end
    | None => fst m
    end.

  Definition set {A} (p: place) (x: A) (m: t A) : t A :=
    let id := (local_of_place p) in
    let l' :=
      match PTree.get id (snd m) with
      | Some l =>
          if in_dec place_eq p (fst (split l)) then
            map (fun '(p', a) => if place_eq p p' then (p, x) else (p, a)) l
          else
            (p, x) :: l
      | None =>
          (p, x) :: nil
      end in
    (fst m, PTree.set id l' (snd m)).


  Axiom gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.

  (** The following code is required when we implement PlaceMap as a Tree *)
  (* Definition remove {A} (p: place) (m: t A) : t A := *)
  (*   let id := (local_of_place p) in *)
  (*   match PTree.get id m with *)
  (*   | Some l => *)
  (*       let l' := filter (fun '(p', a) => if place_eq p p' then false else true) l in *)
  (*       PTree.set id l' m *)
  (*   | None => *)
  (*       m *)
  (*   end. *)

  (* (** TODO  *) *)
  (* Axiom gempty: *)
  (*   forall (A: Type) (i: elt), get i (empty A) = None. *)
  (* Axiom gss: *)
  (*   forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x. *)
  (* Axiom gso: *)
  (*   forall (A: Type) (i j: elt) (x: A) (m: t A), *)
  (*   i <> j -> get i (set j x m) = get i m. *)
  (* Axiom gsspec: *)
  (*   forall (A: Type) (i j: elt) (x: A) (m: t A), *)
  (*   get i (set j x m) = if elt_eq i j then Some x else get i m. *)
  (* Axiom grs: *)
  (*   forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None. *)
  (* Axiom gro: *)
  (*   forall (A: Type) (i j: elt) (m: t A), *)
  (*   i <> j -> get i (remove j m) = get i m. *)
  (* Axiom grspec: *)
  (*   forall (A: Type) (i j: elt) (m: t A), *)
  (*   get i (remove j m) = if elt_eq i j then None else get i m. *)


  (* Section BOOLEAN_EQUALITY. *)
    
  (*   Variable A: Type. *)
  (*   Variable beqA: A -> A -> bool. *)

  (*   Definition beq_listA (l1 l2 : list (place * A)) : bool := *)
  (*     list_beq (place * A) (fun '(p1, a1) '(p2, a2) => if place_eq p1 p2 then beqA a1 a2 else false) l1 l2. *)
    
  (*   Definition beq (m1 m2: t A) : bool := *)
  (*     PTree.beq beq_listA m1 m2. *)

  (*   Axiom beq_correct: *)
  (*     forall m1 m2, *)
  (*     beq m1 m2 = true <-> *)
  (*     (forall (x: elt), *)
  (*      match get x m1, get x m2 with *)
  (*      | None, None => True *)
  (*      | Some y1, Some y2 => beqA y1 y2 = true *)
  (*      | _, _ => False *)
  (*      end). *)

  (* End BOOLEAN_EQUALITY. *)

  (* Definition map {A B} (f: place -> A -> B) (m: t A) := *)
  (*   PTree.map1 (fun l => List.map (fun '(p, elt) => (p, f p elt)) l) am. *)

  (* Axiom gmap: *)
  (*   forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A), *)
  (*     get i (map f m) = option_map (f i) (get i m). *)
  
  Definition map {A B} (f: A -> B) (m: t A) :=
    (f (fst m), PTree.map1 (fun (l : list (place * A)) => List.map (fun '(p, elt) => (p, f elt)) l) (snd m)).
  
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  
End PlaceMap.

(* block id: an abstract block may corresponds to multiple concrete
block *)
Inductive ablock : Type :=
| Stack (var : ident)
| Heap (loc: node)              (**r the heap block created in [loc] of the CFG  *)
| Extern (id: positive)         (**r external block which is passed from the environment  *)
.
  
Inductive tag : Type :=
| Tintern (pc: node)       (**r internal tag created in location [pc] *)
| Textern (t: positive)         (**r external tag for function arguments *)
.

Lemma tag_eq : forall (t1 t2 : tag), {t1 = t2} + {t1 <> t2}.
Proof.
  generalize Pos.eq_dec. intros.
  decide equality.
Qed.

Definition ident_of_tag (t: tag) :=
  match t with
  | Tintern pc => pc
  | Textern t => t
  end.

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
  generalize Pos.eq_dec path_eq tag_eq. intros.
  decide equality.
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
| Vbot                        (**r no defined value  *)
| Scalar
| Ptr (l: LAptrs.t)
(* we use list of ident and aval to represent the fields of struct and
enum instead of PTree because the it is hard to implement nested
recursion with PTree.fold *)
| Vstruct (t: list (ident * aval))
| Venum (t: list (ident * aval)) (**r if (id, Vtop), it means that id is undefined  *)
| Vtop                        (**r undefined value *)
.

Definition field_names {A: Type} (l: list (ident * A)) : list ident :=
  map fst l.

Definition field_vals {A: Type} (l: list (ident * A)) : list A :=
  map snd l.

Definition find_elt {A: Type} (id: ident) (l: list (ident * A)) : option A :=
  match find (fun '(id', v) => ident_eq id id') l with
  | Some (_, v) => Some v
  | None => None
  end.

Definition set_elt {A: Type} (id: ident) (v: A) (l: list (ident * A)) : list (ident * A) :=
  map (fun '(id', v') => if ident_eq id id' then (id, v) else (id', v')) l.
  
  
Module LAval <: SEMILATTICE_WITH_TOP.
  
  Definition t := aval.
  
  Inductive eq' : aval -> aval -> Prop :=    
  | Ebot : eq' Vbot Vbot
  | Escalar : eq' Scalar Scalar
  | Eptr : forall l1 l2, LAptrs.eq l1 l2 -> eq' (Ptr l1) (Ptr l2)
  | Estruct : forall t1 t2,
      field_names t1 = field_names t2 ->
      list_forall2 eq' (field_vals t1) (field_vals t2) ->
      eq' (Vstruct t1) (Vstruct t2)
  | Eenum : forall t1 t2,
      field_names t1 = field_names t2 ->
      list_forall2 eq' (field_vals t1) (field_vals t2) ->
      eq' (Venum t1) (Venum t2).

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
        let beq' '(id1, v1) '(id2, v2) :=
          ident_eq id1 id2 && beq v1 v2 in
        list_beq (ident * aval) beq' t1 t2
    | Venum t1, Venum t2 =>
        let beq' '(id1, v1) '(id2, v2) :=
          ident_eq id1 id2 && beq v1 v2 in
        list_beq (ident * aval) beq' t1 t2
    | _, _ => false
    end.
  
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Inductive ge' : aval -> aval -> Prop :=
  | Gbot : forall v, ge' v Vbot
  | Gtop : forall v, ge' Vtop v
  | Gscalar: ge' Scalar Scalar
  | Gptr: forall l1 l2,
      LAptrs.ge l1 l2 ->
      ge' (Ptr l1) (Ptr l2)
  | Gstruct: forall t1 t2,
      (* the list elements are equivalent *)
      field_names t1 = field_names t2 ->
      list_forall2 ge' (field_vals t1) (field_vals t2) ->
      ge' (Vstruct t1) (Vstruct t2)
  | Genum: forall t1 t2,
      field_names t1 = field_names t2 ->
      list_forall2 ge' (field_vals t1) (field_vals t2) ->
      ge' (Venum t1) (Venum t2).

  Definition ge := ge'.
  
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Definition bot := Vbot.
  
  Axiom ge_bot: forall x, ge x bot.

  Definition top := Vtop.
  Axiom ge_top: forall x, ge top x.

  Fixpoint lub (x y: aval) {struct x}: aval :=
    (* why we have to define this function inside lub. But it is ok to
    use map. *)
    let recf :=
      fix merge_field_aval (l1 l2: list (ident * aval)) : list (ident * aval) :=
        match l1, l2 with
        | (id1, v1) :: l1', (id2, v2) :: l2' => (id1, lub v1 v2) :: merge_field_aval l1' l2'
        | _, _ => []
        end in
    match x,y with
    | Vbot, _ => y
    | _, Vbot => x
    | _, Vtop => Vtop
    | Vtop, _ => Vtop
    | Scalar, Scalar => Scalar
    | Ptr l1, Ptr l2 => Ptr (LAptrs.lub l1 l2)
    | Vstruct t1, Vstruct t2 =>
        Vstruct (recf t1 t2)
    | Venum t1, Venum t2 =>
        Venum (recf t1 t2)
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
| Share (t: tag)
| Unique (t: tag)
| Disable (t: tag) 
.

Definition bor_item_tag (i: bor_item) : tag :=
  match i with
  | Share t
  | Unique t
  | Disable t => t
  end.

Definition combine_bor_item (i1 i2 : bor_item) : option bor_item :=
  if tag_eq (bor_item_tag i1) (bor_item_tag i2) then    
    match i1, i2 with
    | Disable t1, _ => Some (Disable t1)
    | _, Disable t2 => Some (Disable t2)
    | Share t1, _ => Some (Share t1)
    | _, Share t2 => Some (Share t2)
    | _, _ => Some i1
    end
  else None.

Definition bor_item_eqb (i1 i2: bor_item) : bool :=
  match i1, i2 with
  | Share t1, Share t2 => tag_eq t1 t2
  | Unique t1, Unique t2 => tag_eq t1 t2
  | Disable t1, Disable t2 => tag_eq t1 t2
  | _, _ => false
  end.

Inductive bor_item_ge : bor_item -> bor_item -> Prop :=
| BIdisable : forall i t, 
    bor_item_tag i = t ->
    bor_item_ge (Disable t) i
| BIshare : forall i t,
    (i = Share t \/ i = Unique t) ->
    bor_item_ge (Share t) i
| BIunique : forall t,
    bor_item_ge (Unique t) (Unique t).
    
    
(* borrow tree represents all the possiblity of the execution of
programs *)
Inductive bor_tree' : Type :=
| Bnode (i: bor_item) (children: list bor_tree').

Inductive bor_tree : Type :=
| Broot (t: list bor_tree').


Fixpoint combine_bor_tree' (t1 t2: bor_tree') : list bor_tree' := 
  match t1, t2 with
  | Bnode i1 l1, Bnode i2 l2 =>
      (* try to combine i1 and i2 *)
      match combine_bor_item i1 i2 with
      | Some i' =>
          let children :=
            (fix combine_bor_tree_list' (l1 l2: list bor_tree') : list bor_tree' :=
               match l1, l2 with
               | [], _ => l2
               | _, [] => l1
               | t1 :: l1', t2 :: l2' =>
                   combine_bor_tree' t1 t2 ++ combine_bor_tree_list' l1' l2'
               end) l1 l2 in                                
          [Bnode i' children]
      | None =>          
          [t1; t2]
      end
  end.

Fixpoint combine_bor_tree_list' (l1 l2: list bor_tree') : list bor_tree' :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | t1 :: l1', t2 :: l2' =>
      combine_bor_tree' t1 t2 ++ combine_bor_tree_list' l1' l2'
  end.

Definition combine_bor_tree (t1 t2: bor_tree) : bor_tree :=
  match t1, t2 with
  | Broot t1, Broot t2 =>
      Broot (combine_bor_tree_list' t1 t2)
  end.


(** TODO *)
Module LBorTree <: SEMILATTICE.

  Definition t := bor_tree.

  (** TODO: Is it correct?  *)
  Definition eq := @eq bor_tree.

  Fixpoint bor_tree_beq' (t1 t2: bor_tree') : bool :=
    match t1, t2 with
    | Bnode i1 l1, Bnode i2 l2 =>
        bor_item_eqb i1 i2 &&  list_beq bor_tree' bor_tree_beq' l1 l2
    end.
                                        
  Definition beq (t1 t2 : bor_tree) : bool :=
    match t1, t2 with
    | Broot l1, Broot l2 =>
        list_beq bor_tree' bor_tree_beq' l1 l2
    end.

  Inductive bor_tree_ge' : bor_tree' -> bor_tree' -> Prop :=
  | Bt_ge : forall i1 i2 l1 l2 n t1 t2,
      bor_item_ge i1 i2 ->
      (nth_error l2 n = Some t2 -> nth_error l1 n = Some t1 /\ bor_tree_ge' t1 t2) ->
      bor_tree_ge' (Bnode i1 l1) (Bnode i2 l2)
  .

  Definition bor_tree_ge_list' (l1 l2: list bor_tree') : Prop :=
    forall t1 t2 n,
      nth_error l2 n = Some t2 ->
      nth_error l1 n = Some t1 /\ bor_tree_ge' t1 t2.
  
  Definition ge (t1 t2: bor_tree) : Prop :=
    match t1, t2 with
    | Broot l1, Broot l2 =>
        bor_tree_ge_list' l1 l2
    end.

  (** Is it correct?  *)
  Definition bot := Broot nil.
  
  Definition lub := combine_bor_tree.

  (** TODO  *)
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End LBorTree.
  
(* The borrow stacks inside one abstract block *)
Inductive block_bortree : Type :=
| Bbot                          (* necessary for semi-lattice *)
| Batomic (t: bor_tree)
| Bstruct (tl: list (ident * block_bortree)).

(** TODO  *)
Module LBlkBorTree <: SEMILATTICE.
  
  Definition t := block_bortree.

  Inductive eq' : t -> t -> Prop :=
  | Eqbot : eq' Bbot Bbot
  | Eqatomic : forall t1 t2,
      LBorTree.eq t1 t2 ->
      eq' (Batomic t1) (Batomic t2)
  | Eqstruct : forall l1 l2,
      field_names l1 = field_names l2 ->
      list_forall2 eq' (field_vals l1) (field_vals l2) ->
      eq' (Bstruct l1) (Bstruct l2).

  Definition eq := eq'.
  
  Fixpoint beq (x y : t) : bool :=
    match x, y with
    | Bbot, Bbot => true
    | Batomic t1, Batomic t2 => LBorTree.beq t1 t2
    | Bstruct l1, Bstruct l2 =>
        let beq' '(id1, v1) '(id2, v2) :=
          ident_eq id1 id2 && beq v1 v2 in
        list_beq (ident * block_bortree) beq' l1 l2
    | _, _ => false
    end.

  Inductive ge' : t -> t -> Prop :=
  | Gbot : forall t, ge' t Bbot
  | Gatomic : forall t1 t2,
      LBorTree.ge t1 t2 ->
      ge' (Batomic t1) (Batomic t2)
  | Gstruct : forall l1 l2,
      field_names l1 = field_names l2 ->
      list_forall2 ge' (field_vals l1) (field_vals l2) ->
      ge' (Bstruct l1) (Bstruct l2).

  Definition ge := ge'.
  
  Definition bot := Bbot.
  
  Fixpoint lub (x y: block_bortree) : block_bortree :=
    let recf :=
      fix merge_field_blkbortree (l1 l2: list (ident * block_bortree)) : list (ident * block_bortree) :=
        match l1, l2 with
        | (id1, t1) :: l1', (id2, t2) :: l2' => (id1, lub t1 t2) :: merge_field_blkbortree l1' l2'
        | _, _ => []
        end in
    match x,y with
    | Bbot, _ => y
    | _, Bbot => x
    | Batomic t1, Batomic t2 => Batomic (LBorTree.lub t1 t2)
    | Bstruct l1, Bstruct l2 =>
        Bstruct (recf l1 l2)
    | _, _ => Bbot
    end.
       
  
  (** TODO  *)
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

  
End LBlkBorTree.  

Module LAvalMap := LPMap1(LAval).
Module LBorMap := LPMap1(LBlkBorTree).

(* abstract memory *)
(* There are three regions of memory: stack, heap and external blocks *)
Record amem : Type := build_amem
  { am_stack : LAvalMap.t;
    am_stack_bortree : LBorMap.t;
    am_heap : LAvalMap.t;
    am_heap_bortree : LBorMap.t;
    am_external : LAvalMap.t;
    am_external_bortree : LBorMap.t;
  }.

Definition init_amem := build_amem LAvalMap.bot LBorMap.bot LAvalMap.bot LBorMap.bot LAvalMap.bot LBorMap.bot.

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
      match find_elt fid t with
      | Some v' => load_path p' v'
      | None => Error [CTX fid; MSG ": location in this field id has no valid value, load path"]
      end
  | _, _ =>  Error [MSG "Path and anstract value mismatches, load path"]
  end.


Fixpoint load_path_bortree (p: path) (bb: block_bortree) : res block_bortree :=
  match p, bb with
  | [], _ => OK bb
  | (Rfield fid) :: p', Bstruct t =>
      match find_elt fid t with
      | Some bb' => load_path_bortree p' bb'
      | None => Error [CTX fid; MSG ": location in this field id has no valid block_bortree (load_path_bortree)"]
      end
  | _, _ =>  Error [MSG "Path and anstract value mismatches (load_path_bortree)"]
  end.


Local Open Scope string_scope.

(* load the avals from (b,ph) *)
Definition load (m: amem) (b: ablock) (ph: path) : res aval :=
  let load' m id msg :=
    match m!id with
    | Some v =>
        load_path ph v
    | None =>
        Error [CTX id; MSG msg; MSG ": this block is unallocated (load)"]
    end in
  match b with
  | Stack id => load' m.(am_stack) id "stack block"
  | Heap pc => load' m.(am_heap) pc "heap block"
  | Extern id => load' m.(am_external) id "external block"
  end.

(* load the block borrow tree from a place *)
Definition load_block_bortree (m: amem) (b: ablock) (ph: path) : res block_bortree :=
  let load_block_bortree' m id msg :=
    match m!id with
    | Some bb =>
        load_path_bortree ph bb
    | None =>
        Error [CTX id; MSG msg; MSG ": this block is unallocated (load_block_bortree)"]
    end in   
  match b with
  | Stack id => load_block_bortree' m.(am_stack_bortree) id "stack block"
  | Heap pc => load_block_bortree' m.(am_heap_bortree) pc "heap block"
  | Extern id => load_block_bortree' m.(am_external_bortree) id "external block"
  end.


Fixpoint update_path (p: path) (m: aval) (v: aval): res aval :=
  match p, m with
  | [], _ => OK v
  | (Rfield fid) :: p', Vstruct t =>
      match find_elt fid t with
      | Some t' =>
          (* replace p' in t' with v *)
          do m' <- update_path p' t' v;
          OK (Vstruct (set_elt fid m' t))
      | None =>
          match p' with
          | [] => OK (Vstruct (set_elt fid v t))
          (* access undefined value *)
          | _ => Error [CTX fid; MSG ": this field has no valid abstract value, update_path"]
          end
      end
  | _, _ => Error [MSG "Path and anstract value mismatches (update_path)"]
  end.


Fixpoint update_path_bortree (p: path) (m: block_bortree) (v: block_bortree): res block_bortree :=
  match p, m with
  | [], _ => OK v
  | (Rfield fid) :: p', Bstruct t =>
      match find_elt fid t with
      | Some t' =>
          (* replace p' in t' with v *)
          do m' <- update_path_bortree p' t' v;
          OK (Bstruct (set_elt fid m' t))
      | None =>
          match p' with
          | [] => OK (Bstruct (set_elt fid v t))
          (* access undefined value *)
          | _ => Error [CTX fid; MSG ": this field has no valid borrow tree (update_path_bortree)"]
          end
      end
  | _, _ => Error [MSG "Path and anstract value mismatches (update_path_bortree)"]
  end.


Definition store (m: amem) (b: ablock) (ph: path) (v: aval) : res amem :=
  let store' m id msg :=
    match m!id with
    | Some bv =>
        do bv' <- update_path ph bv v;
        OK (PTree.set id bv' m)
    | None => Error [CTX id; MSG msg; MSG ": this block is unallocated (store) "]
    end in
  match b with
  | Stack id =>
      do stack' <- store' m.(am_stack) id "stack block";
      OK (build_amem stack' m.(am_stack_bortree) m.(am_heap) m.(am_heap_bortree) m.(am_external) m.(am_external_bortree))      
  | Heap pc =>
      do heap' <- store' m.(am_heap) pc "heap block";
      OK (build_amem m.(am_stack) m.(am_stack_bortree) heap' m.(am_heap_bortree) m.(am_external) m.(am_external_bortree))
  | Extern id =>
      do extern' <- store' m.(am_external) id "heap block";
      OK (build_amem m.(am_stack) m.(am_stack_bortree) m.(am_heap) m.(am_heap_bortree) extern' m.(am_external_bortree))
  end.


Definition store_block_bortree (m: amem) (b: ablock) (ph: path) (v: block_bortree) : res amem :=
  let store_block_bortree' m id msg :=
    match m!id with
    | Some bb =>
        do bb' <- update_path_bortree ph bb v;
        OK (PTree.set id bb' m)
    | None => Error [CTX id; MSG msg; MSG ": this block is unallocated (store_block_bortree) "]
    end in
  match b with
  | Stack id =>
      do stack' <- store_block_bortree' m.(am_stack_bortree) id "stack block";
      OK (build_amem m.(am_stack) stack' m.(am_heap) m.(am_heap_bortree) m.(am_external) m.(am_external_bortree))      
  | Heap pc =>
      do heap' <- store_block_bortree' m.(am_heap_bortree) pc "heap block";
      OK (build_amem m.(am_stack) m.(am_stack_bortree) m.(am_heap) heap' m.(am_external) m.(am_external_bortree))
  | Extern id =>
      do extern' <- store_block_bortree' m.(am_external_bortree) id "heap block";
      OK (build_amem m.(am_stack) m.(am_stack_bortree) m.(am_heap) m.(am_heap_bortree) m.(am_external) extern')
  end.

Local Close Scope string_scope.

(* this initialization is for uninit variables such as local variables *)
Fixpoint alloc_aval_and_bortree' (fuel: nat) (ty: type) : res (aval * block_bortree) :=
  match fuel with
  | O => Error [MSG "Running out of fuel in alloc_aval_and_bortree'"]
  | S fuel' =>
      let rec := alloc_aval_and_bortree' fuel' in
      match ty with
      | Tstruct id _ | Tvariant id _  =>
          match ce!id with
          | Some co =>
              let f '(Member_plain fid ty') := rec ty' in
              (* compute the list of aval for each fields *)
              do l <- fold_right_bind co.(co_members) f;
              let (v, sb) := split l in
              (* get the idents of each field *)
              let ids := map (fun '(Member_plain fid ty') => fid) co.(co_members) in
              OK (Vstruct (combine ids v), Bstruct (combine ids sb))
          | None => Error [CTX id; MSG ": no such composite, init_avl_of_type'"]
          end
      | _ =>
          (* init an empty borrow tree *)
          OK (Vtop, Batomic (Broot nil))
      end
  end.
                
Definition alloc_aval_and_bortree (ty: type) : res (aval * block_bortree) :=
  alloc_aval_and_bortree' (PTree_Properties.cardinal ce) ty.

(* allocate a stack block [b] *)
Definition alloc_stack_block (m: amem) (ty: type) (id: ident) : res (ablock * amem) :=
  do (v, stk) <- alloc_aval_and_bortree ty;
  OK (Stack id, (build_amem (PTree.set id v m.(am_stack)) (PTree.set id stk m.(am_stack_bortree)) m.(am_heap) m.(am_heap_bortree) m.(am_external) m.(am_external_bortree))).

Definition alloc_heap_block (m: amem) (ty: type) (pc: node) : res (ablock * amem) :=
  do (v, stk) <- alloc_aval_and_bortree ty;
  OK (Heap pc, (build_amem m.(am_stack) m.(am_stack_bortree) (PTree.set pc v m.(am_heap)) (PTree.set pc stk m.(am_heap_bortree)) m.(am_external) m.(am_external_bortree))).

Definition alloc_external_block (m: amem) (ty: type) (id: positive) : res (ablock * amem) :=
  do (v, stk) <- alloc_aval_and_bortree ty;
  OK (Extern id, (build_amem m.(am_stack) m.(am_stack_bortree) m.(am_heap) m.(am_heap_bortree) (PTree.set id v m.(am_external)) (PTree.set id stk m.(am_external_bortree)))).


(** Some definitions for "stacked borrow" rules *)

Definition tree_path := list nat.

Definition granting_item (access: access_kind) (t: tag) (i: bor_item) : bool :=
  match access with
  | Aread =>
      match i with
      | Unique t' | Share t' => tag_eq t t'
      | _ => false
      end
  | Awrite =>
      match i with
      | Unique t' => tag_eq t t'
      | _ => false
      end
  end.

Fixpoint find_granting_aux (access: access_kind) (t: tag) (p: tree_path) (bt: bor_tree') : option tree_path :=
  match bt with
  | Bnode i l =>
      if granting_item access t i then Some p
      else
        let f (acc: option tree_path * nat) elt :=          
          let (opt_p, idx) := acc in
          match opt_p with
          | Some p' => (Some p', S idx)
          (* If we do not find the granting in the former borrow trees *)
          | None =>
              (find_granting_aux access t (idx :: p) elt, S idx)
          end in
        fst (fold_left f l (None, O))
  end.

Definition find_granting_list_acc (access: access_kind) (t: tag) (p: tree_path) (acc: option tree_path * nat) elt : (option tree_path * nat) :=
  let (opt_p, idx) := acc in
  match opt_p with
  | Some p' => (Some p', S idx)
  (* If we do not find the granting in the former borrow trees *)
  | None =>
      (find_granting_aux access t (idx :: p) elt, S idx)
  end.

Definition find_granting_list (access: access_kind) (t: tag) (l: list bor_tree') : option tree_path :=
  fst (fold_left (find_granting_list_acc access t []) l (None, O)).

(* remember to reverse the tree_path *)
Definition find_granting (access: access_kind) (t: tag) (bt: bor_tree) : option tree_path :=
  match bt with
  | Broot l =>      
      match find_granting_list access t l with
      | Some p => Some (rev p)
      | None => None
      end
  end.


(* change the state for each item according to the access type. *)
Fixpoint update_subtree_rec (access: access_kind) (bt: bor_tree') : bor_tree' :=
  match bt with
  | Bnode i l =>
      let i' :=
        match i, access with
        | Unique t, Aread
        | Share t, Aread => Share t
        | Unique t, Awrite
        | Share t, Awrite => Disable t
        | Disable _, _ => i
        end in
      Bnode i' (map (update_subtree_rec access) l)
  end.

Definition update_subtree (access: access_kind) (bt: bor_tree') : bor_tree' :=
  (* we do not change the state of the granting item [i] *)
  match bt with
  | Bnode i l => Bnode i (map (update_subtree_rec access) l)
  end.


(* It uses the [update] function to transform the found subtree *)
Fixpoint update_subtree_at' (p: tree_path) (l: list bor_tree') (update: bor_tree' -> bor_tree') : option (list bor_tree') :=
  match p with
  | [] => None
  | [idx] =>      
      match nth_error l idx with
      (* replace the idx-th element *)
      | Some t => Some ((firstn idx l) ++ (update t :: (skipn (S idx) l)))
      | None => None
      end
  | idx :: p' =>
      match nth_error l idx with
      | Some (Bnode i l') =>
          match update_subtree_at' p' l' update with
          | Some l'' =>
              (* replace the idx-th element *)
              Some ((firstn idx l) ++ (Bnode i l'' :: (skipn (S idx) l)))
          | None => None
          end
      | None => None
      end
  end.

Definition access_subtree_at (access: access_kind) (p: tree_path) (bt: bor_tree) : res bor_tree :=
  match bt with
  | Broot l =>
      match update_subtree_at' p l (update_subtree access) with
      | Some l' =>
          OK (Broot l')
      | None =>
          Error [MSG "Unable to find the subtree (access_subtree_at)"]
      end
  end.

(** TODO: consider ownership access  *)
Definition access_bortree (access: access_kind) (t: option tag) (bt: bor_tree) : res bor_tree :=
  match t with
  | Some t =>
      (* access by tag [t] *)
      match find_granting access t bt with
      | Some tp =>
          access_subtree_at access tp bt
      | None =>
          Error [CTX (ident_of_tag t); MSG ": Unable to find the granting item for this tag (access)"]
      end
  | None =>
      (* access by the owner *)
      match bt with
      | Broot l => OK (Broot (map (update_subtree_rec access) l))
      end
  end.

Fixpoint access_block_bortree (access: access_kind) (t: option tag) (bbt: block_bortree) : res block_bortree :=
  match bbt with
  | Bbot => Error [MSG "Access a non-defined block borrow tree (access_block_bortree)"]
  | Batomic bt =>
      do bt <- access_bortree access t bt;
      OK (Batomic bt)
  | Bstruct l =>
      (* fold function that update each block_bortree in each field *)
      let f '(id, elt) := do bbt' <- access_block_bortree access t elt; OK (id, bbt') in
      do bbt'' <- fold_right_bind l f;
      OK (Bstruct bbt'')
  end.

      
(* update block borrow tree while accessing by read or write *)

Definition access (access: access_kind) (b: ablock) (ph: path) (t: option tag) (m: amem) : res amem :=
  do bbt <- load_block_bortree m b ph;
  do bbt' <- access_block_bortree access t bbt;
  store_block_bortree m b ph bbt'.


(** Update borrow stacks while creating new reference *)

Definition access_of_mutkind (mut: mutkind) : access_kind :=
  match mut with
  | Mutable => Awrite
  | Immutable => Aread
  end.

Definition item_of_mutkind (mut: mutkind) (t: tag) : bor_item :=
  match mut with
  | Mutable => Unique t
  | Immutable => Share t
  end.
  
(* insert a bor_tree' in the end of [bt]'s children nodes *)
Definition insert_bor_tree (insert: bor_tree') (bt: bor_tree') : bor_tree' :=
  match bt with
  | Bnode i l => Bnode i (l ++ [insert])
  end.

(* update the borrow tree when creating a reference with mutkind [mut] *)
Definition create_reference (mut: mutkind) (t: option tag) (fresh_tag: tag) (bt: bor_tree): res bor_tree :=
  let access := access_of_mutkind mut in
  (* new sub bor_tree for fresh_tag *)
  let it := item_of_mutkind mut fresh_tag in
  let new_tree := Bnode it nil in
  match t with
  | Some t =>
      match find_granting access t bt with
      | Some tp =>
          (* perform an access: why don't we use [access_bortree]?
             Because we need the tree path to update the borrow tree  *)
          do bt' <- access_subtree_at access tp bt;
          match bt' with
          | Broot l =>
              match update_subtree_at' tp l (insert_bor_tree new_tree) with
              | Some l' => OK (Broot l')
              | None => Error [CTX (ident_of_tag t); CTX (ident_of_tag fresh_tag); MSG "Unable to update the subtree (create_reference)"]
              end
          end
      | None => Error [CTX (ident_of_tag t); MSG ": Unable to find the granting item for this tag (create_reference)"]
      end
  | None =>
      (* owner access *)
      match bt with
      | Broot l =>
          (* perform accesses to the owner's children *)
          let l' := map (update_subtree_rec access) l in
          OK (Broot (l ++ [new_tree]))
      end
  end.

(* update the block borrow tree when creating reference for this whole block *)
Fixpoint update_block_bortree (mut: mutkind) (t: option tag) (fresh_tag: tag) (bbt: block_bortree) : res block_bortree :=
  match bbt with
  | Bbot => Error [MSG "Updating a invalid block borrow tree (update_block_bortree)"]
  | Batomic bt =>
      do bt' <- create_reference mut t fresh_tag bt;
      OK (Batomic bt')
  | Bstruct st =>
      (* fold function that update each block_bortree in each field *)
      let f '(id, elt) := do bbt' <- update_block_bortree mut t fresh_tag elt; OK (id, bbt') in
      do bbt'' <- fold_right_bind st f;
      OK (Bstruct bbt'')
  end.


(* update the memory when creating reference from a pointer (reborrow) *)    
Definition create_reference_from_ptr (mut: mutkind) (p: aptr) (fresh_tag: tag) (m: amem) : res (aptr * amem) :=
  let '(b, ph, t) := p in
  do bbt <- load_block_bortree m b ph;
  (* update the block borrow tree by pushing some new tag *)
  do bbt' <- update_block_bortree mut (Some t) fresh_tag bbt;
  (* store this updated bortree in the abstract memory *)
  do m' <- store_block_bortree m b ph bbt';
  OK (b, ph, fresh_tag, m').

Definition create_reference_from_ptrs (mut: mutkind) (ptrs: Aptrs.t) (fresh_tag: tag) (m: amem) : res (Aptrs.t * amem) :=
  Aptrs.fold (fun ptr acc =>
                do (ptrs, m) <- acc;
                do (ptr', m') <- create_reference_from_ptr mut ptr fresh_tag m;
                OK (Aptrs.add ptr' ptrs, m')) ptrs (OK (Aptrs.empty, m)).

(* (b,p) is the location of the owner *)
Definition create_reference_from_owner (mut: mutkind) (b: ablock) (ph: path) (fresh_tag: tag) (m: amem) : res (aptr * amem) :=
  do bbt <- load_block_bortree m b ph;
  (* update the block borrow tree by pushing some new tag *)
  do bbt' <- update_block_bortree mut None fresh_tag bbt;
  (* store this updated bortree in the abstract memory *)
  do m' <- store_block_bortree m b ph bbt';
  OK ((b, ph, fresh_tag), m').


(** read access with permission checking *)

(* Do we need a mutable load? When creating a mutable reference, the loading is considered as a write action *)
Definition load_aptr (m: amem) (p: aptr) (a: access_kind) : res (aval * amem) :=
  let '(b, ph , t) := p in
  do m' <- access a b ph (Some t) m;
  do v <- load m' b ph;
  OK (v, m').

(* load an abstract pointer with multiple possiblity *)
Definition load_aptrs (m: amem) (ptrs: Aptrs.t) (a: access_kind) : res (aval * amem) :=
  Aptrs.fold (fun elt acc => do (v, m) <- acc; do (v', m') <- load_aptr m elt a; OK (LAval.lub v v', m')) ptrs (OK (LAval.bot, m)).

Definition load_owner (m: amem) (b: ablock) (ph: path) (a: access_kind) : res (aval * amem) :=  
  do m' <- access a b ph None m;
  do v <- load m' b ph;
  OK (v, m').

(* permission checking (these functions are not used for now *)

Definition check_perm_bortree (bt: bor_tree) (t: tag) (a: access_kind) : bool :=
  match find_granting a t bt with
  | Some _ => true
  | None => false
  end.

Fixpoint check_perm_block_bortree (bbt: block_bortree) (t: tag) (a: access_kind) : bool :=
  match bbt with
  | Bbot => false
  | Batomic bt => check_perm_bortree bt t a
  | Bstruct l =>
      (* do we need to consider l is empty? *)
      fold_left (fun acc elt => andb acc (check_perm_block_bortree (snd elt) t a)) l true
  end.

Definition check_perm_aptr (m: amem) (p: aptr) (a: access_kind) : res unit :=
  let '(b, ph, t) := p in
  do bbt <- load_block_bortree m b ph;
  if check_perm_block_bortree bbt t a then
    OK tt
  else
    Error [CTX (ident_of_tag t); MSG ": cannot find its permission"].


Definition check_perm_aptrs (m: amem) (ptrs: Aptrs.t) (a: access_kind) : res unit :=
  Aptrs.fold (fun elt acc => do _ <- acc; check_perm_aptr m elt a) ptrs (OK tt).

End COMPOSITE_ENV.

(** Lattice for dataflow analysis *)

Module AM <: SEMILATTICE.
  
  Inductive t' := | Bot | Err (msg: errmsg) | State (m: amem).
  
  Definition t := t'.

  Definition get_aval (m: amem) (b: ablock) :=
    match b with
    | Stack id =>
        match m.(am_stack)!id with | None => LAval.bot | Some v => v end
    | Heap pc =>
        match m.(am_heap)!pc with | None => LAval.bot | Some v => v end
    | Extern id =>
        match m.(am_external)!id with | None => LAval.bot | Some v => v end
    end.

  Definition get_bt (m: amem) (b: ablock) :=
    match b with
    | Stack id =>
        match m.(am_stack_bortree)!id with | None => LBlkBorTree.bot | Some v => v end
    | Heap pc =>      
        match m.(am_heap_bortree)!pc with | None => LBlkBorTree.bot | Some v => v end
    | Extern id =>
        match m.(am_external_bortree)!id with | None => LBlkBorTree.bot | Some v => v end
    end.
  
  Definition eq (x y : t) : Prop :=
    match x, y with
    | Bot, Bot => True
    | State m1, State m2 =>
        LAvalMap.eq m1.(am_stack) m2.(am_stack) /\
        LBorMap.eq  m1.(am_stack_bortree) m2.(am_stack_bortree) /\
        LAvalMap.eq m1.(am_heap) m2.(am_heap) /\
        LBorMap.eq m1.(am_heap_bortree) m2.(am_heap_bortree) /\
        LAvalMap.eq m1.(am_external) m2.(am_external) /\
        LBorMap.eq m1.(am_external_bortree) m2.(am_external_bortree)
    | _, _ => False
    end.

  Definition beq (x y : t) : bool :=
    match x, y with
    | Bot, Bot => true
    | State m1, State m2 =>
        LAvalMap.beq m1.(am_stack) m2.(am_stack) &&
        LBorMap.beq  m1.(am_stack_bortree) m2.(am_stack_bortree) &&
        LAvalMap.beq m1.(am_heap) m2.(am_heap) &&
        LBorMap.beq m1.(am_heap_bortree) m2.(am_heap_bortree) &&
        LAvalMap.beq m1.(am_external) m2.(am_external) &&
        LBorMap.beq m1.(am_external_bortree) m2.(am_external_bortree)
    | _, _ => false
    end.
      
  Definition ge (x y : t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    (* Err is the top *)
    | Err _, _ => True
    | _, Err _ => False
    | State m1, State m2 =>          
        LAvalMap.ge m1.(am_stack) m2.(am_stack) /\
        LBorMap.ge  m1.(am_stack_bortree) m2.(am_stack_bortree) /\
        LAvalMap.ge m1.(am_heap) m2.(am_heap) /\
        LBorMap.ge m1.(am_heap_bortree) m2.(am_heap_bortree) /\
        LAvalMap.ge m1.(am_external) m2.(am_external) /\
        LBorMap.ge m1.(am_external_bortree) m2.(am_external_bortree)
    end.

  Definition bot := Bot.
  
  Definition lub (x y: t) :=
    match x,y with
    | _, Bot => x
    | Bot, _ => y
    | Err _, State _ => x
    | State _, Err _ => y
    | Err msg1, Err msg2 =>
        Err ((MSG "Error 1: ") :: msg1 ++ (MSG "; Error 2: " :: msg2))
    | State m1, State m2 =>
        State (build_amem
                 (LAvalMap.lub m1.(am_stack) m2.(am_stack)) 
                 (LBorMap.lub m1.(am_stack_bortree) m2.(am_stack_bortree))
                 (LAvalMap.lub m1.(am_heap) m2.(am_heap)) 
                 (LBorMap.lub m1.(am_heap_bortree) m2.(am_heap_bortree))
                 (LAvalMap.lub m1.(am_external) m2.(am_external)) 
                 (LBorMap.lub m1.(am_external_bortree) m2.(am_external_bortree)))
    end.

  (** TODO  *)
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End AM.
