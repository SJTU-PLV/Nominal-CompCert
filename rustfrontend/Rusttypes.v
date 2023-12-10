(** Type for Rustlight languages  *)

Require Import Axioms Coqlib Maps Errors.
Require Import AST Linking.
Require Import Ctypes.
Require Archi.

Set Asymmetric Patterns.

Local Open Scope error_monad_scope.

Inductive usekind : Type :=
| Copy
| Move.                        (**r used for types that are unsafe for copying *)


(** ** Types  *)

Inductive type : Type :=
| Tunit: type                                    (**r the [unit] type *)
| Tint: intsize -> signedness -> attr -> type       (**r integer types *)
| Tlong : signedness -> attr -> type
| Tfloat : floatsize -> attr -> type
| Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
| Tstruct: ident -> attr -> type                              (**r struct types  *)
| Tvariant: ident -> attr -> type                             (**r tagged union types *)
with typelist : Type :=
| Tnil: typelist
| Tcons: type -> typelist -> typelist.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}.
Proof.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  generalize ident_eq zeq bool_dec ident_eq intsize_eq signedness_eq attr_eq; intros.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
Defined.

Global Opaque type_eq typelist_eq.

Definition attr_of_type (ty: type) :=
  match ty with
  | Tunit => noattr
  | Tint sz si a => a
  | Tlong si a => a
  | Tfloat sz a => a
  | Tfunction args res cc => noattr
  | Tstruct id a => a
  | Tvariant id a => a
  end.

(** access mode for Rust types  *)
Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tlong _ _ => By_value Mint64
  | Tfloat F32 _ => By_value Mfloat32
  | Tfloat F64 _ => By_value Mfloat64                                   
  | Tunit => By_nothing
  | Tfunction _ _ _ => By_reference
  | Tstruct _ _ => By_copy
  | Tvariant _ _ => By_copy
end.


(** Composite  *)

Inductive struct_or_variant : Set :=  Struct : struct_or_variant | TaggedUnion : struct_or_variant.

Inductive member : Type :=
  | Member_plain (id: ident) (t: type).

Definition members : Type := list member.

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_variant) (m: members) (a: attr).

Definition name_member (m: member) : ident :=
  match m with
  | Member_plain id _ => id
  end.

Definition type_member (m: member) : type :=
  match m with
  | Member_plain _ t => t
  end.

Definition member_is_padding (m: member) : bool :=
  match m with
  | Member_plain _ _ => false
  end.

Definition name_composite_def (c: composite_definition) : ident :=
  match c with Composite id su m a => id end.

Definition composite_def_eq (x y: composite_definition): {x=y} + {x<>y}.
Proof.
  decide equality.
- decide equality. decide equality. apply N.eq_dec. apply bool_dec.
- apply list_eq_dec. decide equality.
  apply type_eq. apply ident_eq.
- decide equality.
- apply ident_eq.
Defined.

Global Opaque composite_def_eq. 

(** For type-checking, compilation and semantics purposes, the composite
  definitions are collected in the following [composite_env] environment.
  The [composite] record contains additional information compared with
  the [composite_definition], such as size and alignment information. *)

Record composite : Type := {
  co_sv: struct_or_variant;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.

Definition composite_env : Type := PTree.t composite.

(** ** Complete types *)

(** A type is complete if it fully describes an object.
  All struct and union names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. *)

Definition complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tunit => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | Tfunction _ _ _ => false
  | Tstruct id _ | Tvariant id _ =>
      match env!id with Some co => true | None => false end
  end.

Definition complete_or_function_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tfunction _ _ _ => true
  | _ => complete_type env t
  end.


(** ** Alignment of a type *)

(** Adjust the natural alignment [al] based on the attributes [a] attached
  to the type.  If an "alignas" attribute is given, use it as alignment
  in preference to [al]. *)

Definition align_attr (a: attr) (al: Z) : Z :=
  match attr_alignas a with
  | Some l => two_p (Z.of_N l)
  | None => al
  end.

Definition alignof (env: composite_env) (t: type) : Z :=
  align_attr (attr_of_type t)
   (match t with
      | Tunit => 1
      | Tint I8 _ _ => 1
      | Tint I16 _ _ => 2
      | Tint I32 _ _ => 4
      | Tint IBool _ _ => 1
      | Tlong _ _ => Archi.align_int64
      | Tfloat F32 _ => 4
      | Tfloat F64 _ => Archi.align_float64
      | Tfunction _ _ _ => 1
      | Tstruct id _ | Tvariant id _ =>
          match env!id with Some co => co_alignof co | None => 1 end
    end).

Remark align_attr_two_p:
  forall al a,
  (exists n, al = two_power_nat n) ->
  (exists n, align_attr a al = two_power_nat n).
Proof.
  intros. unfold align_attr. destruct (attr_alignas a).
  exists (N.to_nat n). rewrite two_power_nat_two_p. rewrite N_nat_Z. auto.
  auto.
Qed.

Lemma alignof_two_p:
  forall env t, exists n, alignof env t = two_power_nat n.
Proof.
  induction t; apply align_attr_two_p; simpl.
  exists 0%nat; auto.
  destruct i.
    exists 0%nat; auto.
    exists 1%nat; auto.
    exists 2%nat; auto.
    exists 0%nat; auto.
    unfold Archi.align_int64. destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
  destruct f.
    exists 2%nat; auto.
    unfold Archi.align_float64. destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
  exists 0%nat; auto.
  destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
  destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
Qed.

Lemma alignof_pos:
  forall env t, alignof env t > 0.
Proof.
  intros. destruct (alignof_two_p env t) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
Qed.

(** Ownership type  *)

Fixpoint own_type (fuel: nat) (ce: composite_env) (ty: type) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match ty with
      | Tstruct id _ | Tvariant id _ =>
          match ce ! id with
          | Some co =>
              let acc res m :=
                let own := (match m with
                            | Member_plain fid fty =>
                                own_type fuel' ce fty
                            end) in
                orb res own in
              fold_left acc co.(co_members) false
          | None => false
          end
      (** TODO: unique pointer and mutable reference are own type  *)
      | _ => false
      end
  end.



(** Size of a type  *)

Definition sizeof (env: composite_env) (t: type) : Z :=
  match t with
  | Tunit => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _
  | Tfloat F32 _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _
  | Tfloat F64 _ => 8
  | Tfunction _ _ _ => 1
  | Tstruct id _
  | Tvariant id _ =>
      match env!id with
      | Some co => co_sizeof co
      | None => 0
      end                    
  end.

Lemma sizeof_pos:
  forall env t, sizeof env t >= 0.
Proof.
  induction t; simpl.
- lia.
- destruct i; lia.
- lia.
- destruct f; lia.
- destruct Archi.ptr64; lia.
- destruct (env!i). apply co_sizeof_pos. lia.
- destruct (env!i). apply co_sizeof_pos. lia.
Qed.

Definition alignof_blockcopy (env: composite_env) (t: type) : Z :=
  match t with
  | Tunit => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _
  | Tfloat F32 _ => 4
  | Tlong _ _
  | Tfloat F64 _ => 8
  | Tint IBool _ _ => 1
  | Tfunction _ _ _ => 1
  | Tstruct id _
  | Tvariant id _ =>
      match env!id with
      | Some co => Z.min 8 (co_alignof co)
      | None => 1
      end
  end.


(** ** Layout of struct fields *)

Section LAYOUT.

Variable env: composite_env.

Definition bitalignof (t: type) := alignof env t * 8.

Definition bitsizeof  (t: type) := sizeof env t * 8.

Definition bitalignof_intsize (sz: intsize) : Z :=
  match sz with
  | I8 | IBool => 8
  | I16 => 16
  | I32 => 32
  end.

(* The index of the variant *)
Fixpoint field_tag' (fid: ident) (ms: members) (pos: Z) : option Z :=
  match ms with
  | nil => None
  | m::ms =>
      match m with
      | Member_plain id _ =>
          if Pos.eqb fid id
          then Some pos
          else field_tag' fid ms (pos + 1)
      end
  end.

Definition field_tag (fid: ident) (ms:members) : option Z :=
  field_tag' fid ms 0.

Fixpoint type_tag' (ty: type) (ms: members) (pos: Z) {struct ms} : option (ident * Z) :=
  match ms with
  | nil => None
  | m::ms =>
      match m with
      | Member_plain id ty' =>
          if type_eq ty ty' then
            Some (id,pos)
          else
            type_tag' ty ms (pos + 1) 
      end
  end.

Definition type_tag (ty: type) (ms:members) : option (ident*Z) :=
  type_tag' ty ms 0.

Definition next_field (pos: Z) (m: member) : Z :=
  match m with
  | Member_plain _ t =>
      align pos (bitalignof t) + bitsizeof t
  end.

Definition layout_field (pos: Z) (m: member) : res (Z * bitfield) :=
  match m with
  | Member_plain _ t =>
      OK (align pos (bitalignof t) / 8, Full)
  end.

(** Some properties *)

Lemma bitalignof_intsize_pos:
  forall sz, bitalignof_intsize sz > 0.
Proof.
  destruct sz; simpl; lia.
Qed.

Lemma next_field_incr:
  forall pos m, pos <= next_field pos m.
Proof.
  intros. unfold next_field. destruct m.
- set (al := bitalignof t).
  assert (A: al > 0).
  { unfold al, bitalignof. generalize (alignof_pos env t). lia. }
  assert (pos <= align pos al) by (apply align_le; auto).
  assert (bitsizeof t >= 0).
  { unfold bitsizeof. generalize (sizeof_pos env t). lia. } 
  lia.
Qed.

Definition layout_start (p: Z) (bf: bitfield) :=
  p * 8 + match bf with Full => 0 | Bits sz sg pos w => pos end.

Definition layout_width (t: type) (bf: bitfield) :=
  match bf with Full => bitsizeof t | Bits sz sg pos w => w end.

Lemma layout_field_range: forall pos m ofs bf,
  layout_field pos m = OK (ofs, bf) ->
  pos <= layout_start ofs bf 
  /\ layout_start ofs bf + layout_width (type_member m) bf <= next_field pos m.
Proof.
  intros until bf; intros L. unfold layout_start, layout_width. destruct m; simpl in L.
- inv L. simpl.
  set (al := bitalignof t).
  set (q := align pos al).
  assert (A: al > 0).
  { unfold al, bitalignof. generalize (alignof_pos env t). lia. }
  assert (B: pos <= q) by (apply align_le; auto).
  assert (C: (al | q)) by (apply align_divides; auto).
  assert (D: (8 | q)). 
  { apply Z.divide_transitive with al; auto. apply Z.divide_factor_r. }
  assert (E: q / 8 * 8 = q).
  { destruct D as (n & E). rewrite E. rewrite Z.div_mul by lia. auto. }
  rewrite E. lia.
Qed.

Definition layout_alignment (t: type) (bf: bitfield) :=
  match bf with
  | Full => alignof env t
  | Bits sz _ _ _ => bitalignof_intsize sz / 8
  end.

Lemma layout_field_alignment: forall pos m ofs bf,
  layout_field pos m = OK (ofs, bf) ->
  (layout_alignment (type_member m) bf | ofs).
Proof.
  intros until bf; intros L. destruct m; simpl in L.
- inv L; simpl. 
  set (q := align pos (bitalignof t)).
  assert (A: (bitalignof t | q)).
  { apply align_divides. unfold bitalignof. generalize (alignof_pos env t). lia. }
  destruct A as [n E]. exists n. rewrite E. unfold bitalignof. rewrite Z.mul_assoc, Z.div_mul by lia. auto.
Qed.

End LAYOUT.


(** ** Size and alignment for composite definitions *)

(** The alignment for a structure or variant is the max of the alignment
  of its members.  Padding bitfields are ignored. *)

Fixpoint alignof_composite (env: composite_env) (ms: members) : Z :=
  match ms with
  | nil => 1
  | m :: ms => 
     if member_is_padding m
     then alignof_composite env ms
     else Z.max (alignof env (type_member m)) (alignof_composite env ms)
  end.

(** The size of a structure corresponds to its layout: fields are
  laid out consecutively, and padding is inserted to align
  each field to the alignment for its type.  Bitfields are packed
  as described above. *)

Fixpoint bitsizeof_struct (env: composite_env) (cur: Z) (ms: members) : Z :=
  match ms with
  | nil => cur
  | m :: ms => bitsizeof_struct env (next_field env cur m) ms
  end.

Definition bytes_of_bits (n: Z) := (n + 7) / 8.

Definition sizeof_struct (env: composite_env) (m: members) : Z :=
  bytes_of_bits (bitsizeof_struct env 0 m).

(** The size of an variant is the size of tagged (4 bytes) plus the
max of the sizes of its members. *)

Fixpoint sizeof_variant' (env: composite_env) (ms: members) : Z :=
  (match ms with
  | nil => 0
  | m :: ms => Z.max (sizeof env (type_member m)) (sizeof_variant' env ms)
  end).

Definition sizeof_variant (env: composite_env) (ms: members) : Z :=
  sizeof_variant' env ms + 4.

(** Some properties *)

Lemma alignof_composite_two_p:
  forall env m, exists n, alignof_composite env m = two_power_nat n.
Proof.
  induction m; simpl.
- exists 0%nat; auto.
- destruct (member_is_padding a); auto.
  apply Z.max_case; auto. apply alignof_two_p.
Qed.

Lemma alignof_composite_pos:
  forall env m a, align_attr a (alignof_composite env m) > 0.
Proof.
  intros.
  exploit align_attr_two_p. apply (alignof_composite_two_p env m).
  instantiate (1 := a). intros [n EQ].
  rewrite EQ; apply two_power_nat_pos.
Qed.

Lemma bitsizeof_struct_incr:
  forall env m cur, cur <= bitsizeof_struct env cur m.
Proof.
  induction m; simpl; intros.
- lia.
- apply Z.le_trans with (next_field env cur a).
  apply next_field_incr. apply IHm.
Qed.

Lemma sizeof_variant'_pos:
  forall env m, 0 <= sizeof_variant' env m.
Proof.
  induction m; simpl; extlia.  
Qed.

Lemma sizeof_variant_pos:
  forall env m, 0 <= sizeof_variant env m.
Proof.
  intros. unfold sizeof_variant.
  generalize (sizeof_variant'_pos env m).
  lia.
Qed.
  
(** Type ranks *)

(** The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and union types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. *)

Definition rank_type (ce: composite_env) (t: type) : nat :=
  match t with
  | Tstruct id _ | Tvariant id _ =>
      match ce!id with
      | None => O
      | Some co => S (co_rank co)
      end
  | _ => O
  end.

Fixpoint rank_members (ce: composite_env) (m: members) : nat :=
  match m with
  | nil => 0%nat
  | Member_plain _ t :: m => Init.Nat.max (rank_type ce t) (rank_members ce m)
  end.


(** ** Rust types and back-end types *)

(** Extracting a type list from a function parameter declaration. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** Translating C types to Cminor types and function signatures. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tunit => AST.Tint
  | Tint _ _ _ => AST.Tint
  | Tlong _ _ => AST.Tlong
  | Tfloat F32 _ => AST.Tsingle
  | Tfloat F64 _ => AST.Tfloat
  | Tfunction _ _ _ | Tstruct _ _ | Tvariant _ _ => AST.Tptr
  end.

Definition rettype_of_type (t: type) : AST.rettype :=
  match t with
  | Tunit => AST.Tvoid
  | Tint I32 _ _ => AST.Tint
  | Tint I8 Signed _ => AST.Tint8signed
  | Tint I8 Unsigned _ => AST.Tint8unsigned
  | Tint I16 Signed _ => AST.Tint16signed
  | Tint I16 Unsigned _ => AST.Tint16unsigned
  | Tint IBool _ _ => AST.Tint8unsigned
  | Tlong _ _ => AST.Tlong
  | Tfloat F32 _ => AST.Tsingle
  | Tfloat F64 _ => AST.Tfloat
  | Tfunction _ _ _ | Tstruct _ _ | Tvariant _ _ => AST.Tvoid
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) (cc: calling_convention): signature :=
  mksignature (typlist_of_typelist args) (rettype_of_type res) cc.


(** * Construction of the composite environment *)

Definition sizeof_composite (env: composite_env) (sv: struct_or_variant) (m: members) : Z :=
  match sv with
  | Struct => sizeof_struct env m
  | TaggedUnion  => sizeof_variant env m
  end.

Lemma sizeof_composite_pos:
  forall env su m, 0 <= sizeof_composite env su m.
Proof.
  intros. destruct su; simpl.
- unfold sizeof_struct, bytes_of_bits.
  assert (0 <= bitsizeof_struct env 0 m) by apply bitsizeof_struct_incr.
  change 0 with (0 / 8) at 1. apply Z.div_le_mono; lia.
- apply sizeof_variant_pos.
Qed.

Fixpoint complete_members (env: composite_env) (ms: members) : bool :=
  match ms with
  | nil => true
  | m :: ms => complete_type env (type_member m) && complete_members env ms
  end.

Lemma complete_member:
  forall env m ms,
  In m ms -> complete_members env ms = true -> complete_type env (type_member m) = true.
Proof.
  induction ms as [|m1 ms]; simpl; intuition auto.
  InvBooleans; inv H1; auto.
  InvBooleans; eauto.
Qed.

Program Definition composite_of_def
     (env: composite_env) (id: ident) (su: struct_or_variant) (m: members) (a: attr)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or union " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or union " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite env m) in
      OK {| co_sv := su;
            co_members := m;
            co_attr := a;
            co_sizeof := align (sizeof_composite env su m) al;
            co_alignof := al;
            co_rank := rank_members env m;
            co_sizeof_pos := _;
            co_alignof_two_p := _;
            co_sizeof_alignof := _ |}
  end.
Next Obligation.
  apply Z.le_ge. eapply Z.le_trans. eapply sizeof_composite_pos.
  apply align_le; apply alignof_composite_pos.
Defined.
Next Obligation.
  apply align_attr_two_p. apply alignof_composite_two_p.
Defined.
Next Obligation.
  apply align_divides. apply alignof_composite_pos.
Defined.

(** The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the definition of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. *)

Fixpoint add_composite_definitions (env: composite_env) (defs: list composite_definition) : res composite_env :=
  match defs with
  | nil => OK env
  | Composite id su m a :: defs =>
      do co <- composite_of_def env id su m a;
      add_composite_definitions (PTree.set id co env) defs
  end.

Definition build_composite_env (defs: list composite_definition) :=
  add_composite_definitions (PTree.empty _) defs.


(** ** Byte offset and bitfield designator for a field of a structure *)

Fixpoint field_type (id: ident) (ms: members) {struct ms} : res type :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms => if ident_eq id (name_member m) then OK (type_member m) else field_type id ms
  end.

(** [field_offset env id fld] returns the byte offset for field [id]
  in a structure whose members are [fld].  It also returns a
  bitfield designator, giving the location of the bits to access
  within the storage unit for the bitfield. *)

Fixpoint field_offset_rec (env: composite_env) (id: ident) (ms: members) (pos: Z)
                          {struct ms} : res (Z * bitfield) :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms =>
      if ident_eq id (name_member m)
      then layout_field env pos m
      else field_offset_rec env id ms (next_field env pos m)
  end.

Definition field_offset (env: composite_env) (id: ident) (ms: members) : res (Z * bitfield) :=
  field_offset_rec env id ms 0.

(** field_offset_all returns all the byte offset for fileds in a structure  *)

Fixpoint field_offset_all_rec (env: composite_env) (ms: members) (pos: Z)
                          {struct ms} : res (list (Z * bitfield)) :=
  match ms with
  | nil => OK nil
  | m :: ms =>
      do ofsm <- layout_field env pos m;
      do ofsms <- field_offset_all_rec env ms (next_field env pos m);
      OK (ofsm :: ofsms)
  end.

Definition field_offset_all (env: composite_env) (ms: members) : res (list (Z * bitfield)) :=
  field_offset_all_rec env ms 0.

(* [field_zero_or_padding m] returns true if the field is a zero length bitfield
   or does not have a name *)
Definition field_zero_or_padding (m: member) : bool :=
  match m with
  | Member_plain _ _ => false
  (* | Member_bitfield _ _ _ _ w p => orb (zle w 0) p *)
  end.

(** [layout_struct env ms accu pos] computes the layout of all fields of a struct that
    are not unnamed or zero width bitfield members *)
Fixpoint layout_struct_rec (env: composite_env) (ms: members)
                           (accu: list (ident * Z * bitfield)) (pos: Z)
                           {struct ms} : res (list (ident * Z * bitfield)) :=
  match ms with
  | nil => OK accu
  | m :: ms =>
      if field_zero_or_padding m then
        layout_struct_rec env ms accu (next_field env pos m)
      else
        do (p, b) <- layout_field env pos m;
        layout_struct_rec env ms (((name_member m), p ,b) :: accu) (next_field env pos m)
  end.

Definition layout_struct (env: composite_env) (ms: members) : res (list (ident * Z * bitfield)) :=
  layout_struct_rec env ms nil 0.

(** Some sanity checks about field offsets.  First, field offsets are
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall env id ofs bf ty ms pos,
  field_offset_rec env id ms pos = OK (ofs, bf) -> field_type id ms = OK ty ->
  pos <= layout_start ofs bf
  /\ layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env pos ms.
Proof.
  induction ms as [ | m ms]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)).
  + inv H0. 
    exploit layout_field_range; eauto.
    generalize (bitsizeof_struct_incr env ms (next_field env pos m)).
    lia.
  + exploit IHms; eauto.
    generalize (next_field_incr env pos m).
    lia.
Qed.

Lemma field_offset_in_range_gen:
  forall env ms id ofs bf ty,
  field_offset env id ms = OK (ofs, bf) -> field_type id ms = OK ty ->
  0 <= layout_start ofs bf
  /\ layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env 0 ms.
Proof.
  intros. eapply field_offset_rec_in_range; eauto.
Qed.

Corollary field_offset_in_range:
  forall env ms id ofs ty,
  field_offset env id ms = OK (ofs, Full) -> field_type id ms = OK ty ->
  0 <= ofs /\ ofs + sizeof env ty <= sizeof_struct env ms.
Proof.
  intros. exploit field_offset_in_range_gen; eauto. 
  unfold layout_start, layout_width, bitsizeof, sizeof_struct. intros [A B].
  assert (C: forall x y, x * 8 <= y -> x <= bytes_of_bits y).
  { unfold bytes_of_bits; intros. 
    assert (P: 8 > 0) by lia.
    generalize (Z_div_mod_eq (y + 7) 8 P) (Z_mod_lt (y + 7) 8 P).
    lia. }
  split. lia. apply C. lia.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall env id1 ofs1 bf1 ty1 id2 ofs2 bf2 ty2 fld,
  field_offset env id1 fld = OK (ofs1, bf1) -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK (ofs2, bf2) -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  layout_start ofs1 bf1 + layout_width env ty1 bf1 <= layout_start ofs2 bf2
  \/ layout_start ofs2 bf2 + layout_width env ty2 bf2 <= layout_start ofs1 bf1.
Proof.
  intros until fld. unfold field_offset. generalize 0 as pos.
  induction fld as [|m fld]; simpl; intros.
- discriminate.
- destruct (ident_eq id1 (name_member m)); destruct (ident_eq id2 (name_member m)).
+ congruence.
+ inv H0.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. lia.
+ inv H2.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. lia.
+ eapply IHfld; eauto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Lemma field_offset_prefix:
  forall env id ofs bf fld2 fld1,
  field_offset env id fld1 = OK (ofs, bf) ->
  field_offset env id (fld1 ++ fld2) = OK (ofs, bf).
Proof.
  intros until fld1. unfold field_offset. generalize 0 as pos.
  induction fld1 as [|m fld1]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)); auto.
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned_gen:
  forall env id fld ofs bf ty,
  field_offset env id fld = OK (ofs, bf) -> field_type id fld = OK ty ->
  (layout_alignment env ty bf | ofs).
Proof.
  intros until ty. unfold field_offset. generalize 0 as pos. revert fld.
  induction fld as [|m fld]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)).
+ inv H0. eapply layout_field_alignment; eauto.
+ eauto.
Qed.

Corollary field_offset_aligned:
  forall env id fld ofs ty,
  field_offset env id fld = OK (ofs, Full) -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
  intros. exploit field_offset_aligned_gen; eauto.
Qed.

(** [union_field_offset env id ms] returns the byte offset (plus 4 bytes) and
    bitfield designator for accessing a member named [id] of a union
    whose members are [ms].  The byte offset is always 0. *)

Fixpoint variant_field_offset (env: composite_env) (id: ident) (ms: members)
                          {struct ms} : res (Z * bitfield) :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms =>
      if ident_eq id (name_member m)
      then layout_field env 4 m
      else variant_field_offset env id ms
  end.


(** Some sanity checks about union field offsets.  First, field offsets
    fit within the size of the union. *)

Section PROGRAMS.

(** move to Rusttypes *)
Variable F: Type.

Inductive fundef : Type :=
| Internal: F -> fundef
| External: external_function -> typelist -> type -> calling_convention -> fundef.

Global Instance rustlight_fundef_is_internal : FundefIsInternal fundef :=
  fun f =>
    match f with
      | Internal _ => true
      | _ => false
    end.

Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.

End PROGRAMS.
