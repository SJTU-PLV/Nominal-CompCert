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
| Tunion: ident -> attr -> type                               (**r union types *)
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

Definition attr_of_type (ty: type) :=
  match ty with
  | Tunit => noattr
  | Tint sz si a => a
  | Tlong si a => a
  | Tfloat sz a => a
  | Tfunction args res cc => noattr
  | Tstruct id a => a
  | Tunion id a => a
  end.


(** Composite  *)

Inductive member : Type :=
  | Member_plain (id: ident) (t: type).

Definition members : Type := list member.

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_union) (m: members) (a: attr).

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
  co_su: struct_or_union;
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

Fixpoint complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tunit => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | Tfunction _ _ _ => false
  | Tstruct id _ | Tunion id _ =>
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
      | Tstruct id _ | Tunion id _ =>
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
  | Tunion id _ =>
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
  | Tunion id _ =>
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

(** The alignment for a structure or union is the max of the alignment
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

(** The size of an union is the max of the sizes of its members. *)

Fixpoint sizeof_union (env: composite_env) (ms: members) : Z :=
  match ms with
  | nil => 0
  | m :: ms => Z.max (sizeof env (type_member m)) (sizeof_union env ms)
  end.


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

Lemma sizeof_union_pos:
  forall env m, 0 <= sizeof_union env m.
Proof.
  induction m; simpl; extlia.
Qed.

(** Type ranks *)

(** The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and union types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. *)

Fixpoint rank_type (ce: composite_env) (t: type) : nat :=
  match t with
  | Tstruct id _ | Tunion id _ =>
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


(** * Construction of the composite environment *)

Definition sizeof_composite (env: composite_env) (su: struct_or_union) (m: members) : Z :=
  match su with
  | Struct => sizeof_struct env m
  | Union  => sizeof_union env m
  end.

Lemma sizeof_composite_pos:
  forall env su m, 0 <= sizeof_composite env su m.
Proof.
  intros. destruct su; simpl.
- unfold sizeof_struct, bytes_of_bits.
  assert (0 <= bitsizeof_struct env 0 m) by apply bitsizeof_struct_incr.
  change 0 with (0 / 8) at 1. apply Z.div_le_mono; lia.
- apply sizeof_union_pos.
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
     (env: composite_env) (id: ident) (su: struct_or_union) (m: members) (a: attr)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or union " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or union " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite env m) in
      OK {| co_su := su;
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

Section PROGRAMS.

(** move to Rusttypes *)
Variable F: Type.

Inductive fundef : Type :=
| Internal: F -> fundef
| External: external_function -> typelist -> type -> calling_convention -> fundef.


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
