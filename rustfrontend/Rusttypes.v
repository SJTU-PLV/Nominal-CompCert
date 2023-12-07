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

(** Access modes for members of structs or unions: either a plain field
    or a bitfield *)

Inductive bitfield : Type :=
  | Full
  | Bits (sz: intsize) (sg: signedness) (pos: Z) (width: Z).


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
