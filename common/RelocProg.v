(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 13, 2019 *)
(* Last updated:  Feb 27, 2022 by Jinhua Wu*)
(* *******************  *)

(** * Template of languages with information about symbols and relocation *)

Require Import Coqlib Maps Integers Values AST.
Require Import Globalenvs.
Require Import Permutation.
Require Import LocalLib.

Import List.ListNotations.

(** ** Sections *)

Inductive section (I D:Type): Type :=
| sec_text (code: list I)
| sec_rwdata (init: list D)
| sec_rodata (init: list D).
(* (* | sec_rodata (init: list init_data) *) *)
(* | sec_bytes (bs: list byte). *)

Arguments sec_text [I D].
Arguments sec_rwdata [I D].
Arguments sec_rodata [I D].

(** Gnerate one section for each definition *)
(** The section table is the map from ident to section *)
Definition sectable (I D: Type) := PTree.t (section I D).

(** ** Symbol table *)

(* Different from the elf file format, we use read-write and read-only two type to represent data . Because encoding elminates the section type infomation. *)
Inductive symbtype : Type := symb_func | symb_data | symb_notype.

Definition symbtype_eq_dec : forall (t1 t2: symbtype), {t1 = t2} + {t1 <> t2}.
Proof.
  intros. destruct t1;destruct t2;auto;right;congruence.
Qed.


(** normal: point to a section *)
Inductive secindex : Type :=
| secindex_normal (idx:ident)
| secindex_comm
| secindex_undef.

Inductive bindtype : Type :=
| bind_local
| bind_global.

Record symbentry : Type :=
{
  (* symbentry_id: ident;  *) (** The original identifier of the symbol *) 
  symbentry_bind: bindtype;
  symbentry_type: symbtype;
  symbentry_value: Z;  (** This holds the alignment info if secindex is secindex_comm,
                           otherwise, it holds the offset from the beginning of the section *)
  symbentry_secindex: secindex;
  symbentry_size: Z;
}.

Definition is_symbentry_internal e :=
  match symbentry_secindex e with
  | secindex_normal _ => true
  | _ => false
  end.

(** symbtable is the mapping from id to symbentry *)
Definition symbtable := PTree.t symbentry.

(** ** Relocation table *)
Inductive reloctype : Type := reloc_abs | reloc_rel | reloc_null.

Record relocentry : Type :=
{
  reloc_offset: Z;
  reloc_type  : reloctype;
  reloc_symb  : ident;    (* Index into the symbol table *)
  reloc_addend : Z;
}.

(* Module RelocTable := SeqTable(RelocTblParams). *)
Definition reloctable := list relocentry.
Definition reloctable_map := PTree.t reloctable.

(** ** Definition of program constructs *)

(* Definition gdef := AST.globdef fundef unit. *)

Record program (F V I D: Type): Type := {
  prog_defs : list (ident * AST.globdef F V); (** Only used in external function reasoning *)
  prog_public: list ident;
  prog_main: ident;
  prog_sectable: sectable I D;
  prog_symbtable: symbtable;
  prog_reloctables: reloctable_map;
  prog_senv : Globalenvs.Senv.t }.


Arguments prog_defs [F V I D].
Arguments prog_public [F V I D].
Arguments prog_main [F V I D].
Arguments prog_sectable [F V I D].
Arguments prog_symbtable [F V I D].
Arguments prog_reloctables [F V I D].
Arguments prog_senv [F V I D].

(** Generate the mapping from symbol ids to indexes *)
Definition symb_index_map_type := PTree.t N.

Definition reloc_ofs_map_type := ZTree.t relocentry.

Definition acc_reloc_ofs_map (e:relocentry) (rs: reloc_ofs_map_type): reloc_ofs_map_type :=
  let ofs := reloc_offset e in
  ZTree.set ofs e rs.

Definition gen_reloc_ofs_map (rtbl: reloctable) :  reloc_ofs_map_type :=
  fold_right acc_reloc_ofs_map (ZTree.empty relocentry) rtbl.

(* Coercion prog_to_prog : program >-> AST.program. *)

(** Section table ids *)
(* Definition sec_rodata_id   := 1%N. *)
(* Definition sec_data_id     := 2%N. *)
(* Definition sec_code_id     := 3%N. *)
Definition sec_strtbl_id   := 4%N.
Definition sec_symbtbl_id  := 5%N.
(* Definition sec_rel_rodata_id := 6%N. *)
(* Definition sec_rel_data_id := 7%N. *)
(* Definition sec_rel_code_id := 8%N. *)
Definition sec_shstrtbl_id := 9%N.

(** Ultility function s*)
(* Definition add_symb_to_list (t: list (ident * symbentry)) (s:symbentry) := *)
(*   (symbentry_id s, s) :: t. *)
Definition symbtable_to_idlist (t:symbtable) := 
  (PTree.elements t).

Definition get_symbentry_ids (t:symbtable) : list ident :=
  map fst (PTree.elements t).


Lemma get_symbentry_ids_add_symb_eq: forall stbl, 
    get_symbentry_ids stbl = (map fst (symbtable_to_idlist stbl)).
Proof.
  unfold get_symbentry_ids.
  intros.
  unfold symbtable_to_idlist.
  auto.
Qed.
