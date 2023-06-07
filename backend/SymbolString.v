Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Ascii String.

(** This an external function in ML for 
    finding the strings associated with the global symbols *)
Parameter find_symbol_pos : ident -> option (list positive).

Parameter string_to_ident : list byte -> option ident.

Parameter create_float_literal_ident : unit -> ident.

Parameter create_int64_literal_ident : unit -> ident.

Parameter create_float_mask_ident : unit -> ((ident*ident)*(ident*ident)).

Parameter create_jump_table_ident : unit -> ident.

Parameter create_label_ident : unit -> ident.

Parameter create_section_ident: unit -> ident.

(** Special Sections *)
Parameter create_text_section_ident: unit -> ident.
Parameter create_data_section_ident: unit -> ident.
Parameter create_rodata_section_ident: unit -> ident.
Parameter create_text_rel_ident: unit -> ident.
Parameter create_data_rel_ident: unit -> ident.
Parameter create_rodata_rel_ident: unit -> ident.

Axiom string_to_ident_symbol_to_pos:
  forall s lb, find_symbol_pos s = Some lb ->
               string_to_ident (map (fun p => Byte.repr (Zpos p)) lb) = Some s.
