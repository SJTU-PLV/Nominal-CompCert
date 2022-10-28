(* *******************  *)
(* Author: Jinhua Wu  *)
(* Date:   Jun 19, 2022 *)
(* *******************  *)

(* Generate special section identity *)

open Camlcoq
open BinNums

let create_text_section_ident () : positive =
  let id = intern_string ".text" in
  id

let create_data_section_ident () : positive =
  let id = intern_string ".data" in
  id

let create_rodata_section_ident () : positive =
  let id = intern_string ".rodata" in
  id

let create_text_rel_ident () : positive =
  let id = intern_string ".rel.text" in
  id

let create_data_rel_ident () : positive =
  let id = intern_string ".rel.data" in
  id

let create_rodata_rel_ident () : positive =
  let id = intern_string ".rel.rodata" in
  id