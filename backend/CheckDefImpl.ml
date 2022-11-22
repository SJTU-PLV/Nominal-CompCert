(** * Check if the definition is a local or global one *)

open C2C
open AST

let is_def_string_literal (id: ident) : bool =
  let lit_sec = [Sections.for_stringlit()] in
  try 
    let a = Hashtbl.find decl_atom id in
    a.a_sections = lit_sec
  with
  | Not_found ->
     false

let is_def_static (id: ident) : bool =
  atom_is_static id