open Format
open Camlcoq
(* open Values *)
open AST
open! Rusttypes
(* open Cop *)
(* open Rustsyntax *)
open PrintCsyntax

let string_of_mut mut =
  match mut with
  | Mutable -> "mut"
  | Immutable -> ""

let rec print_origins_aux (orgs : origin list) =
  match orgs with
  | [] -> ""
  | org :: orgs' -> extern_atom org ^ print_origins_aux orgs'

let print_origins (orgs : origin list) =
  match orgs with
  | [] -> ""
  | _ -> "<" ^ print_origins_aux orgs^ ">"
  

let rec name_rust_decl id ty =
  match ty with
  | Rusttypes.Tunit ->
      "()" ^ name_optid id
  | Rusttypes.Tint(sz, sg, a) ->
      name_inttype sz sg ^ attributes a ^ name_optid id
  | Rusttypes.Tfloat(sz, a) ->
      name_floattype sz ^ attributes a ^ name_optid id
  | Rusttypes.Tlong(sg, a) ->
      name_longtype sg ^ attributes a ^ name_optid id
  | Rusttypes.Treference(org, mut, t, a) ->
      "& '" ^ (extern_atom org) ^" "^  string_of_mut mut ^ " " ^ (name_rust_decl ""  t) ^ name_optid id
  | Tbox(t, a) ->
      "Box<" ^ (name_rust_decl ""  t) ^ ">" ^ name_optid id
  | Tfunction( _, _, args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "void")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl "" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      name_rust_decl (Buffer.contents b) res
  | Tstruct(orgs, name, a) ->
      "struct" ^ print_origins orgs ^ " " ^ extern_atom name ^ attributes a ^ name_optid id
  | Tvariant(orgs, name, a) ->
      "variant" ^ print_origins orgs ^ " " ^ extern_atom name ^ attributes a ^ name_optid id

(* Type *)

let name_rust_type ty = name_rust_decl "" ty

(* TODO: print expressions and statements *)

let name_function_parameters name_param fun_name params cconv =
    let b = Buffer.create 20 in
    Buffer.add_string b fun_name;
    Buffer.add_char b '(';
    begin match params with
    | [] ->
        Buffer.add_string b (if cconv.cc_vararg <> None then "..." else "")
    | _ ->
        let rec add_params first = function
        | [] ->
            if cconv.cc_vararg <> None then Buffer.add_string b ",..."
        | (id, ty) :: rem ->
            if not first then Buffer.add_string b ", ";
            Buffer.add_string b ((name_param id)^": "^(name_rust_decl "" ty));
            add_params false rem in
        add_params true params
    end;
    Buffer.add_char b ')';
    Buffer.contents b

let print_fundecl p id fd =
  match fd with
  | Ctypes.Internal f ->
      let linkage = if C2C.atom_is_static id then "static" else "extern" in
      fprintf p "%s %s;@ @ " linkage
                (name_rust_decl (extern_atom id) (Rustsyntax.type_of_function f))
  | _ -> ()

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  match v.gvar_init with
  | [] ->
      fprintf p "extern %s;@ @ "
              (name_rust_decl name2 v.gvar_info)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_rust_decl name2 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_rust_decl name2 v.gvar_info);
      begin match v.gvar_info, v.gvar_init with
      | (Rusttypes.Tint _ | Rusttypes.Tlong _ | Rusttypes.Tfloat _ | Tfunction _),
        [i1] ->
          print_init p i1
      | _, il ->
          if Str.string_match re_string_literal (extern_atom id) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) il
          then fprintf p "\"%s\"" (string_of_init (chop_last_nul il))
          else print_composite_init p il
      end;
      fprintf p ";@]@ @ "

let print_globvardecl p id v =
  let name = extern_atom id in
  let name = if v.gvar_readonly then "const "^name else name in
  let linkage = if C2C.atom_is_static id then "static" else "extern" in
  fprintf p "%s %s;@ @ " linkage (name_rust_decl name v.gvar_info)

let print_globdecl p (id,gd) =
  match gd with
  | Gfun f -> print_fundecl p id f
  | Gvar v -> print_globvardecl p id v

(* TODO *)
(* let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v *)

let struct_or_variant = function Struct -> "struct" | TaggedUnion -> "variant"

let declare_composite p (Composite(id, su, m, a, _, _)) =
  fprintf p "%s %s;@ " (struct_or_variant su) (extern_atom id)

let print_member p = function
  | Member_plain(id, ty) ->
      fprintf p "@ %s;" (name_rust_decl (extern_atom id) ty)

let define_composite p (Composite(id, su, m, a, _, _)) =
  fprintf p "@[<v 2>%s %s%s {"
          (struct_or_variant su) (extern_atom id) (attributes a);
  List.iter (print_member p) m;
  fprintf p "@;<0 -2>};@]@ @ "