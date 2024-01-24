(* open Printf *)
open Camlcoq
(* open Values *)
open AST
open! Rusttypes
(* open Cop *)
(* open Rustsyntax *)
open PrintCsyntax


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
  | Tbox(t, a) ->
      "Box<" ^ (name_rust_decl ""  t) ^ ">"
  | Tfunction(args, res, cconv) ->
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
  | Tstruct(name, a) ->
      "struct " ^ extern_atom name ^ attributes a ^ name_optid id
  | Tvariant(name, a) ->
      "variant " ^ extern_atom name ^ attributes a ^ name_optid id

(* Type *)

let name_rust_type ty = name_rust_decl "" ty

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
            Buffer.add_string b ((name_param id)^(name_rust_decl "" ty));
            add_params false rem in
        add_params true params
    end;
    Buffer.add_char b ')';
    Buffer.contents b