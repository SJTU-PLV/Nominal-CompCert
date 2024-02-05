open Format
open Camlcoq
(* open PrintAST *)
open Rusttypes
(* open Ctypes *)
open RustIR
(* open PrintCsyntax *)
open PrintRustsyntax
open PrintRustlight
open Maps

let rec print_stmt p (s: RustIR.statement) =
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
    fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
  | Scall(v, e1, el) ->
    fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
              print_place v
              expr (15, e1)
              print_expr_list (true, el)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
    fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
    fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s1) ->
    fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sbreak ->
    fprintf p "break;"
  | Scontinue ->
    fprintf p "continue;"
  | Sreturn None ->
    fprintf p "return;"
  | Sreturn (Some e) ->
    fprintf p "return %a;" print_expr e
  | Sbox(v, e) ->
    fprintf p "@[<hv 2>%a =@ Box::new(%a);@]" print_place v   print_expr e
  | Sstoragelive id ->
    fprintf p "storagelive %s;" (extern_atom id)
  | Sstoragedead id ->
    fprintf p "storagedead %s;" (extern_atom id)
  | Sdrop v ->
    fprintf p "drop(%a of %s);" print_place v (name_rust_type (RustlightBase.typeof_place v))
    

(* Print cfg of RustIR *)

let print_instruction pp prog (pc, i) =
  fprintf pp "%5d:\t" pc;
  match i with
  | Inop s ->
    let s = P.to_int s in
    if s = pc - 1
    then fprintf pp "nop\n"
    else fprintf pp "goto %d\n" s
  | Isel(sel, s) ->
    (match select_stmt prog sel with
    | Some stmt ->
      print_stmt pp stmt;
      fprintf pp "\n"
    | None ->
      fprintf pp "Error: cannot find statement\n")
  | Icond(e, s1, s2) ->
    fprintf pp "if (%a) goto %d else goto %d\n"
        PrintRustlight.print_expr e
        (P.to_int s1) (P.to_int s2)
  | Iend ->
    fprintf pp "return\n"

let print_param pp param =
  let (id,ty) = param in
  fprintf pp "%s: %s" (extern_atom id) (name_rust_type ty)

  let rec print_params pp = function
  | [] -> ()
  | [r] -> print_param pp r
  | r1::rl -> fprintf pp "%a, %a" print_param r1 print_params rl

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let print_function pp id f =
  fprintf pp "%s@ "
            (name_rust_decl (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv) f.fn_return);
  fprintf pp "@[<v 2>{@ ";
  print_stmt pp f.fn_body;
  fprintf pp "@;<0 -2>}@]@ @ "

let print_cfg_body pp (body, entry, cfg) = 
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg)) in
  print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction pp body) instrs;
  fprintf pp "}\n\n"

let print_cfg pp id f =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    fprintf pp "%s(%a) {\n" (extern_atom id) print_params f.fn_params;
    print_cfg_body pp (f.fn_body, entry, cfg)
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG"
 
(* Print program *)


let print_fundef p id fd =
  match fd with
  | Rusttypes.External(_, _, _, _) ->
      ()
  | Internal f ->
      print_function p id f

let print_fundecl p id fd =
  match fd with
  | External((AST.EF_external _ | AST.EF_runtime _ | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ "
                (name_rust_decl (extern_atom id) (Tfunction(args, res, cconv)))
  | External(_, _, _, _) ->
      ()
  | Internal f ->
      fprintf p "%s;@ "
                (name_rust_decl (extern_atom id) (RustIR.type_of_function f))

let print_globdef p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundef p id f
  | AST.Gvar v -> PrintRustsyntax.print_globvar p id v  (* from PrintRustsyntax.ml *)

let print_globdecl p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundecl p id f
  | AST.Gvar v -> ()

let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (PrintRustsyntax.declare_composite p) prog.prog_types;
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.prog_defs;
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc