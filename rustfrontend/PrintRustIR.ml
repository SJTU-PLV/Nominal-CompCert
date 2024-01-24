open Printf
open Camlcoq
(* open PrintAST *)
(* open Rusttypes *)
open Ctypes
open Cop
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
    fprintf p "storagelive %s" (extern_atom id)
  | Sstoragedead id ->
    fprintf p "storagedead %s" (extern_atom id)
  | Sdrop v ->
    fprintf p "drop(%a of %s)" print_place v (name_rust_type (RustlightBase.typeof_place v))
    
    
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
      print_stmt pp stmt
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

let print_function pp id f =
  fprintf pp "%s@ "
            (name_rust_decl (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv) f.fn_return);
  fprintf pp "@[<v 2>{@ ";
  print_stmt pp f.fn_body;
  fprintf pp "@;<0 -2>}@]@ @ "


let print_cfg pp id f =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    fprintf pp "%s(%a) {\n" (extern_atom id) print_params f.fn_params;
    let instrs =
      List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements cfg)) in
    PrintRTL.print_succ pp entry
      (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
    List.iter (print_instruction pp f.fn_body) instrs;
    fprintf pp "}\n\n"
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG"
 