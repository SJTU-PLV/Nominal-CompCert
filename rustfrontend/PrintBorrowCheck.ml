open Format
open Camlcoq
(* open PrintAST *)
open Rusttypes
(* open Ctypes *)
open RustIR
(* open PrintCsyntax *)
open PrintRustlight
open Maps
open BorrowCheckPolonius
open BorrowCheckDomain
open Driveraux

let print_mutkind pp (mut: mutkind) =
  match mut with
  | Mutable -> fprintf pp "mut"
  | Immutable -> fprintf pp "immut"

let print_loan pp (l: loan) =
  match l with
  | Lextern(org) ->
    fprintf pp "Lextern(%s)" (extern_atom org)
  | Lintern(mut, p) ->
    fprintf pp "(%a, %a)" print_mutkind mut print_place p

let print_loanset pp (ls: LoanSet.t) =
  let l = LoanSet.elements ls in
  pp_print_list ~pp_sep: (fun out () -> fprintf out ";@ ") print_loan pp l

let print_origin pp org =
  fprintf pp "%s" (extern_atom org)

let print_originset pp (ls: OriginSet.t) =
  let l = OriginSet.elements ls in
  pp_print_list ~pp_sep: (fun out () -> fprintf out ";@ ") print_origin pp l

let print_dead_origin pp (org: origin) =
  fprintf pp "%s: Dead@ " (extern_atom org)

let print_origin_state pp (org_st: origin * LOrgSt.t) =
  let (org, st) = org_st in
  match st with
  | Obot -> fprintf pp "%s: Bot@ " (extern_atom org)
  | Live(ls) ->
    fprintf pp "%s: {@[<hov>%a@]}@ " (extern_atom org) print_loanset ls
  | Dead ->
    print_dead_origin pp org

let print_origin_env pp (e: LOrgEnv.t) =
  fprintf pp "OrgEnv: ";
  let l = (PTree.elements e) in
  List.iter (print_origin_state pp) l

let print_live_loans pp (ls: LoanSet.t) =
  fprintf pp "May-Live Loans: {@[<hov>%a@]}@ " print_loanset ls

let print_alias_graph pp (ag: LAliasGraph.t) =
  let l = PTree.elements ag in
  match l with
  | [] -> fprintf pp "Alias Graph is empty "
  | _ ->
    fprintf pp "Alias Graph: ";
    List.iter
        (fun (org, ls) -> fprintf pp "%s: {@[<hov>%a@]}@ " (extern_atom org) print_originset ls) l

let print_ae pp ae =
  match ae with
  | AE.Err(pc', msg) ->
    fprintf pp "Error found in %d: %a@.@." (P.to_int pc') print_error msg
  | AE.Bot ->
    fprintf pp "Unreachable point@.@."
  | AE.State(live_loans, org_env, alias_graph) ->
    (* TODO: print alias graph *)
    fprintf pp "%a@ %a@ %a@.@." print_live_loans live_loans print_origin_env org_env print_alias_graph alias_graph

let print_instruction_debug pp prog (pc, (i, ae)) =
  PrintRustIR.print_instruction pp prog (pc,i);
  print_ae pp ae

let print_cfg_body_borrow_check pp (body, entry, cfg) ae =
  let cfg' = PTree.combine PrintRustIR.combine cfg ae in
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg')) in
  PrintRustIR.print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
    List.iter (print_instruction_debug pp body) instrs;
    fprintf pp "}\n\n"

let print_cfg_borrow_check ce pp id f  =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    (match borrow_check ce f with
    | Errors.OK ae ->
      fprintf pp "%s(%a) {\n" (extern_atom id) PrintRustIR.print_params f.fn_params;
      (* Print variables and their types *)
      List.iter
      (fun (id, ty) ->
        fprintf pp "%s;@ " (PrintRustsyntax.name_rust_decl (extern_atom id) ty)) f.fn_vars;
      print_cfg_body_borrow_check pp (f.fn_body, entry, cfg) ae
    | Errors.Error msg ->
      Diagnostics.fatal_error Diagnostics.no_loc "Error in borrow check: %a@ " Driveraux.print_error msg)
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG (borrow check): %a@ " Driveraux.print_error msg

let print_cfg_program_borrow_check p (prog: RustIR.coq_function Rusttypes.program) =
  fprintf p "@[<v 0>";
  List.iter (PrintRustsyntax.declare_composite p) prog.prog_types;
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (PrintRustIR.print_globdecl p) prog.prog_defs;
  List.iter (PrintRustIR.print_globdef p (print_cfg_borrow_check prog.prog_comp_env)) prog.prog_defs;
  fprintf p "@]@."