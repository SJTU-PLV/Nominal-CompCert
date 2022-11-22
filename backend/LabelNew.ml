open Asm
open AST
open Camlcoq

(* Generation of fresh labels *)

let dummy_function = { fn_code = []; fn_sig = signature_main; fn_stacksize = Camlcoq.Z.of_uint 0}
let current_function = ref dummy_function
let next_label = ref (None: label option)

let new_label () =
  let lbl =
    match !next_label with
    | Some l -> l
    | None ->
        (* on-demand computation of the next available label *)
        List.fold_left
          (fun next instr ->
            match instr with
            | Plabel l -> if P.lt l next then next else P.succ l
            | _ -> next)
          P.one (!current_function).fn_code
  in
    next_label := Some (P.succ lbl);
    lbl

let set_current_function f =
  current_function := f; next_label := None; Errors.OK ()