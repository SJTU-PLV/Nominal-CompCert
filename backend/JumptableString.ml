(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 04, 2020 *)
(* *******************  *)

(* Generate the string assciated with a jump table symbol *)

open Camlcoq
open BinNums

let jmptbl_id = ref 0
(* let label_id = ref 0 *)
let jmptbl_strmap = (Hashtbl.create 10 : (positive, bool) Hashtbl.t)

let is_def_jumptbl (id: positive) : bool =
  try
    Hashtbl.find jmptbl_strmap id
  with Not_found -> false

let create_jump_table_ident () : positive =
  incr jmptbl_id;
  (* label_id := 0; *)
  let name = Printf.sprintf "__jumptable_%d" (!jmptbl_id) in
  let id = intern_string name in
  Hashtbl.add jmptbl_strmap id true;
  id
(* 
let create_label_ident() : positive =
  incr label_id;
  let name = Printf.sprintf "__jmptbl%d_label_%d" (!jmptbl_id) (!label_id) in
  let id = intern_string name in
  id *)

