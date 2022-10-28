(* *******************  *)
(* Author: Jinhua Wu  *)
(* Date:   Apr 6, 2022 *)
(* *******************  *)

(* Generate the string assciated with a int64 literal symbol *)

open Camlcoq
open BinNums

let litNum = ref 0

let int64lit_tbl = (Hashtbl.create 10 : (positive, bool) Hashtbl.t)
                   
let create_int64_literal_ident () : positive =
  incr litNum;
  let name = Printf.sprintf "__int64lit_%d" (!litNum) in
  let id = intern_string name in
    Hashtbl.add int64lit_tbl id true;
  id

let is_def_int64_literal (id: positive) : bool =
  try
    Hashtbl.find int64lit_tbl id
  with Not_found -> false
