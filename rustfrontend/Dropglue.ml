open Camlcoq
open BinNums

let litNum = ref 0

let dropglue_tbl = (Hashtbl.create 10 : (positive, bool) Hashtbl.t)
                   
let create_dropglue_ident (a: positive) : positive =
  (* TODO: use the name of a in the end of drop in place *)
  incr litNum;
  (* let str = extern_atom a in *)
  let name = Printf.sprintf "__drop_in_place_%d" (!litNum) in
  let id = intern_string name in
    Hashtbl.add dropglue_tbl id true;
  id

let is_dropglue_ident (id: positive) : bool =
  try
    Hashtbl.find dropglue_tbl id
  with Not_found -> false