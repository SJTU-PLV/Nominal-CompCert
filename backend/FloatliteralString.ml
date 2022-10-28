(* *******************  *)
(* Author: Zhenguo Yin  *)
(* Date:   Jul 27, 2020 *)
(* *******************  *)

(* Generate the string assciated with a float literal symbol *)

open Camlcoq
open BinNums

let litNum = ref 0

let fltlit_tbl = (Hashtbl.create 10 : (positive, bool) Hashtbl.t)
                   
let create_float_literal_ident () : positive =
  incr litNum;
  let name = Printf.sprintf "__floatlit_%d" (!litNum) in
  let id = intern_string name in
    Hashtbl.add fltlit_tbl id true;
  id

let is_def_float_literal (id: positive) : bool =
  try
    Hashtbl.find fltlit_tbl id
  with Not_found -> false

let create_float_mask_ident () : ((positive*positive)*(positive*positive)) =
  let negd_mask_s = "__negd_mask" in
  let negd_mask_id = intern_string negd_mask_s in
  Hashtbl.add fltlit_tbl negd_mask_id true;
  let negs_mask_s = "__negs_mask" in
  let negs_mask_id = intern_string negs_mask_s in
  Hashtbl.add fltlit_tbl negs_mask_id true;
  let absd_mask_s = "__absd_mask" in
  let absd_mask_id = intern_string absd_mask_s in
  Hashtbl.add fltlit_tbl absd_mask_id true;
  let abss_mask_s = "__abss_mask" in
  let abss_mask_id = intern_string abss_mask_s in
  Hashtbl.add fltlit_tbl abss_mask_id true;
  ((negd_mask_id,negs_mask_id),(absd_mask_id,abss_mask_id))
  
