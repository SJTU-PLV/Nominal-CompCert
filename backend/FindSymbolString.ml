(* Finding the string assciated with a symbol *)

open Printf
open Camlcoq
open Integers
open BinNums

let rec int_to_pos (i:int) : positive =
  if i = 1 then
    Coq_xH
  else if i > 1 then      
    let un = int_to_pos (i / 2) in
    let rm = i mod 2 in
    if rm = 0 then
      Coq_xO un
    else
      Coq_xI un
  else
    let s = sprintf "%i" i in
    raise (Invalid_argument s)

let int_to_Z (i:int) : coq_Z =
  if i = 0 then
    Z0
  else if i > 0 then
    Zpos (int_to_pos i)
  else
    Zneg (int_to_pos (-i))


let int_to_N (i:int) : coq_N =
  if i = 0 then
    N0
  else if i > 0 then      
    Npos (int_to_pos i)
  else
    let s = sprintf "%i" i in
    raise (Invalid_argument s)


let string_to_list (s:string) : char list =
  let l = ref [] in
  String.iter (fun c -> l := c::(!l)) s;
  List.rev !l

let find_symbol_pos a : positive list option =
  try 
    let s = (Hashtbl.find string_of_atom a) in
    (* Printf.printf "Found symbol %s\n" s; *)
    let pos = List.map (fun c -> int_to_pos (Char.code c)) (string_to_list s) in
    Some pos
  with
  | Not_found ->
     None

let string_to_ident (l: Byte.int list) : positive option =
  try
    let cl = List.map (fun b -> Char.chr (Z.to_int (Byte.unsigned b))) l in
    let s = String.init (List.length cl) (List.nth cl) in
    let i = Hashtbl.find atom_of_string s in
    Some i
  with
  | Not_found ->
    None

let coq_string_to_ident (l: char list) : positive option =
  try
    let s = camlstring_of_coqstring l in
    let i = Hashtbl.find  atom_of_string s in
    Some i
  with
  | Not_found ->
    None