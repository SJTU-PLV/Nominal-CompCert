Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Local Open Scope error_monad_scope.

(** Some 64 bit instructions with imm64 are pseudo, generate global variable for the imm64 *)

Definition transf_instr (i:instruction) :  instruction* option (ident * (globdef fundef unit)) :=
  match i with
  | Pmovq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Pmovq_rm r a, Some (id, def))
  | Paddq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Paddq_rm r a, Some (id, def))
  | Psubq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Psubq_rm r a, Some (id, def))
  | Pimulq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Pimulq_rm r a, Some (id, def))
  | Pandq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Pandq_rm r a, Some (id, def))
  | Porq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Porq_rm r a, Some (id, def))
  | Pxorq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Pxorq_rm r a, Some (id, def))
  | Pcmpq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Pcmpq_rm r a, Some (id, def))
  | Ptestq_ri r imm64 =>
    let id := create_int64_literal_ident tt in
    let var := mkglobvar tt [Init_int64 imm64] true false in
    let def := Gvar var in
    let a := Addrmode None None (inr (id, Ptrofs.zero)) in
    (Ptestq_rm r a, Some (id, def))
  | _ => (i,None)
  end.

Definition acc_instr (acc: code * list (ident * (globdef fundef unit))) (i: instruction) :=
  let (c, id_defs) := acc in
  let (i', o_id_def) := transf_instr i in
  match o_id_def with
  | Some id_def =>
    (c++[i'], id_defs ++ [id_def])
  | None =>
    (c++[i'], id_defs)
  end.

Definition transf_code (c:code) :=
  fold_left acc_instr c ([],[]).

Definition transf_def (iddef: ident * (AST.globdef Asm.fundef unit))
  : list (ident * (AST.globdef Asm.fundef unit)) :=
  match iddef with
  | (id, (Gvar v)) => [(id, (Gvar v))]
  | (id, (Gfun (External ef))) => [(id, (Gfun (External ef)))]
  | (id, (Gfun (Internal f))) =>
    let c := fn_code f in
    let (c', int64_defs) :=  transf_code c in 
    let f' := mkfunction (fn_sig f) c' (fn_stacksize f) (fn_ofs_link f)in
    [(id, (Gfun (Internal f')))] ++ int64_defs
  end.

Definition gen_long_int_literal iddefs :=
  concat (map transf_def iddefs).

Definition transf_program (p: Asm.program) :=
  let defs:= gen_long_int_literal (prog_defs p) in
  {| prog_defs := defs;
     prog_public := AST.prog_public p;
     prog_main := AST.prog_main p |}.


           
