Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition transf_instr i : (list instruction) * option (ident * globdef fundef unit) :=
  match i with
  | Ploadli rd n =>
      let id := create_int64_literal_ident tt in
      let var := mkglobvar tt [Init_int64 n] true false in
      let def := Gvar var in
      (* follow Asm.v Ploadli >> lui ++ ld *)
      (*  lui x31, %hi(lbl)
        ld rd, %lo(lbl  )(x31)  *)
      ([Ploadsymbol_high X31 id (Ptrofs.zero); Pld rd X31 (Ofslow id (Ptrofs.zero))], Some (id,def))
  | Ploadfi rd f =>
      let id := create_float_literal_ident tt in
      let var := mkglobvar tt [Init_float64 f] true false in
      let def := Gvar var in
      ([Ploadsymbol_high X31 id (Ptrofs.zero); Pfld rd X31 (Ofslow id (Ptrofs.zero))], Some (id,def))
  | Ploadsi rd f =>
      let id := create_float_literal_ident tt in
      let var := mkglobvar tt [Init_float32 f] true false in
      let def := Gvar var in
      ([Ploadsymbol_high X31 id (Ptrofs.zero); Pfls rd X31 (Ofslow id (Ptrofs.zero))], Some (id,def))
  | Ploadsymbol rd id ofs =>
      (* not consider :  Archi.pic_code *)
      (* I think it is necessary to check the 20-bit bounds for ofs when generating reocation entry for Ploadsymbol_high *)
      (* HACKING!!!! Since addi use an int value, we can not place a symbol in addi instruction. I use Ploadsymbol to represent the addi here, which is transformed to addi in relocation table generation *)
      (* We expand Ploadsymbol here because the id_eliminate in assembler is one to one *)
      (* A more flexible choice is to define a new instruction *)
      ([Ploadsymbol_high rd id ofs; Ploadsymbol rd id ofs], None)
  | _ =>
      ([],None)
  end.

Definition acc_instr (acc: code * list (ident * (globdef fundef unit))) (i: instruction) :=
  let (c, id_defs) := acc in
  let (i', o_id_def) := transf_instr i in
  match o_id_def with
  | Some id_def =>
    (c++i', id_defs ++ [id_def])
  | None =>
    (c++i', id_defs)
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
    let (c', defs) :=  transf_code c in 
    let f' := mkfunction (fn_sig f) c' (fn_stacksize f) in
    [(id, (Gfun (Internal f')))] ++ defs
  end.

Definition gen_literal iddefs :=
  concat (map transf_def iddefs).

Definition transf_program (p: Asm.program) :=
  let defs:= gen_literal (prog_defs p) in
  {| prog_defs := defs;
     prog_public := AST.prog_public p;
     prog_main := AST.prog_main p |}.

