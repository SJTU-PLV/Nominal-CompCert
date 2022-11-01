Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Definition labelofstoInitdata (fid: ident) (ofs: Z) : init_data :=
  Init_addrof fid (Ptrofs.repr ofs).

Section INSTRSIZE.
  Variable instr_size : instruction -> Z.

Section FID.
  Variable fid: ident.          (* the function processing *)
  
Definition transf_instr (i: instruction) (ofs:Z) : (list instruction * option (ident * globdef fundef unit)) :=
  let sz := instr_size i in
  match i with
  | Pbtbl_ofs r ofsLst =>
    let id := create_jump_table_ident tt in
    (* absolute address *)
    let initdataLst := map (labelofstoInitdata fid) ofsLst in
    let def := mkglobvar tt initdataLst true false in
    (* consider init_data size
       >> sll x5, r, (2 or 3)
          la X31, id  # Plui_s X31 id 0;Paddi X31 X31 id 0
          add x5, x31, x5 # get the address of the offset of the label
          ld x5, 0(x5)
          jr x5
     *)
    let i1 := if Archi.ptr64 then Psllil X5 r (Int.repr 3) else Pslliw X5 r (Int.repr 2) in
    let loadid := [Plui_s X31 id 0; Paddi_s X31 X31 id 0] in
    let lbladdr := if Archi.ptr64 then Paddl X5 X31 X5 else Paddw X5 X31 X5 in
    let loadaddr := Pld X5 X5 (Ofsimm Ptrofs.zero) in
    let jump := Pjal_rr X0 X5 0 in
    ([i1]++loadid++[lbladdr;loadaddr;jump], Some (id, Gvar def))
  | _ => ([i], None)
  end.

Definition acc_instr (acc: Z * code * list (ident * (globdef fundef unit))) (i: instruction) :=
  let '(ofs, c, id_defs) := acc in
  let (i', o_id_def) := transf_instr i ofs in
  let sz := code_size instr_size i' in
  match o_id_def with
  | Some id_def =>
    (ofs+sz, c++i', id_defs ++ [id_def])
  | None =>
    (ofs+sz,c++i', id_defs)
  end.

Definition transf_code (c:code) :=
  let '(_, code, iddefs) := fold_left acc_instr c (0, [],[]) in
  (code, iddefs).

Definition transf_function (f:function)  : (function * list (ident*globdef fundef unit)) :=
  let code := fn_code f in
  let rs := transf_code code in
  let (code', iddefs) := rs in
  let f' := mkfunction (fn_sig f) code' (fn_stacksize f) in
  (f', iddefs).

Definition transf_fundef (fd: fundef) : (fundef * list (ident*globdef fundef unit)) :=
  match fd with
  | Internal f =>
    let (f', iddefs) := transf_function f in
    (Internal f', iddefs)
  | _ => (fd, [])
  end.

End FID.

Definition transf_globdef (acc: list (ident*globdef fundef unit) * list (ident*globdef fundef unit)) (id_def: ident * globdef fundef unit) :=
  let (id, def) := id_def in
  match def with
  | Gfun fd =>
    let (fd', iddefs) := transf_fundef id fd in
    ((fst acc) ++ [(id, Gfun fd')], (snd acc) ++ iddefs)
  | _ => ((fst acc) ++ [id_def], snd acc)
  end.

Definition transf_program (p:Asm.program) : program :=
  {| prog_defs := let (defs, jmptbls) := fold_left transf_globdef (prog_defs p) ([],[]) in
                  defs ++ jmptbls;
     prog_public := prog_public p;
     prog_main := prog_main p
  |}.
                            
End INSTRSIZE.


