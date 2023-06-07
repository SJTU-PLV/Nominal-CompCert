Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
(* Require Import RelocProgram. *)
Require Import Globalenvs.
Require Import SymbolString.
Require Import LocalLib.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Definition labelofstoInitdata (fid: ident) (ofs: Z) : init_data :=
  Init_addrof fid (Ptrofs.repr ofs).


Section INSTRSIZE.
  Variable instr_size : instruction -> Z.

Section FID.
  Variable fid: ident.          (* the function processing *)
  
Definition transl_instr (i: instruction) (ofs:Z) :
  (* res (instruction * option (ident * list init_data * list symbentry)) *)
  (instruction * option (ident * globdef fundef unit))
  :=
  let sz := instr_size i in
  match i with
  | Pjmptbl_rel r ofsLst =>
    let id := create_jump_table_ident tt in
    let addrLst := map (Zplus ((sz + ofs))) ofsLst in
    (* absolute address *)
    let initdataLst := map (labelofstoInitdata fid) addrLst in
    let def := mkglobvar tt initdataLst true false in
    let disp := (id, Ptrofs.repr(0)) in
    (* unnecessary to distinguish ptr64 *)
    let lblMem := if Archi.ptr64 then  (Addrmode None (Some(r,8)) (inr disp)) else (Addrmode None (Some(r,4)) (inr disp)) in
    let i' := Pjmp_m lblMem in
    (i', Some (id, Gvar def))
  | _ => (i, None)
  end.

Definition acc_instrs (* (r: res(Z * list instruction * list init_data * list symbentry)) *)
           (r : Z * list instruction * list (ident * globdef fundef unit)) (i:instruction) :=
  let '(acc_ofs, acc_code, acc_defs) := r in
  let (i', res) :=  transl_instr i acc_ofs in
  let code' := acc_code ++ [i'] in
  let ofs' := acc_ofs + instr_size i in
  match res with
  | Some iddef =>
    (ofs', code', acc_defs ++ [iddef])
  | None =>
    (ofs',code',acc_defs)
  end.
  (* do rs <- r; *)
  (* let '(acc_ofs, acc_code, acc_jmp_data, acc_jmp_symbl) := rs in *)
  (* do (i', res) <- transl_instr i acc_ofs; *)
  (* let code' := acc_code ++ [i'] in *)
  (* let ofs' := acc_ofs + instr_size i in *)
  (* match res with *)
  (* | Some jmp_tbl => *)
  (*   let '(tbl_id, tbl_data, lbl_symbl) := jmp_tbl in *)
  (*   let tbl_e := *)
  (*       {|symbentry_id := tbl_id; *)
  (*         symbentry_bind := bind_local; *)
  (*         symbentry_type := symb_data; *)
  (*         symbentry_value := init_data_list_size rodata + *)
  (*                            init_data_list_size acc_jmp_data; *)
  (*         symbentry_secindex := secindex_normal sec_rodata_id; *)
  (*         symbentry_size := init_data_list_size tbl_data; *)
  (*       |} in *)
  (*   let jmp_data' := acc_jmp_data ++ tbl_data in *)
  (*   let jmp_symbl' := acc_jmp_symbl ++ [tbl_e] ++ lbl_symbl in *)
  (*   OK (ofs', code', jmp_data', jmp_symbl') *)
  (* | None => *)
  (*   OK (ofs', code', acc_jmp_data, acc_jmp_symbl) *)
  (* end. *)

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) :code * list (ident *  globdef fundef unit) (* list init_data * list symbentry) *) :=
  let r := fold_left acc_instrs c (0,[],[]) in
  let '(_, code, iddefs) := r in
  (code, iddefs).

Definition transf_function (f:function)  : (function * list (ident*globdef fundef unit)) :=
  let code := fn_code f in
  let rs := transl_code code in
  let '(code', iddefs) := rs in
  let f' := mkfunction (fn_sig f) code' (fn_stacksize f) (fn_ofs_link f) in
  (f', iddefs).

Definition transf_fundef (fd: fundef) : (fundef * list (ident*globdef fundef unit)) :=
  match fd with
  | Internal f =>
    let (f', iddefs) := transf_function f in
    (Internal f', iddefs)
  | _ => (fd, [])
  end.

End FID.

(* acc = (fst, snd) , fst is the mapping of original globdef, snd is the appending jumptables *)

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
(* Definition compute_pad_size initd := *)
(*   let sz := AST.init_data_list_size initd in *)
(*   (align sz alignw) - sz. *)
  
(** Generation of list of jump tables *)
(* Definition gen_jump_table (sctbl: sectable) (sytbl: symbtable) *)
(*   : res (sectable*symbtable) := *)
(*   match sctbl with *)
(*   | [sec_rodata rdl; sec_data dl; sec_text code] => *)
(*     (* translation of code to generate defs*) *)
(*     do r <- transl_code rdl code; *)
(*     let '(code', jmp_dl, jmp_syl) := r in *)
(*     (* pad jmpdl *) *)
(*     let psz := compute_pad_size jmp_dl in *)
(*     let jmp_dl_pad := *)
(*         if zlt 0 psz then *)
(*           jmp_dl ++ [Init_space psz] *)
(*         else *)
(*           jmp_dl in *)
(*     let rdl' := rdl ++ jmp_dl_pad in *)
(*     let sytbl' := sytbl ++ jmp_syl in *)
(*     OK ([sec_rodata rdl'; sec_data dl; sec_text code'], sytbl') *)
(*   | _ => Error (msg "Expected the section table to be [sec_rodata; sec_data; sec_text]") *)
(*   end. *)
  
(* Definition transf_program (p: program) : res program := *)
(*   do r <- gen_jump_table (prog_sectable p) (prog_symbtable p); *)
(*   let (sctabl, sytabl) := r in *)
(*   OK {| prog_defs := prog_defs p; *)
(*         prog_public := prog_public p; *)
(*         prog_main := prog_main p; *)
(*         prog_sectable := sctabl; *)
(*         prog_strtable := prog_strtable p; *)
(*         prog_symbtable := sytabl; *)
(*         prog_reloctables := prog_reloctables p; *)
(*         prog_senv := prog_senv p *)
(*      |}. *)
