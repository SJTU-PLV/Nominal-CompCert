(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 18, 2019 *)
(* Last updated: Feb 5, 2022 by Jinhua Wu*)
(* **********   *********  *)

Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProg RelocProgram.
Require Import encode.Hex encode.Bits Memdata encode.Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
Require Import TranslateInstr.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
  
Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

Definition concat_byte (acc: res (list byte)) i :=
  do code <- acc;
  do c <- EncDecRet.encode_Instruction i;
  OK (code ++ c).

(* Definition encode_instruction (e: option relocentry) (ofs: Z) (i: instruction) :res (list byte) := *)
(*   do c1 <- translate_instr e ofs i; *)
(*   do c <- fold_left concat_byte c1 (OK []); *)
(*   OK c. *)

(* use generated encoder*)
Definition acc_instrs r i := 
  do r' <- r;
  let '(code,ofs,reloctbl) := r' in
  match reloctbl with
  | [] =>
    do c1 <- translate_instr None i;
    do c2 <- fold_left concat_byte c1 (OK []);
    if Z.eqb (Z.of_nat (length c2)) (instr_size i) then
      OK (code ++ c2,ofs + instr_size i,[])
    else
      Error [MSG "Inconsistent instruction size for: ";
            MSG (instr_to_string i)]
  | e :: tl =>
    let ofs' := ofs + instr_size i in
    if Z.ltb ofs e.(reloc_offset) && Z.ltb e.(reloc_offset) ofs' then
      do c1 <- translate_instr (Some e) i;
      do c2 <- fold_left concat_byte c1 (OK []);
      if Z.eqb (Z.of_nat (length c2)) (instr_size i) then
        OK (code ++ c2,ofs + instr_size i,tl)
      else
        Error [MSG "Inconsistent instruction size for: ";
              MSG (instr_to_string i)]
    else
      do c1 <- translate_instr None i;
      do c2 <- fold_left concat_byte c1 (OK []);
      if Z.eqb (Z.of_nat (length c2)) (instr_size i) then
        OK (code ++ c2,ofs + instr_size i,reloctbl)
      else
        Error [MSG "Inconsistent instruction size for: ";
              MSG (instr_to_string i)]
  end.


(** Translation of a sequence of instructions in a function *)
Definition transl_code (reloctbl: reloctable) (c:code) : res (list byte) :=
  do r <- fold_left acc_instrs c (OK ([],0,reloctbl));
  OK (fst (fst r)).
  
End INSTR_SIZE.

(** ** Encoding of data *)

(* Retain the information for decoding: only provide relocentry for Init_addrof  *)
Definition transl_init_data (e: option relocentry) (d:init_data) : res (list byte) :=
  match d,e with
  | Init_int8 i, None => OK (encode_int 1 (Int.unsigned i))
  | Init_int16 i, None => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i, None => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i, None => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f, None => OK (encode_int 4 (Int.unsigned (Float32.to_bits f)))
  | Init_float64 f, None => OK (encode_int 8 (Int64.unsigned (Float.to_bits f)))
  | Init_space n, None =>
    if n <=? 0 then
      Error (msg "Init_space size is less than equal zero")
    else
      OK (concat (list_repeat (Z.to_nat n) (encode_int 1 (Int.unsigned Int.zero))))
  | Init_addrof id ofs, Some e => 
    (* do addend <- get_reloc_addend rtbl_ofs_map dofs; *)

    if (Pos.eqb (reloc_symb e) id) && (Z.eqb (reloc_addend e) (Ptrofs.unsigned ofs)) then
      if Archi.ptr64 then     
        OK (encode_int 8 (Ptrofs.unsigned ofs)) 
      else
        OK (encode_int 4 (Ptrofs.unsigned ofs))
    else Error (msg "Init_addrof is inconsistent with relocentry")
  | _,_ => Error (msg "mismatching for init_data and relocentry")
  end.

Definition acc_init_data r d := 
  do r' <- r;
  let '(rbytes,ofs,reloctbl) := r' in
  match reloctbl with
  | [] =>
    let ofs' := ofs + init_data_size d in
    do dbytes <- transl_init_data None d;
    OK (rbytes ++ dbytes, ofs', [])
  | e :: tl =>
    let ofs' := ofs + init_data_size d in
    if ofs =? e.(reloc_offset) then
      do dbytes <- transl_init_data (Some e) d;
      OK (rbytes ++ dbytes, ofs', tl)
    else if ofs + (init_data_size d) <? e.(reloc_offset) then
      do dbytes <- transl_init_data None d;
      OK (rbytes ++ dbytes, ofs', reloctbl)
    else Error (msg "ofs greater than reloc_offset: skipping someone? ")
  end.

Definition transl_init_data_list (reloctbl: reloctable) (l: list init_data) : res (list byte) :=
  do r <- fold_left acc_init_data l (OK ([],0,reloctbl));
  OK (fst (fst r)).
  (* let '(_,bytes) := r in *)
  (* OK (rev bytes). *)



Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

(** ** Translation of a program *)
Definition transl_section (sec : section) (reloctbl: reloctable) (symbe:symbentry) : res section :=
  match sec,(symbentry_type symbe) with
  | sec_text code, symb_func =>
    do codebytes <- transl_code instr_size reloctbl code;
    OK (sec_bytes codebytes)
  | sec_data dl, symb_rodata =>
    do databytes <- transl_init_data_list reloctbl dl;
    OK (sec_bytes databytes)
  | sec_data dl, symb_rwdata =>
    do databytes <- transl_init_data_list reloctbl dl;
    OK (sec_bytes databytes)
  (* | sec_rodata rdl => *)
  (*   do rodatabytes <- transl_init_data_list (gen_reloc_ofs_map reloctbl) rdl; *)
  (*   OK (sec_bytes rodatabytes) *)
  | _,_ => Error (msg "There are bytes before binary generation")
  end.



Definition acc_fold_section (symbtbl: symbtable) (reloc_map : reloctable_map) (id: ident) (sec: section) :=
  (* do sectbl <- res_sectbl; *)
  let reloc_tbl := 
      match reloc_map ! id with
      | Some t => t
      | None => []
      end in
  match symbtbl ! id with
  | Some e =>
    do sec' <- transl_section sec reloc_tbl e;
    OK sec'
    (* OK (PTree.set id sec' sectbl) *)
  | _ => Error (msg "no symbol entry for this section")
  end.
        
Definition transl_sectable (stbl: sectable) (relocmap: reloctable_map) (symbtbl: symbtable) :=
  PTree.fold (acc_PTree_fold (acc_fold_section symbtbl relocmap)) stbl (OK (PTree.empty section)).


Definition transf_program (p:program) : res program := 
  do stbl <- transl_sectable (prog_sectable p) (prog_reloctables p) (prog_symbtable p);
  (* do szstrings <- fold_right *)
  (*                   (fun (id : ident) (acc : res Z) => *)
  (*                      match acc with *)
  (*                      | OK z => *)
  (*                        match SymbolString.find_symbol_pos id with *)
  (*                        | Some pos => OK (z + 2 + Z.of_nat (length pos)) *)
  (*                        | None => Error (msg "cannot find string") *)
  (*                        end *)
  (*                      | Error _ => acc *)
  (*                      end) (OK 0) (map fst (PTree.elements (prog_symbtable p))); *)
  (* if zlt szstrings Int.max_unsigned *)
  (* then  *)
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := stbl;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p;
     |}.
  (* else Error (msg "Too many strings in symbtable"). *)

End INSTR_SIZE.
