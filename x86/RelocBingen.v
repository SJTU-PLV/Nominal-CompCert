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

Section WITH_RELOC_OFS_MAP.
  Variable rtbl_ofs_map : ZTree.t relocentry.
  
Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

Definition concat_byte (acc: res (list byte)) i :=
  do code <- acc;
  do c <- EncDecRet.encode_Instruction i;
  OK (code ++ c).

Definition encode_instruction (ofs: Z) (i: instruction) :res (list byte) :=
  do c1 <- translate_instr rtbl_ofs_map ofs i;
  do c <- fold_left concat_byte c1 (OK []);
  OK c.

(* use generated encoder*)
Definition acc_instrs r i := 
  do r' <- r;
  let '(ofs, code) := r' in
  do c <- encode_instruction ofs i;
  (** check instr_size eqaul to encoded instuction size *)
  if Z.eqb (Z.of_nat (length c)) (instr_size i) then
    OK (ofs + instr_size i, code ++ c)
  else
    Error [MSG "Inconsistent instruction size for: ";
          MSG (instr_to_string i)].

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) : res (list byte) :=
  do r <- fold_left acc_instrs c (OK (0, []));
  let '(_, c') := r in
  OK c'.                                                           

End INSTR_SIZE.

(** ** Encoding of data *)

Definition transl_init_data (dofs:Z) (d:init_data) : res (list byte) :=
  match d with
  | Init_int8 i => OK [Byte.repr (Int.unsigned i)]
  | Init_int16 i => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f => OK (encode_int 4 (Int.unsigned (Float32.to_bits f)))
  | Init_float64 f => OK (encode_int 8 (Int64.unsigned (Float.to_bits f)))
  | Init_space n => OK (zero_bytes (Z.to_nat n))
  | Init_addrof id ofs => 
    (* do addend <- get_reloc_addend rtbl_ofs_map dofs; *)
    match ZTree.get dofs rtbl_ofs_map with
    | Some e =>
      if (Pos.eqb (reloc_symb e) id) && (Z.eqb (reloc_addend e) (Ptrofs.unsigned ofs)) then
        if Archi.ptr64 then     
          OK (encode_int64 (Ptrofs.unsigned ofs)) 
        else
          OK (encode_int32 (Ptrofs.unsigned ofs))
      else Error (msg "Init_addrof is inconsistent with relocentry")
    | None => Error (msg "No relocentry in Init_addrof")
    end
  end.

Definition acc_init_data r d := 
  do r' <- r;
  let '(ofs, rbytes) := r' in
  do dbytes <- transl_init_data ofs d;
  OK (ofs + init_data_size d, rev dbytes ++ rbytes).

Definition transl_init_data_list (l: list init_data) : res (list byte) :=
  do r <- fold_left acc_init_data l (OK (0, []));
  let '(_,bytes) := r in
  OK (rev bytes).

End WITH_RELOC_OFS_MAP.


Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

(** ** Translation of a program *)
Definition transl_section (sec : section) (reloctbl: reloctable) : res section :=
  match sec with
  | sec_text code =>
    do codebytes <- transl_code (gen_reloc_ofs_map reloctbl) instr_size code;
    OK (sec_bytes codebytes)
  | sec_data dl =>
    do databytes <- transl_init_data_list (gen_reloc_ofs_map reloctbl) dl;
    OK (sec_bytes databytes)
  (* | sec_rodata rdl => *)
  (*   do rodatabytes <- transl_init_data_list (gen_reloc_ofs_map reloctbl) rdl; *)
  (*   OK (sec_bytes rodatabytes) *)
  | _ => Error (msg "There are bytes before binary generation")
  end.


Definition acc_fold_section (reloc_map : reloctable_map) (res_sectbl: res sectable) (id: ident) (sec: section) :=
  do sectbl <- res_sectbl;
  let reloc_tbl := 
      match reloc_map ! id with
      | Some t => t
      | None => []
      end in
  do sec' <- transl_section sec reloc_tbl;
  OK (PTree.set id sec' sectbl).
        
Definition transl_sectable (stbl: sectable) (relocmap: reloctable_map) :=
  PTree.fold (acc_fold_section relocmap) stbl (OK (PTree.empty section)).


Definition transf_program (p:program) : res program := 
  do stbl <- transl_sectable (prog_sectable p) (prog_reloctables p);
  do szstrings <- fold_right
                    (fun (id : ident) (acc : res Z) =>
                       match acc with
                       | OK z =>
                         match SymbolString.find_symbol_pos id with
                         | Some pos => OK (z + 2 + Z.of_nat (length pos))
                         | None => Error (msg "cannot find string")
                         end
                       | Error _ => acc
                       end) (OK 0) (map fst (PTree.elements (prog_symbtable p)));
  if zlt szstrings Int.max_unsigned
  then 
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := stbl;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p;
     |}
  else Error (msg "Too many strings in symbtable").

End INSTR_SIZE.
