Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProg RelocProgramBytes.
Require Import encode.Hex encode.Bits Memdata encode.Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
Require Import TranslateInstr BPProperty.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Fixpoint translate_bytes instrs :=
  match instrs with
  | [] => OK []
  | i :: instrs' =>
      do bits <- EncDecRet.encode_Instruction i;
      (* bits_to_bytes, in addition with a revertion in riscV *)
      do bs <- bits_to_bytes_archi bits;
      do tl <- translate_bytes instrs';
      OK (bs ++ tl)
  end.

Fixpoint translate_instrs instrs :=
  match instrs with
  | [] => OK []
  | i :: instrs' =>
      do bs <- translate_instr i;
      do tl <- translate_instrs instrs';      
      OK (bs ++ tl)
  end.

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) : res (list byte) :=
  do l1 <- translate_instrs c;
  translate_bytes l1.
  

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
      OK (repeat (Byte.repr 0) (Z.to_nat n))
  | Init_addrof id ofs, Some e => 
    (* do addend <- get_reloc_addend rtbl_ofs_map dofs; *)

    if (Pos.eqb (reloc_symb e) id) then
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
    else if ofs + (init_data_size d) <=? e.(reloc_offset) then
      do dbytes <- transl_init_data None d;
      OK (rbytes ++ dbytes, ofs', reloctbl)
    else Error (msg "ofs greater than reloc_offset: skipping someone? ")
  end.

Definition transl_init_data_list (reloctbl: reloctable) (l: list init_data) : res (list byte) :=
  do r <- fold_left acc_init_data l (OK ([],0,reloctbl));
  OK (fst (fst r)).
  (* let '(_,bytes) := r in *)
  (* OK (rev bytes). *)


(** ** Translation of a program *)
Definition transl_section (sec : RelocProgram.section) (reloctbl: reloctable) : res section :=
  match sec with
  | sec_text code =>
    do codebytes <- transl_code code;
    OK (sec_text codebytes)
  | sec_rwdata dl =>
    do databytes <- transl_init_data_list reloctbl dl;
    OK (sec_rwdata databytes)
  | sec_rodata dl =>
    do databytes <- transl_init_data_list reloctbl dl;
    OK (sec_rodata databytes)
  end.



Definition acc_fold_section (reloc_map : reloctable_map) (id: ident) (sec: RelocProgram.section) :=
  (* do sectbl <- res_sectbl; *)
  let reloc_tbl := 
      match reloc_map ! id with
      | Some t => t
      | None => []
      end in
    do sec' <- transl_section sec reloc_tbl;
    OK sec'.
        
Definition transl_sectable (stbl: RelocProgram.sectable) (relocmap: reloctable_map) (symbtbl: symbtable) :=
  PTree.fold (acc_PTree_fold (acc_fold_section relocmap)) stbl (OK (PTree.empty section)).


Definition transf_program (p:RelocProgram.program) : res program := 
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

