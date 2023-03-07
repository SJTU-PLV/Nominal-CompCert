(** * Generation of the relocatable Elf file *)

Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Asm RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import RelocElf.
Require Import SymbolString.
(* Require Import ShstrtableEncode. *)
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode.
Require Import RelocElfArchi.
Import Hex Bits.
Import ListNotations.
(* Require Import RelocProgSemantics3. *)

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.

(* We create a simple ELF file with the following layout
   where every section is aligned at 4 bytes:

32bit mode:

   1. ELF Header                                       (52 bytes)
   2. Sections
      -- .data section for each Gvar (global variables)
      -- .text section for each Internal function (instructions)   
      -- .strtab section (string table)
      -- .symtab section (symbol table)                   
      -- .reladata section for each Gvar need relocation
      -- .relatext section for each Internal function need relocation
      -- .shstrtab section (section string table)
   3. Section headers
      -- Null header                      (40 bytes)
      -- header for each Gvar      (40 bytes)
      -- header for each Internal function  (40 bytes)
      -- header for .strtab
      -- header for .symbtab      (40 bytes)
      -- header for each Gvar need relocation
      -- header for each Internal function need relocation
      -- header for .shstrtab
 *)


(** *Transition state *)
Record elf_state :=
  { e_sections : list section;
    e_headers : list section_header;
    e_shstrtbl : list byte;
    e_sections_ofs : Z;
    e_headers_idx : Z;
    e_shstrtbl_ofs: Z }.

Definition update_elf_state st secs h str secs_size h_num str_size : elf_state :=
  {| e_sections := st.(e_sections) ++ secs;
     e_headers := st.(e_headers) ++ h;
     e_shstrtbl := st.(e_shstrtbl) ++ str;
     e_sections_ofs := st.(e_sections_ofs) + secs_size;
     e_headers_idx := st.(e_headers_idx) + h_num;
     e_shstrtbl_ofs := st.(e_shstrtbl_ofs) + str_size |}.

Definition initial_elf_state :=
  {| e_sections := [];
     e_headers := [null_section_header];
     e_shstrtbl := [];
     e_sections_ofs := 0;
     e_headers_idx := 1;
     e_shstrtbl_ofs := 0 |}.



(** ** Generation of ELF header *)

Definition get_sections_size (t: sectable) :=
  PTree.fold1 (fun acc sec => sec_size sec + acc) t 0.

Definition get_elf_shoff (p:program) :=
  elf_header_size +
  get_sections_size p.(prog_sectable).

  
Definition gen_elf_header (st: elf_state) : elf_header :=
  {| e_class        := if Archi.ptr64 then ELFCLASS64 else  ELFCLASS32;
     e_encoding     := if Archi.big_endian then ELFDATA2MSB else ELFDATA2LSB;
     e_version      := EV_CURRENT;
     e_type         := ET_REL;
     e_machine      := machine;
     e_entry        := 0;
     e_phoff        := 0;
     e_shoff        := elf_header_size + st.(e_sections_ofs);      
     e_flags        := elf_flag;
     e_ehsize       := elf_header_size;
     e_phentsize    := prog_header_size;
     e_phnum        := 0;
     e_shentsize    := sec_header_size;
     e_shnum        := Z.of_nat (length st.(e_headers)); (* one null header *)
     e_shstrndx     := Z.of_nat (length st.(e_headers)) -1 ; (* the last header *)
  |}.


Fixpoint list_first_n {A:Type} (n:nat) (l:list A) :=
  match n, l with
  | O, _ => nil
  | S n', (h::t) => h :: (list_first_n n' t)
  | _ , nil =>  nil
  end.

(* Fixpoint sectable_prefix_size (id:N) t := *)
(*   let l := list_first_n (N.to_nat id) t in *)
(*   get_sections_size l. *)

(* Lemma unfold_sectable_prefix_size : forall id t, *)
(*     sectable_prefix_size id t =    *)
(*     get_sections_size (list_first_n (N.to_nat id) t). *)
(* Proof. *)
(*   induction id.  *)
(*   - cbn. auto. *)
(*   - cbn. auto. *)
(* Qed. *)

                      
(* Definition get_sh_offset id (t:sectable) := *)
(*   elf_header_size + (sectable_prefix_size (SecTable.idx id) t). *)

(* Definition get_section_size id (t:sectable) := *)
(*   match SecTable.get id t with *)
(*   | None => 0 *)
(*   | Some s => sec_size s *)
(*   end. *)

(** Create section headers *)
(* generated while iterate the sectable, ofs not contain elf_header *)
(* shstrtbl_idx: the section header name index in section headers string table*)
Definition gen_rodata_sec_header (sec: list byte) (shstrtbl_idx: Z) (sec_ofs: Z) :=
  {| sh_name     := shstrtbl_idx;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.of_nat (length sec);
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 16;
     sh_entsize  := 0;
  |}.

Definition gen_data_sec_header (sec: list byte) (shstrtbl_idx: Z) (sec_ofs: Z) :=
  {| sh_name     := shstrtbl_idx;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC; SHF_WRITE];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.of_nat (length sec);
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

Definition gen_text_sec_header (sec: list byte) (shstrtbl_idx: Z) (sec_ofs: Z) :=
  {| sh_name     := shstrtbl_idx;
     sh_type     := SHT_PROGBITS;
     sh_flags    := [SHF_ALLOC; SHF_EXECINSTR];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.of_nat (length sec);
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

(** We assume local symbols come before global symbols,
 so one greater than the index of the last local symbol is exactly 
 the size of local symbols*)
Definition one_greater_last_local_symb_index (symbtbl: list symbentry) :=
  let locals := filter (fun s => match symbentry_bind s with
                                    | bind_local => true
                                    | _ => false
                                    end) symbtbl in
  Z.of_nat (length locals + 1).

(* strtbl_idx: strtbl index in section headers table *)
Definition gen_symtab_sec_header (symbtbl: list symbentry) (shstrtbl_idx: Z) (sec_ofs: Z) (strtbl_idx: Z):=
  {| sh_name     := shstrtbl_idx;
     sh_type     := SHT_SYMTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := elf_header_size +  sec_ofs;
     sh_size     := Z.mul symb_entry_size (Z.of_nat (length symbtbl) + 1); (* don't forget dummy symbtable *)
     sh_link     := strtbl_idx;
     sh_info     := one_greater_last_local_symb_index symbtbl;
     sh_addralign := 1;
     sh_entsize  := symb_entry_size;
  |}.


(* sh_link: related symbol table *)
(* sh_info: reloction related section *)
Definition gen_rel_sec_header (reloctbl: list relocentry) (shstrtbl_idx: Z) (sec_ofs: Z) (symbtbl_idx: Z) (related_sec: Z):=
  {| sh_name     := shstrtbl_idx;
     sh_type     := rel_eh_type;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.mul (Z.of_nat reloc_entry_size) (Z.of_nat (length reloctbl));
     sh_link     := symbtbl_idx;
     sh_info     := related_sec;
     sh_addralign := 1;
     sh_entsize  := (Z.of_nat reloc_entry_size);
  |}.

(* Definition gen_reldata_sec_header p := *)
(*   let t := (prog_sectable p) in *)
(*   {| sh_name     := reladata_str_ofs; *)
(*      sh_type     := SHT_REL; *)
(*      sh_flags    := []; *)
(*      sh_addr     := 0; *)
(*      sh_offset   := get_sh_offset sec_rel_data_id t; *)
(*      sh_size     := get_section_size sec_rel_data_id t; *)
(*      sh_link     := Z.of_N sec_symbtbl_id; *)
(*      sh_info     := Z.of_N sec_data_id; *)
(*      sh_addralign := 1; *)
(*      sh_entsize  := reloc_entry_size; *)
(*   |}. *)

(* Definition gen_reltext_sec_header p := *)
(*   let t := (prog_sectable p) in *)
(*   {| sh_name     := relatext_str_ofs; *)
(*      sh_type     := SHT_REL; *)
(*      sh_flags    := []; *)
(*      sh_addr     := 0; *)
(*      sh_offset   := get_sh_offset sec_rel_code_id t; *)
(*      sh_size     := get_section_size sec_rel_code_id t; *)
(*      sh_link     := Z.of_N sec_symbtbl_id; *)
(*      sh_info     := Z.of_N sec_code_id; *)
(*      sh_addralign := 1; *)
(*      sh_entsize  := reloc_entry_size; *)
(*   |}. *)

(* generate strtable and sec header strtable *)
Definition gen_strtab_sec_header (sec: list byte) (shstrtbl_idx: Z) (sec_ofs: Z) :=
  {| sh_name     := shstrtbl_idx;
     sh_type     := SHT_STRTAB;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.of_nat (length sec);
     sh_link     := 0;
     sh_info     := 0;
     sh_addralign := 1;
     sh_entsize  := 0;
  |}.

(* Definition gen_strtab_sec_header (sec: list byte) (shstrtbl_idx: Z) (sec_ofs: Z) := *)
(*   {| sh_name     := strtab_str_ofs; *)
(*      sh_type     := SHT_STRTAB; *)
(*      sh_flags    := []; *)
(*      sh_addr     := 0; *)
(*      sh_offset   := get_sh_offset sec_strtbl_id t; *)
(*      sh_size     := get_section_size sec_strtbl_id t; *)
(*      sh_link     := 0; *)
(*      sh_info     := 0; *)
(*      sh_addralign := 1; *)
(*      sh_entsize  := 0; *)
(*   |}. *)


(** Generation of the Elf file *)

(* Sorting of symbtable *)
Definition filter_local_symbe (id_symbe:ident * symbentry) :=
  match symbentry_bind (snd id_symbe) with
  | bind_local => true
  | bind_global => false
  end.

Definition filter_global_symbe (id_symbe:ident * symbentry) :=
  match symbentry_bind (snd id_symbe) with
  | bind_global => true
  | bind_local => false
  end.

Definition sort_symbtable (id_symbt: list (ident * symbentry))
  : list (ident * symbentry) :=
  let symb_local := List.filter filter_local_symbe id_symbt in
  let symb_global := List.filter filter_global_symbe id_symbt in
  symb_local ++ symb_global.


(* Extract string table from symbol table  *)
(* every ident should map to one string *)
Definition acc_strtbl acc ofs (id: ident) : res (list byte * Z) :=
  match find_symbol_pos id with
  | None => Error [MSG "Cannot find the string of the symbol "; CTX id]
  | Some n =>
    let bytes := map (fun p => Byte.repr (Zpos p)) n in
    (* check whether there is HB["00"] in bytes *)
    if in_dec Byte.eq_dec HB["00"] bytes then
      Error [MSG "Symbol string contains '\0'"; CTX id]    
    else
      OK (acc ++ bytes ++  [HB["00"]], ofs + Z.of_nat (length bytes) + 1)  
  end.

(* (* content of strtbl, map from ident to index in the strtbl, the accumulate ofs *) *)
(* Definition gen_strtbl (symbols : list ident) : res (list byte * PTree.t Z * Z) := *)
(*   fold_left acc_strtbl symbols (OK ([HB["00"]], PTree.empty Z, 1)). *)

(* generate relocation table string .relname from relocation map*)
Definition acc_relstrtbl acc ofs (id: ident) : res (list byte * Z) :=
  match find_symbol_pos id with
  | None => Error [MSG "Cannot find the string of the symbol "; CTX id]
  | Some n =>
    let bytes := map (fun p => Byte.repr (Zpos p)) n in
    (* check whether there is HB["00"] in bytes *)
    if in_dec Byte.eq_dec HB["00"] bytes then
      Error [MSG "Symbol string contains '\0'"; CTX id]
    else
      OK (acc ++ SB[".rel"] ++ bytes ++  [HB["00"]], ofs + Z.of_nat (length bytes) + 5)               
  end.

(* ofs is the previous section header string table offset *)
(* Definition gen_relstrtbl (symbols : list ident) (ofs: Z) : res (list byte * PTree.t Z * Z) := *)
(*   fold_left acc_relstrtbl symbols (OK ([], PTree.empty Z, ofs)). *)

Definition acc_ident_to_index (acc: PTree.t Z * Z) (id: ident) :=
  let (t, idx) := acc in
  (PTree.set id idx t, idx + 1).

Definition ident_to_index (idl : list ident) (start: Z): PTree.t Z :=
  fst (fold_left acc_ident_to_index idl (PTree.empty Z, start)).

(* generate section header and shstrtbl from text and data section, not include strtbl, symbtbl, reltbl*)
(* also return the section accumulated size *)
(* acc: section table, section header, section table offset, shstrtbl, strtbl offset *)
Definition acc_sections_headers (symbtbl: symbtable) (res_acc: res (list section * list section_header * Z * list byte * Z)) (id_sec: ident * RelocProgramBytes.section) : res (list section * list section_header * Z * list byte * Z) :=
  do secs_hs_ofs <- res_acc;
  let '(secs,hs,ofs,shstrtbl,shstrofs) := secs_hs_ofs in
  let (id, sec0) := id_sec in
  do (shstrtbl', shstrofs') <- acc_strtbl shstrtbl shstrofs id;
  match PTree.get id symbtbl with
  | None => Error [MSG "Cannot find the symbol entry of the symbol "; CTX id]
  | Some e =>
    match sec0 with
    | sec_text sec =>
    (* match PTree.get id shstrmap with *)
    (* | None => Error [MSG "Cannot find the section header string table index  of the symbol "; CTX id] *)
    (* | Some idx => *)
      let h := gen_text_sec_header sec shstrofs ofs in
      (* consistency checking *)
      if Z.eqb (Z.of_nat (length sec)) e.(symbentry_size) then
        OK (secs ++ [sec], hs++[h],ofs + (Z.of_nat (length sec)), shstrtbl', shstrofs')
      else
        Error [MSG "Inconsistency, section length not equal to symbentry field "; CTX id]
    | sec_rwdata sec =>
      let h := gen_data_sec_header sec shstrofs ofs in
      if Z.eqb (Z.of_nat (length sec)) e.(symbentry_size) then
        OK (secs++[sec], hs++[h],ofs + (Z.of_nat (length sec)), shstrtbl', shstrofs')
      else
        Error [MSG "Inconsistency, section length not equal to symbentry field "; CTX id]
    (* read-only infomation in symb table *)
    | sec_rodata sec =>
      let h := gen_rodata_sec_header sec shstrofs ofs in
      if Z.eqb (Z.of_nat (length sec)) e.(symbentry_size) then
        OK (secs++[sec],hs++[h],ofs + (Z.of_nat (length sec)), shstrtbl', shstrofs')
      else
        Error [MSG "Inconsistency, section length not equal to symbentry field "; CTX id]
    end
  end.

(* return section headers and the size of sections *)
Definition gen_section_header (idl_sectbl: list (ident * RelocProgramBytes.section)) (symbtbl: symbtable): res (list section* list section_header * Z * list byte * Z) :=
  fold_left  (acc_sections_headers symbtbl) idl_sectbl (OK ([],[],0,[Byte.repr 0],1)).


(* Definition transl_section (sec: RelocProgram.section) : res section := *)
(*   match sec with *)
(*   | sec_bytes bs => OK bs *)
(*   | _ => Error (msg "Section has not been encoded into bytes") *)
(*   end. *)

(* Definition acc_sections sec r := *)
(*   do r' <- r; *)
(*   do sec' <- transl_section sec; *)
(*   OK (sec' :: r'). *)

(* Definition gen_sections (t:list (RelocProgram.section)) : res (list section) := *)
(*   fold_right acc_sections (OK []) t. *)

Definition shstrtab_str := SB[".shstrtab"] ++ [HB["00"]].
Definition strtab_str := SB[".strtab"] ++ [HB["00"]].
Definition symtab_str := SB[".symtab"] ++ [HB["00"]].

(* return elf_state, section id to index mapping, id to string idx in shstring table mapping *)
Definition gen_text_data_sections_and_shstrtbl (p: RelocProgramBytes.program) (st:elf_state) : res (elf_state * PTree.t Z) :=
  (* generate ident to section index mapping *)
  let idl_sectbl := PTree.elements (prog_sectable p) in
  let secidl := map fst idl_sectbl in
  let sectbl := map snd idl_sectbl in
  (* generate section header string table from section id*)
  let secidxmap := ident_to_index secidl 1 in
  (* (* generate section header string table and mapping *) *)
  (* do shstrtbl_res <- gen_strtbl secidl; *)
  (* let '(shstrtbl0, shstrmap, shstrtbl_size0) := shstrtbl_res in *)
  (* generate section header and shstrtbl*)
  do res_sections_headers_ofs <- gen_section_header idl_sectbl p.(prog_symbtable);
  let '(sectbl0, headers0, ofs0, shstrtbl0, shstrtbl_size0) := res_sections_headers_ofs in
  let secs_size_check := get_sections_size (prog_sectable p) in
  if Z.eqb ofs0 secs_size_check then
    if Nat.eq_dec (length sectbl0) (length headers0) then
      let elf_state1 := update_elf_state st sectbl0 headers0 shstrtbl0 ofs0 (Z.of_nat (length headers0)) shstrtbl_size0 in
      OK (elf_state1, secidxmap)
    else Error (msg "Sections len <> Sectio headers len")
  else Error [MSG "Section size inconsistent between symbol table and section table"].


(* Compute (length encode_dummy_symbentry). *)
(* return: symbtable, strtbl, strtbl_ofs *)
Definition acc_symbtable_bytes  (idxmap: PTree.t Z) acc (id_e: ident * symbentry) : res (list byte * list byte * Z) :=
  let (id, e) := id_e in
  do acc' <- acc;
  let '(symbtbl, strtbl, strtbl_ofs) := acc' in
  do ebytes <-
     (if Archi.ptr64 then
        (encode_symbentry64 e strtbl_ofs idxmap)
      else (encode_symbentry32 e strtbl_ofs idxmap));
  do (strtbl', strtbl_ofs') <- acc_strtbl strtbl strtbl_ofs id;
  OK (symbtbl ++ ebytes, strtbl', strtbl_ofs').

(* generate symbtable table section *)

Definition create_symbtable_section (t:list (ident * symbentry)) (idxmap: PTree.t Z) : res (list byte * list byte * Z) :=
  fold_left (acc_symbtable_bytes idxmap) t (OK ([],[Byte.repr 0],1)).

(* input: program, ident to section header index, state *)
(* output: state, indet to symbol entry index mapping, ident to string index in strtbl mapping (unused and remove it)*)
Definition gen_symtbl_section_strtbl_and_shstr (p: RelocProgramBytes.program) (secidxmap : PTree.t Z) (st: elf_state) :res (elf_state * PTree.t Z) :=
  let idl_symbtbl := PTree.elements (prog_symbtable p) in
  let idl_symbtbl' := sort_symbtable idl_symbtbl in
  let symbidl := map fst idl_symbtbl' in
  let symbtbl := map snd idl_symbtbl' in
  let symtbl_idx_map := ident_to_index symbidl 1 in
  (* do str_res  <-  gen_strtbl symbidl; *)
  (* let '(strtbl, strmap, strtbl_size) := str_res in *)
  (* symbtable and strtbl *)
  let dummy_entry := (if Archi.ptr64 then encode_dummy_symbentry64 else encode_dummy_symbentry32) in
  do symbsec_strtbl_strtbl_size <- create_symbtable_section idl_symbtbl' secidxmap;
  let '(symbsec, strtbl, strtbl_size) := symbsec_strtbl_strtbl_size in
  let strtbl_h := gen_strtab_sec_header strtbl st.(e_shstrtbl_ofs) st.(e_sections_ofs) in
  (* add string table to elf state *)  
  let st1 := update_elf_state st [strtbl] [strtbl_h] strtab_str strtbl_size 1 (Z.of_nat (length strtab_str)) in
  (* encode symbol table into section *)    
  let symb_h := gen_symtab_sec_header symbtbl st1.(e_shstrtbl_ofs) st1.(e_sections_ofs) st.(e_headers_idx) in (* we need strtable section header index *)
  if Z.eqb (Z.of_nat (length symbsec + length dummy_entry)) symb_h.(sh_size) then
    let st2 := update_elf_state st1 [dummy_entry ++ symbsec] [symb_h] symtab_str symb_h.(sh_size) 1 (Z.of_nat (length symtab_str)) in
    OK (st2, symtbl_idx_map)
  else
    Error [MSG "Symbol table size inconsistent"].

Section GEN_RELOC_SECS.

  (* ident to index in headers *)
  Variable (symb_idxmap sec_idxmap :PTree.t Z).
  (* symbol table index in headers table *)
  Variable (symbtbl_idx: Z).

(* return: sections, section headers, section offset, shstrtbl, shstrtbl_ofs *)
Definition acc_reloc_sections_headers (acc: res (list section * list section_header * Z * list byte * Z)) (id_reloctbl:ident * list relocentry) :=
  do acc' <- acc;
  let '(secs, hs, ofs, shstrtbl, shstrtbl_ofs) := acc' in
  let (id, reloctbl) := id_reloctbl in
  match sec_idxmap ! id with
  | None => Error [MSG "Reloction table generation: no related section header index! "; CTX id]
  | Some sec_h_idx  =>
    let h := gen_rel_sec_header reloctbl shstrtbl_ofs ofs symbtbl_idx sec_h_idx (* attention to the null header ! no need to +1 because the idxmap generated from symbol table has the consideration of null header*) in  
    do sec <- encode_reloctable symb_idxmap reloctbl;
    do (shstrtbl', shstrtbl_ofs') <- acc_relstrtbl shstrtbl shstrtbl_ofs id;
    OK (secs++[sec], hs++[h], ofs + Z.of_nat (length sec), shstrtbl', shstrtbl_ofs')
    end.

(* reloc sections, reloc headers, starting ofs of relocation table section in elf file, shstrtbl ,shstrtbl_ofs*)
Definition gen_reloc_sections_headers (idl_reloctbl: list (ident * list relocentry)) (sec_start_ofs shstrtbl_start_ofs: Z) : res (list section * list section_header * Z * list byte * Z) :=
  fold_left acc_reloc_sections_headers idl_reloctbl (OK ([],[],sec_start_ofs, [], shstrtbl_start_ofs)).

End GEN_RELOC_SECS.

(* symb_idxmap: get the index in symbtbl *)
(* sec_idxmap: get the index of header of the section that be relocated in the section header table*)
(* REMOVED: strmap: we do not generate new string for reloc section, we use the related section name *)
(*  *)
Definition gen_reloc_sections_and_shstrtbl (p: program) (symb_idxmap sec_idxmap :PTree.t Z) (st: elf_state) :=
  let idl_reloctbl := PTree.elements p.(prog_reloctables) in
  let rel_idlist := map fst idl_reloctbl in
  (* generate relocation string table , append to shstrtbl *)
  let sec_ofs := st.(e_sections_ofs) in
  let shstrtbl_ofs := st.(e_shstrtbl_ofs) in
  let symbtbl_idx := st.(e_headers_idx) - 1 in
  do r <- gen_reloc_sections_headers symb_idxmap sec_idxmap symbtbl_idx  idl_reloctbl sec_ofs shstrtbl_ofs;
  let '(secs, hs, sec_ofs', shstrtbl', shstrtbl_ofs') := r in
  if Nat.eq_dec (length secs) (length hs) then
    let st1 := update_elf_state st secs hs shstrtbl' (sec_ofs' - sec_ofs) (Z.of_nat (length idl_reloctbl)) (shstrtbl_ofs' - shstrtbl_ofs) in
    OK st1
  else Error (msg "reloc section generation: sections len <> section headers len").

(* shstrtable generation *)
Definition gen_shstrtbl (st: elf_state) :=
  (* only update shstrtbl *)
  let st1 := update_elf_state st [] [] shstrtab_str 0 0 (Z.of_nat (length shstrtab_str)) in
  (* st.(e_shstrtbl_ofs): the shstrtbl_name location in shstrtbl *)
  let shstrtbl_h := gen_strtab_sec_header st1.(e_shstrtbl) st.(e_shstrtbl_ofs) st1.(e_sections_ofs) in
  (* the secs_size is the shstrtbl size *)
  if Z.eqb (Z.of_nat (length st1.(e_shstrtbl))) st1.(e_shstrtbl_ofs) then
   OK ( update_elf_state st1 [st1.(e_shstrtbl)] [shstrtbl_h] [] st1.(e_shstrtbl_ofs) 1 0)
  else
    Error [MSG "Section header string table size inconsistent"].
    
Definition gen_reloc_elf (p:program) :=
  (** *Generate text and data section , related headers and shstrtbl *)
  do st1_secidxmap <- gen_text_data_sections_and_shstrtbl p initial_elf_state;
  let '(st1, secidxmap) := st1_secidxmap in
  (** *Generate string table and symbtbl from symbol table *)
  do st2_symbmap <- gen_symtbl_section_strtbl_and_shstr p secidxmap st1;
  let '(st2, symtbl_idx_map) := st2_symbmap in
  (** *Generate reloction table section and headers *)
  do st3 <- gen_reloc_sections_and_shstrtbl p symtbl_idx_map secidxmap st2;
  (** *Generate section header string table and header *)
  do st4 <- gen_shstrtbl st3;
  (* debug: check section size *)
  if Z.eqb st4.(e_sections_ofs) (fold_right (fun s acc => acc + Z.of_nat (length s)) 0 (st4.(e_sections))) then
  (** *Generate ELF header *)
  let elf_h := gen_elf_header st4 in
  (* file too big ? *)
  if Nat.eqb (length st4.(e_sections)) (length st4.(e_headers) - 1) then
    if zlt elf_h.(e_shoff) (two_p 32) then
      OK {| prog_defs := RelocProg.prog_defs p;
            prog_public   := RelocProg.prog_public p;
            prog_main     := RelocProg.prog_main p;
            prog_senv     := RelocProg.prog_senv p;
            
            elf_head := elf_h;
            elf_sections := st4.(e_sections);
            elf_section_headers := st4.(e_headers) |}
    else Error (msg "Sections too big (e_shoff above bounds)")
  else Error (msg "unequal length of sections and section headers")
  else Error (msg "Generate ELF header fail: shofs inconsistent").
