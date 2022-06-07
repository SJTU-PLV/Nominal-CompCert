(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 22, 2019 *)
(* Last updated: Mar 4, 2022 *)
(* *******************  *)

(** * Generation of the relocatable Elf file *)

Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import RelocProgram RelocProg Encode.
Require Import Memdata.
Require Import RelocElf.
Require Import SymbolString.
(* Require Import ShstrtableEncode. *)
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode.
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

Section INSTR_SIZE.
Variable (instr_size : instruction -> Z).

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
  PTree.fold1 (fun acc sec => sec_size instr_size sec + acc) t 0.

Definition get_elf_shoff (p:program) :=
  elf_header_size +
  get_sections_size (prog_sectable p).

  
Definition gen_elf_header (st: elf_state) : elf_header :=
  {| e_class        := if Archi.ptr64 then ELFCLASS64 else  ELFCLASS32;
     e_encoding     := if Archi.big_endian then ELFDATA2MSB else ELFDATA2LSB;
     e_version      := EV_CURRENT;
     e_type         := ET_REL;
     e_machine      := if Archi.ptr64 then EM_x86_64 else EM_386;
     e_entry        := 0;
     e_phoff        := 0;
     e_shoff        := elf_header_size + st.(e_sections_ofs);      
     e_flags        := 0;
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
  Z.of_nat (1 + length locals).

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
     sh_type     := SHT_REL;
     sh_flags    := [];
     sh_addr     := 0;
     sh_offset   := elf_header_size + sec_ofs;
     sh_size     := Z.mul reloc_entry_size (Z.of_nat (length reloctbl));
     sh_link     := symbtbl_idx;
     sh_info     := related_sec;
     sh_addralign := 1;
     sh_entsize  := reloc_entry_size;
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
Definition acc_strtbl (res_acc: res (list byte * PTree.t Z * Z)) (id: ident) : res (list byte * PTree.t Z * Z) :=
  do acc <- res_acc;
  let '(acc', strmap, ofs) := acc in
  match find_symbol_pos id with
  | None => Error [MSG "Cannot find the string of the symbol "; CTX id]
  | Some n =>
    let bytes := map (fun p => Byte.repr (Zpos p)) n in
    let strmap' := PTree.set id ofs strmap in
    OK (acc' ++ bytes ++  [HB["00"]], strmap', ofs + Z.of_nat (length bytes) + 1)
  end.

(* content of strtbl, map from ident to index in the strtbl, the accumulate ofs *)
Definition gen_strtbl (symbols : list ident) : res (list byte * PTree.t Z * Z) :=
  fold_left acc_strtbl symbols (OK ([HB["00"]], PTree.empty Z, 1)).

(* generate relocation table string .relname from relocation map*)
Definition acc_relstrtbl (res_acc: res (list byte * PTree.t Z * Z)) (id: ident) : res (list byte * PTree.t Z * Z) :=
  do acc <- res_acc;
  let '(acc', strmap, ofs) := acc in
  match find_symbol_pos id with
  | None => Error [MSG "Cannot find the string of the symbol "; CTX id]
  | Some n =>
    let bytes := map (fun p => Byte.repr (Zpos p)) n in
    let strmap' := PTree.set id ofs strmap in
    OK (acc' ++ SB[".rel"] ++ bytes ++  [HB["00"]], strmap', ofs + Z.of_nat (length bytes) + 5 (*1 + 4*))
  end.

(* ofs is the previous section header string table offset *)
Definition gen_relstrtbl (symbols : list ident) (ofs: Z) : res (list byte * PTree.t Z * Z) :=
  fold_left acc_relstrtbl symbols (OK ([], PTree.empty Z, ofs)).

(* ident to section index mapping *)
Fixpoint ident_to_index_aux (idl: list ident) (idx: Z) (acc:PTree.t Z) : PTree.t Z:=
  match idl with
  | [] => acc
  | h::t =>
    let acc' := PTree.set h idx acc in
    ident_to_index_aux t (idx+1) acc'
  end.


Definition ident_to_index (idl : list ident) (start: Z): PTree.t Z :=
  ident_to_index_aux idl start (PTree.empty Z).

(* generate section header from text and data section, not include strtbl, symbtbl, reltbl*)
(* also return the section accumulated size *)
Definition acc_headers (symbtbl: symbtable) (shstrmap: PTree.t Z) (res_acc: res (list section_header * Z)) (id_sec: ident * RelocProgram.section) : res (list section_header * Z) :=
  do (acc, ofs) <- res_acc;
  let (id, sec0) := id_sec in
  match sec0 with
  | sec_bytes sec =>
    match PTree.get id shstrmap with
    | None => Error [MSG "Cannot find the section header string table index  of the symbol "; CTX id]
    | Some idx =>
      match PTree.get id symbtbl with
      | None => Error [MSG "Cannot find the symbol entry of the symbol "; CTX id]
      | Some e =>
        match e.(symbentry_type) with
        | symb_func =>
          let h := gen_text_sec_header sec idx ofs in
          (* consistency checking *)
          if Z.eqb (Z.of_nat (length sec)) e.(symbentry_size) then
            OK (acc++[h],ofs + e.(symbentry_size))
          else
            Error [MSG "Inconsistency, section length not equal to symbentry field "; CTX id]
        | symb_rwdata =>
          let h := gen_data_sec_header sec idx ofs in
          OK (acc++[h],ofs + e.(symbentry_size))
        (* read-only infomation in symb table *)
        | symb_rodata =>
          let h := gen_rodata_sec_header sec idx ofs in
          OK (acc++[h],ofs + e.(symbentry_size))
        |  _ => Error [MSG "Impossible: no type for section "; CTX id]
        end
      end
    end
  | _ => Error [MSG "Section haven't been encoded"; CTX id]
  end.

(* return section headers and the size of sections *)
Definition gen_section_header (idl_sectbl: list (ident * RelocProgram.section)) (symbtbl: symbtable) (shstrmap: PTree.t Z) : res (list section_header * Z) :=
  fold_left  (acc_headers symbtbl shstrmap) idl_sectbl (OK ([],0)).


Definition transl_section (sec: RelocProgram.section) : res section :=
  match sec with
  | sec_bytes bs => OK bs
  | _ => Error (msg "Section has not been encoded into bytes")
  end.

Definition acc_sections sec r :=
  do r' <- r;
  do sec' <- transl_section sec;
  OK (sec' :: r').

Definition gen_sections (t:list (RelocProgram.section)) : res (list section) :=
  fold_right acc_sections (OK []) t.

Definition shstrtab_str := SB[".shstrtab"] ++ [HB["00"]].
Definition strtab_str := SB[".strtab"] ++ [HB["00"]].
Definition symtab_str := SB[".symtab"] ++ [HB["00"]].

(* return elf_state, section id to index mapping, id to string idx in shstring table mapping *)
Definition gen_text_data_sections_and_shstrtbl (p: program) (st:elf_state) : res (elf_state * PTree.t Z * PTree.t Z) :=
  (* generate ident to section index mapping *)
  let idl_sectbl := PTree.elements (prog_sectable p) in
  let secidl := map fst idl_sectbl in
  let sectbl := map snd idl_sectbl in
  (* generate section header string table from section id*)
  let secidxmap := ident_to_index secidl 1 in
  (* generate section header string table and mapping *)
  do shstrtbl_res <- gen_strtbl secidl;
  let '(shstrtbl0, shstrmap, shstrtbl_size0) := shstrtbl_res in
  (* generate section header *)
  do res_headers_ofs <- gen_section_header idl_sectbl p.(prog_symbtable) shstrmap;
  let (headers0, ofs0) := res_headers_ofs in
  (* generate section bytes which only contains func and data *)
  do sectbl0 <- gen_sections sectbl;
  let secs_size_check := get_sections_size (prog_sectable p) in
  if Z.eqb ofs0 secs_size_check then
    let elf_state1 := update_elf_state st sectbl0 headers0 shstrtbl0 ofs0 (Z.of_nat (length headers0)) shstrtbl_size0 in
    OK (elf_state1, secidxmap, shstrmap)
  else Error [MSG "Section size inconsistent between symbol table and section table"].

(* input: program, ident to section header index, state *)
(* output: state, indet to symbol entry index mapping, ident to string index in strtbl mapping (unused and remove it)*)
Definition gen_symtbl_section_strtbl_and_shstr (p: program) (secidxmap : PTree.t Z) (st: elf_state) :res (elf_state * PTree.t Z) :=
  let idl_symbtbl := PTree.elements (prog_symbtable p) in
  let idl_symbtbl' := sort_symbtable idl_symbtbl in
  let symbidl := map fst idl_symbtbl' in
  let symbtbl := map snd idl_symbtbl' in
  let symtbl_idx_map := ident_to_index symbidl 1 in
  do str_res  <-  gen_strtbl symbidl;
  let '(strtbl, strmap, strtbl_size) := str_res in
  let strtbl_h := gen_strtab_sec_header strtbl st.(e_shstrtbl_ofs) st.(e_sections_ofs) in
  (* add string table to elf state *)
  (* Add checking for debug *)
  if Z.eqb (Z.of_nat (length strtbl)) strtbl_size then
    let st1 := update_elf_state st [strtbl] [strtbl_h] strtab_str strtbl_size 1 (Z.of_nat (length strtab_str)) in    
    (* encode symbol table into section *)
    do symbsec <- create_symbtable_section idl_symbtbl' strmap secidxmap;
    let symb_h := gen_symtab_sec_header symbtbl st1.(e_shstrtbl_ofs) st1.(e_sections_ofs) st.(e_headers_idx) in (* we need strtable section header index *)
    if Z.eqb (Z.of_nat (length symbsec)) symb_h.(sh_size) then
      let st2 := update_elf_state st1 [symbsec] [symb_h] symtab_str symb_h.(sh_size) 1 (Z.of_nat (length symtab_str)) in
      OK (st2, symtbl_idx_map)
    else
      Error [MSG "Symbol table size inconsistent"]
  else Error [MSG "String table size generated from symbtable inconsistent"].

Section GEN_RELOC_SECS.

  (* ident to index in headers *)
  Variable (symb_idxmap sec_idxmap :PTree.t Z).
  (* symbol table index in headers table *)
  Variable (symbtbl_idx: Z).
  (* use the section name instead of new name *)
  Variable (strmap: PTree.t Z).
  
Definition acc_reloc_sections_headers acc (id_reloctbl:ident * list relocentry) :=
  do acc' <- acc;
  let '(secs, hs, ofs) := acc' in
  let (id, reloctbl) := id_reloctbl in
  match sec_idxmap ! id with
  | None => Error [MSG "Reloction table generation: no related section header index! "; CTX id]
  | Some sec_h_idx  =>
    match strmap ! id with
    | None => Error [MSG "Reloction table generation: no related string for "; CTX id]
    | Some strtbl_ofs =>
    let h := gen_rel_sec_header reloctbl strtbl_ofs ofs symbtbl_idx sec_h_idx (* attention to the null header ! no need to +1 because the idxmap generated from symbol table has the consideration of null header*) in  
    do sec <- encode_reloctable symb_idxmap reloctbl;
    OK (secs++[sec], hs++[h], ofs + Z.of_nat (length sec))
    end
  end.

(* reloc sections, reloc headers, starting ofs of relocation table section in elf file*)
Definition gen_reloc_sections_headers (idl_reloctbl: list (ident * list relocentry)) (start_ofs: Z) : res (list section * list section_header * Z ) :=
  fold_left acc_reloc_sections_headers idl_reloctbl (OK ([],[],start_ofs)).

End GEN_RELOC_SECS.

(* symb_idxmap: get the index in symbtbl *)
(* sec_idxmap: get the index of header of the section that be relocated in the section header table*)
(* REMOVED: strmap: we do not generate new string for reloc section, we use the related section name *)
(*  *)
Definition gen_reloc_sections_and_shstrtbl (p: program) (symb_idxmap sec_idxmap :PTree.t Z) (st: elf_state) :=
  let idl_reloctbl := PTree.elements p.(prog_reloctables) in
  let rel_idlist := map fst idl_reloctbl in
  (* generate relocation string table , append to shstrtbl *)
  do r <- gen_relstrtbl rel_idlist st.(e_shstrtbl_ofs);
  (* ofs is useless !! *)
  let '(rel_strtbl, rel_strmap, _ ) := r in
  let sec_ofs := st.(e_sections_ofs) in
  let symbtbl_idx := st.(e_headers_idx) - 1 in
  do r <- gen_reloc_sections_headers symb_idxmap sec_idxmap symbtbl_idx rel_strmap idl_reloctbl sec_ofs;
  let '(secs, hs, sec_ofs') := r in
  let st1 := update_elf_state st secs hs rel_strtbl (sec_ofs'-sec_ofs) (Z.of_nat (length idl_reloctbl)) (Z.of_nat (length rel_strtbl)) in
  OK st1.

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
  do st1_secidxmap_shstrmap <- gen_text_data_sections_and_shstrtbl p initial_elf_state;
  let '(st1, secidxmap, shstrmap) := st1_secidxmap_shstrmap in
  (** *Generate string table and symbtbl from symbol table *)
  do st2_symbmap <- gen_symtbl_section_strtbl_and_shstr p secidxmap st1;
  let '(st2, symtbl_idx_map) := st2_symbmap in
  (** *Generate reloction table section and headers *)
  do st3 <- gen_reloc_sections_and_shstrtbl p symtbl_idx_map secidxmap (* shstrmap *) st2;
  (** *Generate section header string table and header *)
  do st4 <- gen_shstrtbl st3;
  (* debug: check section size *)
  if Z.eqb st4.(e_sections_ofs) (fold_right (fun s acc => acc + Z.of_nat (length s)) 0 (st4.(e_sections))) then
  (** *Generate ELF header *)
  let elf_h := gen_elf_header st4 in
  (* file too big ? *)
  if zlt elf_h.(e_shoff) (two_p 32) then
    OK {| prog_defs := RelocProgram.prog_defs p;
          prog_public   := RelocProgram.prog_public p;
          prog_main     := RelocProgram.prog_main p;
          prog_senv     := RelocProgram.prog_senv p;

          elf_head := elf_h;
          elf_sections := st4.(e_sections);
          elf_section_headers := st4.(e_headers) |}
  else Error (msg "Sections too big (e_shoff above bounds)")
  else Error (msg "Generate ELF header fail: shofs inconsistent").
End INSTR_SIZE.

(* Definition gen_reloc_elf (p:program) : res elf_file := *)
(*   do secs <- gen_sections (prog_sectable p); *)
(*   do _ <- RelocProgSemantics3.decode_tables p; *)
(*     if (beq_nat (length secs) 9) then *)
(*       if zlt (get_elf_shoff p) (two_p 32) *)
(*       then  *)
(*         let headers := [null_section_header; *)
(*                        gen_rodata_sec_header p; *)
(*                        gen_data_sec_header p; *)
(*                        gen_text_sec_header p; *)
(*                        gen_strtab_sec_header p; *)
(*                        gen_symtab_sec_header p; *)
(*                        gen_relrodata_sec_header p; *)
(*                        gen_reldata_sec_header p; *)
(*                        gen_reltext_sec_header p; *)
(*                        gen_shstrtab_sec_header p] in *)
(*         OK {| prog_defs     := RelocProgram.prog_defs p; *)
(*               prog_public   := RelocProgram.prog_public p; *)
(*               prog_main     := RelocProgram.prog_main p; *)
(*               prog_senv     := RelocProgram.prog_senv p; *)
(*               elf_head      := gen_elf_header p; *)
(*               elf_sections  := secs; *)
(*               elf_section_headers := headers; *)
(*            |} *)
(*       else *)
(*         Error (msg "Sections too big (get_elf_shoff above bounds)") *)
(*     else *)
(*       Error [MSG "Number of sections is incorrect (not 9: "; POS (Pos.of_nat (length secs))]. *)

(* Require Import Lia. *)

(* Lemma gen_elf_header_valid p: *)
(*   0 <= get_elf_shoff p < two_p 32 -> *)
(*   length (prog_sectable p) = 9%nat -> *)
(*   valid_elf_header (gen_elf_header p). *)
(* Proof. *)
(*   unfold gen_elf_header. intros. *)
(*   constructor; simpl. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(*   auto. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(*   setoid_rewrite H10. *)
(*   vm_compute; intuition try congruence. *)
(*   vm_compute; intuition try congruence. *)
(* Qed. *)

(* Lemma sec_size_pos a: *)
(*   0 <= sec_size a. *)
(* Proof. *)
(*   destruct a; simpl. generalize (code_size_non_neg code); omega. *)
(*   generalize (init_data_list_size_pos init). omega. *)
(*   generalize (init_data_list_size_pos init). omega. *)
(*   omega. *)
(* Qed. *)

(* Lemma fold_sec_size_range: forall l, *)
(*     0 <= fold_right (fun (y : RelocProgram.section) (x : Z) => sec_size y + x) 0 l. *)
(* Proof. *)
(*   induction l; simpl; intros; eauto. omega. *)
(*   apply Z.add_nonneg_nonneg. apply sec_size_pos. auto. *)
(* Qed. *)

(* Lemma get_sections_size_pos t: *)
(*   0 <= get_sections_size t. *)
(* Proof. *)
(*   unfold get_sections_size. *)
(*   intros. rewrite <- fold_left_rev_right. *)
(*   apply fold_sec_size_range. *)
(* Qed. *)

(* Lemma sectable_prefix_size_pos: forall id stbl,  *)
(*     0 <= sectable_prefix_size id stbl. *)
(* Proof. *)
(*   intros. rewrite unfold_sectable_prefix_size. *)
(*   apply get_sections_size_pos. *)
(* Qed. *)

(* Lemma get_elf_shoff_pos p: *)
(*   0 <= get_elf_shoff p. *)
(* Proof. *)
(*   unfold get_elf_shoff. *)
(*   apply Z.add_nonneg_nonneg. vm_compute; intuition congruence. *)
(*   apply get_sections_size_pos. *)
(* Qed. *)

(* Lemma gen_sections_length t x (G: gen_sections t = OK x): *)
(*   (length x) = length t. *)
(* Proof. *)
(*   unfold gen_sections in G.  *)
(*   revert t x G. clear. *)
(*   induction t; simpl; intros; eauto. *)
(*   inv G. reflexivity. *)
(*   unfold acc_sections in G at 1. monadInv G. apply IHt in EQ. simpl in EQ. inv EQ. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma list_first_n_prefix: *)
(*   forall n {A} (l: list A), *)
(*   exists l2, l = list_first_n n l ++ l2. *)
(* Proof. *)
(*   induction n; simpl; intros; eauto. *)
(*   destruct l. simpl. eauto. simpl. *)
(*   edestruct (IHn A0 l) as (l2 & EQ). *)
(*   eexists. f_equal. eauto. *)
(* Qed. *)

(* Lemma fold_left_size_acc: forall b acc, *)
(*     fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b acc = *)
(*     acc + fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b 0. *)
(* Proof. *)
(*   induction b; simpl; intros; eauto. *)
(*   omega. *)
(*   rewrite (IHb (sec_size a + acc)). *)
(*   rewrite (IHb (sec_size a + 0)). omega. *)
(* Qed. *)

(* Lemma fold_left_le: forall b acc, *)
(*     acc <= fold_left (fun (acc : Z) (sec : RelocProgram.section) => sec_size sec + acc) b acc. *)
(* Proof. *)
(*   induction b; simpl; intros; eauto. *)
(*   omega. *)
(*   rewrite fold_left_size_acc. specialize (IHb 0). *)
(*   generalize (sec_size_pos a). omega. *)
(* Qed. *)

(* Lemma get_sections_size_app a b: *)
(*   get_sections_size (a ++ b) = get_sections_size a + get_sections_size b. *)
(* Proof. *)
(*   unfold get_sections_size. rewrite fold_left_app. *)
(*   rewrite fold_left_size_acc. auto. *)
(* Qed. *)

(* Lemma get_sh_offset_range p id *)
(*       (l : get_elf_shoff p < two_p 32): *)
(*   0 <= get_sh_offset id (prog_sectable p) < two_power_pos 32. *)
(* Proof. *)
(*   unfold get_elf_shoff, get_sh_offset in *. *)
(*   set (id' := SecTable.idx id). *)
(*   split. *)
(*   apply Z.add_nonneg_nonneg. vm_compute; intuition congruence. *)
(*   clear. induction id; simpl. vm_compute. congruence. *)
(*   apply sectable_prefix_size_pos. *)
(*   eapply Z.le_lt_trans. 2: eauto. *)
(*   apply Z.add_le_mono_l. *)
(*   generalize (prog_sectable p). clear. *)
(*   induction id; intros. *)
(*   apply get_sections_size_pos. *)
(*   rewrite unfold_sectable_prefix_size.  *)
(*   destruct (list_first_n_prefix (N.to_nat id') s) as (l2 & EQ). *)
(*   rewrite EQ at 2. *)
(*   rewrite get_sections_size_app. *)
(*   generalize (get_sections_size_pos l2); omega. *)
(* Qed. *)

(* Lemma get_section_size_range p id *)
(*       (l : get_elf_shoff p < two_p 32): *)
(*   0 <= get_section_size id (prog_sectable p) < two_power_pos 32. *)
(* Proof. *)
(*   unfold get_elf_shoff in *. *)
(*   split. *)
(*   unfold get_section_size. destr. apply sec_size_pos. omega. *)
(*   eapply Z.le_lt_trans. 2: eauto. *)
(*   cut (get_section_size id (prog_sectable p) <= get_sections_size (prog_sectable p)). *)
(*   cut (0 <= elf_header_size). intros; omega. vm_compute; congruence. *)
(*   generalize (prog_sectable p). clear. Opaque Z.add. *)
(*   unfold get_section_size, SecTable.get. generalize (N.to_nat (SecTable.idx id)). clear. *)
(*   unfold get_sections_size. *)
(*   induction n; destruct s; simpl; intros; eauto. omega. *)
(*   etransitivity. 2: apply fold_left_le. omega. omega. *)
(*   etransitivity. apply IHn. *)
(*   rewrite fold_left_size_acc with (acc:=sec_size v + 0) . *)
(*   generalize (sec_size_pos v). omega. *)
(* Qed. *)

(* Lemma get_sections_size_in t x: *)
(*   In x t -> *)
(*   sec_size x <= get_sections_size t. *)
(* Proof. *)
(*   revert x. *)
(*   unfold get_sections_size. *)
(*   induction t; simpl; intros; eauto. *)
(*   easy. *)
(*   destruct H. *)
(*   - subst; simpl. *)
(*     etransitivity. 2: apply fold_left_le. omega. *)
(*   - etransitivity. eapply IHt. auto. *)
(*     rewrite (fold_left_size_acc t (sec_size a + 0)). *)
(*     generalize (sec_size_pos a); omega. *)
(* Qed. *)

(* Lemma dummy_symbentry_length: length encode_dummy_symbentry = 16%nat. *)
(* Proof. *)
(*   unfold encode_dummy_symbentry. cbn. *)
(*   repeat rewrite app_length. *)
(*   repeat (setoid_rewrite encode_int_length; simpl). *)
(*   auto. *)
(* Qed. *)
  
(* Lemma create_symbtable_section_length p symt *)
(*       (EQ : create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt): *)
(*   sec_size symt = 16 * Z.of_nat (1 + length (prog_symbtable p)). *)
(* Proof. *)
(*   Opaque Z.mul. *)
(*   unfold create_symbtable_section in EQ. monadInv EQ. simpl. *)
(*   unfold encode_symbtable in EQ0.  *)
(*   rewrite app_length. rewrite dummy_symbentry_length. *)
(*   revert x EQ0. *)
(*   generalize (prog_strtable p). *)
(*   generalize (prog_symbtable p). *)
(*   induction s; intros; eauto. inv EQ0. reflexivity. *)
(*   simpl in EQ0. unfold acc_bytes at 1 in EQ0. monadInv EQ0. *)
(*   eapply IHs in EQ. *)
(*   repeat rewrite app_length. *)
(*   assert (length x1 = 16%nat). *)
(*   { *)
(*     clear - EQ0. *)
(*     unfold encode_symbentry in EQ0. monadInv EQ0. *)
(*     repeat rewrite app_length. *)
(*     repeat (setoid_rewrite encode_int_length; simpl). *)
(*     auto. *)
(*   } *)
(*   rewrite H. *)
(*   simpl length. *)
(*   rewrite Nat2Z.inj_add. rewrite EQ. lia. *)
(* Qed. *)

(* Lemma length_filter {A} (l: list A) f: *)
(*   (length (filter f l) <= length l)%nat. *)
(* Proof. *)
(*   induction l; simpl; intros; eauto. *)
(*   destr; simpl; omega. *)
(* Qed. *)

(* Lemma one_greater_last_local_symb_range p symt *)
(*       (EQ: create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt) *)
(*       (IN:  In symt (prog_sectable p)) *)
(*       (l : get_elf_shoff p < two_p 32): *)
(*   0 <= one_greater_last_local_symb_index p < two_power_pos 32. *)
(* Proof. *)
(*   unfold one_greater_last_local_symb_index. *)
(*   split. omega. *)
(*   eapply Z.le_lt_trans. 2: apply l. clear l. *)
(*   unfold get_elf_shoff. *)
(*   transitivity (get_sections_size (prog_sectable p)). *)
(*   2: change elf_header_size with 52; omega. *)
(*   etransitivity. 2: apply get_sections_size_in; eauto. *)
(*   erewrite create_symbtable_section_length; eauto. *)
(*   change 16 with (Z.of_nat 16). *)
(*   rewrite <- Nat2Z.inj_mul. *)
(*   apply Nat2Z.inj_le. *)
(*   transitivity (S (length (prog_symbtable p))). *)
(*   cbn. apply le_n_S. *)
(*   apply length_filter. *)
(*   lia. *)
(* Qed. *)

(* Lemma gen_reloc_elf_valid p ef (GRE: gen_reloc_elf p = OK ef) *)
(*       symt *)
(*       (SYMT: create_symbtable_section (prog_strtable p) (prog_symbtable p) = OK symt) *)
(*       (* (HD: hd sec_null (prog_sectable p) = sec_null) *) *)
(*       (INSYMT: In symt (prog_sectable p)): *)
(*   valid_elf_file ef. *)
(* Proof. *)
(*   unfold gen_reloc_elf in GRE. *)
(*   monadInv GRE. *)
(*   repeat destr_in EQ2. *)
(*   Opaque Z.add Z.eqb check_sizes. *)
(*   constructor; simpl. *)
(*   - apply gen_elf_header_valid. split; auto. *)
(*     apply get_elf_shoff_pos. *)
(*     apply Nat.eqb_eq in Heqb. *)
(*     erewrite <- gen_sections_length; eauto. *)
(*   - constructor. *)
(*     constructor; simpl; vm_compute; try intuition congruence. constructor. *)
(*     constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*     constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     eapply one_greater_last_local_symb_range; eauto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*         constructor. *)
(*     constructor; simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*     constructor. *)
(*     constructor;simpl. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     apply get_sh_offset_range; auto. *)
(*     apply get_section_size_range; auto. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     vm_compute; try intuition congruence. *)
(*     constructor. *)
(*     constructor.     *)
(*   - unfold get_elf_shoff. *)
(*     f_equal. *)
(*     clear -EQ. revert x EQ. generalize (prog_sectable p). *)
(*     unfold gen_sections, get_sections_size. *)
(*     intro s. intros; subst. simpl.  *)
(*     revert s x EQ. clear. *)
(*     induction s; simpl; intros; eauto. *)
(*     + inv EQ. reflexivity. *)
(*     + unfold acc_sections at 1 in EQ. monadInv EQ. *)
(*       apply IHs in EQ0. *)
(*       simpl. *)
(*       rewrite <- EQ0. *)
(*       rewrite fold_left_size_acc. *)
(*       cut (Z.of_nat (length x1) = sec_size a). omega. clear - EQ. *)
(*       unfold transl_section in EQ. destr_in EQ. inv EQ. simpl. auto. *)
(*   - apply gen_sections_length in EQ. setoid_rewrite <- EQ. *)
(*     apply Nat.eqb_eq in Heqb. *)
(*     rewrite Heqb. reflexivity. *)
(*   - Transparent check_sizes. *)
(*     exploit gen_sections_length; eauto. *)
(*     unfold gen_sections in EQ. destr_in EQ. *)
(*     apply Nat.eqb_eq in Heqb. *)
(*     rewrite Heqb. simpl length. intro A; inv A. *)
(*     destruct (prog_sectable p) eqn:Heqs; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence. *)
(*     destruct s; simpl in H11; try congruence.     *)
(*     simpl in H10. monadInv H10. *)
(*     monadInv EQ. *)
(*     monadInv EQ0. *)
(*     monadInv EQ3. *)
(*     monadInv EQ4. *)
(*     monadInv EQ5. *)
(*     monadInv EQ6. *)
(*     monadInv EQ7. *)
(*     monadInv EQ8. *)
(*     cbn. *)
(*     rewrite Heqs. *)
(*     unfold check_sizes. *)
(*     unfold get_section_size, get_sh_offset, SecTable.get. simpl.  *)
(*     repeat match goal with *)
(*              H: transl_section ?s = OK ?x |- _ => *)
(*              unfold transl_section in H; repeat destr_in H *)
(*            end. simpl. *)
(*     rewrite ! Z.eqb_refl. *)
(*     unfold get_sections_size. simpl. *)
(*     change elf_header_size with 52. *)
(*     rewrite !  (proj2 (Z.eqb_eq _ _)) by omega; auto. *)
(*   - reflexivity. *)
(* Qed. *)
