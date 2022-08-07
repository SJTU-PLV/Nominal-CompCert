Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Asm RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import RelocElf RelocElfgen.
Require Import SymbolString.
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode SymbtableDecode.
Require Import ReloctablesDecode.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.


Definition get_ptr64 (ef: elf_file) : bool:=
  match ef.(elf_head).(e_class) with
  | ELFCLASS32 => false
  | ELFCLASS64 => true
  | _ => false                   (* default *)
  end.

Section WITH_FLAG.

Variable elf64: bool.


Fixpoint id_from_strtbl_aux (l: list byte) (str: list byte) :=
  match l with
  | b :: l' =>
    if Byte.eq b HB["00"] then
      match string_to_ident str with
      | Some id =>
        OK (id,  l')
      | _ => Error (msg "get id from strtbl error")
      end        
    else id_from_strtbl_aux l' (str++[b])
  | _ => Error (msg "get id from strtbl error")
  end.
  
Definition id_from_strtbl (l: list byte) :=
  id_from_strtbl_aux [] l.

Record decode_elf_state :=
  { dec_sectable : sectable;
    dec_symbtable : symbtable;
    dec_reloctable: reloctable_map;
    dec_shstrtbl: list byte;
    dec_strtbl: list byte
  }.

Definition update_sectable_shstrtbl st id sec shstrtbl :=
  {| dec_sectable := PTree.set id sec st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

Definition update_reloctable_shstrtbl st id reloctbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := PTree.set id reloctbl st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

(* skip [".strtab"] *)
Definition update_strtbl st strtbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := strtbl
  |}.

(* skip [".symtab"] *)
Definition update_symbtable st symbtbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := symbtbl;
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

Definition acc_index_to_ident (acc: ZTree.t ident * Z) (id: ident) :=
  let (t, idx) := acc in
  (ZTree.set idx id t, idx + 1).

Definition index_to_ident (idl: list ident) (start: Z) :=
  fst (fold_left acc_index_to_ident idl (ZTree.empty ident, start)).


Program Fixpoint decode_symbtable_section (l:list byte) (m:ZTree.t ident) (strtbl: list byte) (symbtbl: symbtable) {measure (length l)} : res symbtable :=
  match l with
  | [] => OK symbtbl
  | _ =>
    let len := if elf64 then 24%nat else 16%nat in
    do (id, strtbl') <- id_from_strtbl strtbl;
    if elf64 then
      match take_drop len l with
      | OK (e, r) =>      
        do e <- decode_symbentry64 e m;
        decode_symbtable_section r m strtbl' (PTree.set id e symbtbl)
      | Error m => Error m
      end     
    else
      match take_drop len l with
      | OK (e, r) =>
        do e <- decode_symbentry32 e m;
        decode_symbtable_section r m strtbl' (PTree.set id e symbtbl)
      | Error m => Error m
      end
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply take_drop_length_2 in Heq_anonymous.
  auto.
  destr;lia.
Defined.
Next Obligation.
  symmetry in Heq_anonymous.
  apply take_drop_length_2 in Heq_anonymous.
  auto.
  destr;lia.
Defined.

Program Fixpoint decode_reloctable_section (l:list byte) (m:ZTree.t ident) (reloctbl: reloctable) {measure (length l)} : res reloctable :=
  match l with
  | [] => OK reloctbl
  | _ =>
    let len := if elf64 then 16%nat else 8%nat in
    match take_drop len l with
    | OK (e, r) =>
      do e <- decode_relocentry m e;
      decode_reloctable_section r m (reloctbl ++ [e])
    | Error m => Error m
    end
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply take_drop_length_2 in Heq_anonymous.
  auto.
  destr;lia.
Defined.

  
Definition acc_section_header (st: res decode_elf_state) (sec_h: section * section_header) :=
  do st <- st;
  let (sec, h) := sec_h in
  match h.(sh_type) with

  (* code and data *)
  | SHT_PROGBITS =>
    (* get section id *)
    do (id, shstrtbl') <- id_from_strtbl st.(dec_shstrtbl);
    match h.(sh_flags) with
    | [SHF_ALLOC] =>
      OK (update_sectable_shstrtbl st id (sec_rodata sec) shstrtbl')
    | [SHF_ALLOC; SHF_WRITE] =>
      OK (update_sectable_shstrtbl st id (sec_rwdata sec) shstrtbl')
    | [SHF_ALLOC; SHF_EXECINSTR] =>
      OK (update_sectable_shstrtbl st id (sec_text sec) shstrtbl')
    | _ => Error (msg "sh_flag error")
    end
       
  (* restore the strtbl in state*)
  (* shstrtbl impossible, since we removelast the shstrtbl header *)
  | SHT_STRTAB =>
    do (_, shstrtbl') <- take_drop (length strtab_str) st.(dec_shstrtbl);
    OK (update_strtbl st sec shstrtbl')
                  
  (* symbtable *)
  | SHT_SYMTAB =>
    (* get id to index map from sectable: Z -> ident *)
    let idl_sectbl := PTree.elements st.(dec_sectable) in
    let secidl := map fst idl_sectbl in
    let secidxmap := index_to_ident secidl 1 in
    (* iterate symbtable section and strtable simutaneously *)
    do symbtbl <- decode_symbtable_section sec secidxmap st.(dec_strtbl) (PTree.empty symbentry);
    do (_, shstrtbl') <- take_drop (length symtab_str) st.(dec_shstrtbl);
    OK (update_symbtable st symbtbl shstrtbl')
       
  | SHT_REL =>
    (* get id to index map from sectable: Z -> ident *)
    let idl_sectbl := PTree.elements st.(dec_sectable) in
    let secidl := map fst idl_sectbl in
    let secidxmap := index_to_ident secidl 1 in
    do (_, shstrtbl0) <- take_drop (length SB[".rel"]) st.(dec_shstrtbl);
    do (id, shstrtbl') <- id_from_strtbl shstrtbl0;
    do reloctbl <- decode_reloctable_section sec secidxmap [];
    OK (update_reloctable_shstrtbl st id reloctbl shstrtbl')
           
  | _ => Error (msg "unsupported section header")
  end.

End WITH_FLAG.

Definition init_dec_state shstrtbl :=
  {| dec_sectable := PTree.empty RelocProgramBytes.section;
     dec_symbtable := PTree.empty symbentry;
     dec_reloctable := PTree.empty reloctable;
     dec_shstrtbl := shstrtbl;
     dec_strtbl := [] |}.

Definition decode_elf (p: elf_file) : res program :=
  let init := init_dec_state (last p.(elf_sections) []) in
  let elf64 := get_ptr64 p in
  let secs := removelast p.(elf_sections) in
  let hs := tail (removelast p.(elf_section_headers)) in
  do st <- fold_left (acc_section_header elf64) (combine secs hs) (OK init);
  OK (Build_program _ _ _ _ p.(prog_defs) p.(prog_public) p.(prog_main) st.(dec_sectable) st.(dec_symbtable) st.(dec_reloctable) p.(prog_senv)).

