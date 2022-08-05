Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Asm RelocProg RelocProgram Encode.
Require Import Memdata.
Require Import RelocElf RelocElfgen.
Require Import SymbolString.
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.

Definition get_ptr64 (ef: elf_file) : res bool:=
  match ef.(elf_head).(e_class) with
  | ELFCLASS32 => OK false
  | ELFCLASS64 => OK true
  | _ => Error (msg "unable to figure out the ptr64")
  end.

Fixpoint id_from_strtbl_aux (l: list byte) (str: list byte) :=
  match l with
  | b :: l' =>
    if Byte.eq b HB["00"] then
      Some (string_to_ident str, Z.of_nat (length str), l')
    else id_from_strtbl_aux l' (str++[b])
  | _ => None
  end.
  
Definition id_from_strtbl (l: list byte) :=
  id_from_strtbl_aux [] l.

Record decode_elf_state :=
  { dec_sectable : sectable;
    dec_symbtable : symbtable;
    dec_reloctable: reloctable_map;
    dec_shstrtbl: list byte;
    dec_shstrtbl_ofs: Z;
    dec_strtbl: list byte;
    dec_sectype: PTree.t symb_type
  }.

Definition update_sectable_shstrtbl st id sec shstrtbl len :=
  {| dec_sectable := PTree.set id sec st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_shstrtbl_ofs := st.(dec_shstrtbl_ofs) + len;
     dec_strtbl := st.(dec_strtbl);
     dec_sectype := st.(dec_sectype)
  |}.

Definition update_strtbl st strtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := st.(dec_shstrtbl);
     dec_shstrtbl_ofs := st.(dec_shstrtbl_ofs);
     dec_strtbl := strtbl;
     dec_sectype := st.(dec_sectype)
  |}.


  
Definition acc_section_header (st: decode_elf_state) (sec_h: section * section_header) :=
  let (sec, h) := sec_h in
  match h.(sh_type) with

  (* code and data *)
  | SHT_PROGBITS =>
    (* get section id *)
    match id_from_strtbl st.(dec_shstrtbl) with
    | Some (id, len, shstrtbl') =>
      let st' := update_sectable_shstrtbl st id sec shstrtbl' len in
      match h.(sh_flags) with
      | 
    | None =>
      st
    end
  (* restore the strtbl in state *)
  | SHT_STRTAB =>
    update_strtbl st sec
                  
  (* symbtable *)
  | SHT_SYMTAB =>
    (* get id to index map from sectable *)
    let idl_sectbl := PTree.elements st.(dec_sectable) in
    let secidl := map fst idl_sectbl in
    let secidxmap := ident_to_index secidl 1 in
    (* iterate symbtable section and strtable simutaneously *)
    

Definition get_sectable:

firstn
partition
  filter
  LocalLib.list_norepet_filter_fst_pres

Definition decode_sections_table (ef: elf_file) : sectable :=
  
