Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import Asm RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import RelocElf RelocElfgen.
Require Import SymbolString.
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode SymbtableDecode.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.


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

Definition update_strtbl st strtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := st.(dec_shstrtbl);
     dec_strtbl := strtbl
  |}.

Definition update_symbtable st symbtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := symbtbl;
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := st.(dec_shstrtbl);
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
    let len := if Archi.ptr64 then 24%nat else 16%nat in
    do (id, strtbl') <- id_from_strtbl strtbl;
    if Archi.ptr64 then
      match take_drop len l with
      | OK (e, r) =>
        match lt_dec (length r) (length l) with
        | left _ => do e <- decode_symbentry64 e m;
                   decode_symbtable_section r m strtbl' (PTree.set id e symbtbl)
        | _ => Error (msg "impossible")
        end
        | Error m => Error m
        end     
    else
      match take_drop len l with
      | OK (e, r) =>
        match lt_dec (length r) (length l) with
        | left _ => do e <- decode_symbentry32 e m;
                   decode_symbtable_section r m strtbl' (PTree.set id e symbtbl)
        | _ => Error (msg "impossible")
        end
        | Error m => Error m
      end
  end.


Definition acc_section_header (st: decode_elf_state) (sec_h: section * section_header) :=
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
       
  (* restore the strtbl in state *)
  | SHT_STRTAB =>
    OK (update_strtbl st sec)
                  
  (* symbtable *)
  | SHT_SYMTAB =>
    (* get id to index map from sectable: Z -> ident *)
    let idl_sectbl := PTree.elements st.(dec_sectable) in
    let secidl := map fst idl_sectbl in
    let secidxmap := index_to_ident secidl 1 in
    (* iterate symbtable section and strtable simutaneously *)
    do symbtbl <- decode_symbtable_section sec secidxmap st.(dec_strtbl) (PTree.empty symbentry);
    OK (update_symbtable st symbtbl)
  | _ => Error (msg "unsupported section header")
  end.
 (*  | SHT_REL => *)
(*     encode_relocentry *)

(* Definition get_sectable: *)

(* firstn *)
(* partition *)
(*   filter *)
(*   LocalLib.list_norepet_filter_fst_pres *)

(* Definition decode_sections_table (ef: elf_file) : sectable := *)
  
