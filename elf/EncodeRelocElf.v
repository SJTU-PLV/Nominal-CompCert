(* Relocatable Elf Files *)
(* Author        : Yuting Wang *)
(* Date Created  : Sep-22-2019 *)

Require Import Coqlib Integers Maps Ascii.
Require Import Errors.
Require Import Encode.
Require Import Memdata.
Require Import RelocElf.
Require Import Asm.
Require Import Hex.
Import Hex.
Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope string_byte_scope.

(** * Encoding of the relocatble ELF files into bytes *)

Definition encode_e_ident (eh:elf_header) :=
  HB["7F"] :: CB["E"] :: CB["L"] :: CB["F"] ::
    (elf_class_to_byte (e_class eh)) ::
    (elf_data_to_byte (e_encoding eh)) ::
    (elf_version_to_byte (e_version eh)) ::
    (map (fun _ => Byte.zero) (seq 1 9)).
  

Definition encode_elf_header32 (eh:elf_header) :list byte := 
  (encode_e_ident eh) ++
  (encode_elf_file_type (e_type eh)) ++
  (encode_elf_machine (e_machine eh)) ++
  (encode_int32 (elf_version_value (e_version eh))) ++
  (encode_int32 (e_entry eh)) ++
  (encode_int32 (e_phoff eh)) ++
  (encode_int32 (e_shoff eh)) ++
  (encode_int32 (e_flags eh)) ++
  (encode_int16 (e_ehsize eh)) ++
  (encode_int16 (e_phentsize eh)) ++
  (encode_int16 (e_phnum eh)) ++
  (encode_int16 (e_shentsize eh))++
  (encode_int16 (e_shnum eh)) ++   
  (encode_int16  (e_shstrndx eh)).

Definition encode_elf_header64 (eh:elf_header) :list byte := 
  (encode_e_ident eh) ++
  (encode_elf_file_type (e_type eh)) ++
  (encode_elf_machine (e_machine eh)) ++
  (encode_int32 (elf_version_value (e_version eh))) ++
  (encode_int64 (e_entry eh)) ++
  (encode_int64 (e_phoff eh)) ++
  (encode_int64 (e_shoff eh)) ++
  (encode_int32 (e_flags eh)) ++
  (encode_int16 (e_ehsize eh)) ++
  (encode_int16 (e_phentsize eh)) ++
  (encode_int16 (e_phnum eh)) ++
  (encode_int16 (e_shentsize eh))++
  (encode_int16 (e_shnum eh)) ++   
  (encode_int16  (e_shstrndx eh)).

Definition encode_sections (ss:list section) :=
  fold_right (fun bytes r => bytes ++ r) [] ss.

Definition encode_section_header32 (sh: section_header) :=
  (encode_int32 (sh_name sh)) ++
  (encode_section_type (sh_type sh)) ++
  (encode_section_flags (sh_flags sh)) ++
  (encode_int32 (sh_addr sh)) ++
  (encode_int32 (sh_offset sh)) ++
  (encode_int32 (sh_size sh)) ++
  (encode_int32 (sh_link sh)) ++
  (encode_int32 (sh_info sh)) ++
  (encode_int32 (sh_addralign sh)) ++
  (encode_int32 (sh_entsize sh)).

Definition encode_section_header64 (sh: section_header) :=
  (encode_int32 (sh_name sh)) ++
  (encode_section_type (sh_type sh)) ++
  (encode_section_flags (sh_flags sh)) ++
  (encode_int64 (sh_addr sh)) ++
  (encode_int64 (sh_offset sh)) ++
  (encode_int64 (sh_size sh)) ++
  (encode_int32 (sh_link sh)) ++
  (encode_int32 (sh_info sh)) ++
  (encode_int64 (sh_addralign sh)) ++
  (encode_int64 (sh_entsize sh)).


Definition encode_section_headers (shs: list section_header) :=
  if Archi.ptr64 then
    fold_right (fun sh r => (encode_section_header64 sh) ++ r) [] shs
  else
    fold_right (fun sh r => (encode_section_header32 sh) ++ r) [] shs.
    

Definition encode_elf_file (ef: elf_file) : res (list byte * program * Globalenvs.Senv.t) :=
  if valid_elf_file_dec ef
  then
    let header := if Archi.ptr64 then encode_elf_header64 (elf_head ef) else encode_elf_header32 (elf_head ef) in
  let bs :=
      header ++
      (encode_sections (elf_sections ef)) ++
      (encode_section_headers (elf_section_headers ef)) in
  let p := {| AST.prog_defs   := RelocElf.prog_defs ef;
              AST.prog_public := RelocElf.prog_public ef;
              AST.prog_main   := RelocElf.prog_main ef; |} in
  OK (bs, p, prog_senv ef)
  else Error (msg "invalid elf file").
