(* Relocatable Elf Files *)
(* Author        : Yuting Wang *)
(* Date Created  : Sep-22-2019 *)

Require Import Coqlib Integers Maps.
Require Import AST Asm Archi.
Require Import Errors.
Require Import Encode.
Require Import Memdata.
Require Import Hex.
Import Hex.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.

(** * Definition of the relocatable ELF files *)

Definition elf_header_size := if ptr64 then 64 else 52.
Definition prog_header_size := if ptr64 then 56 else 32.
Definition sec_header_size  := if ptr64 then 64 else 40.
Definition symb_entry_size := if ptr64 then 24 else 16.
(** for simplicity , only support SHT_REL*)
Definition reloc_entry_size := if ptr64 then 16 else 8.


(** ** ELF header *)

(** File class *)
Inductive elf_file_class : Type := 
| ELFCLASSNONE 
| ELFCLASS32  (** 32-bit file *) 
| ELFCLASS64  (** 64-bit file *)
.

Definition elf_class_value cls :=
  match cls with
  | ELFCLASSNONE => 0
  | ELFCLASS32 => 1
  | ELFCLASS64 => 2
  end.

Definition elf_class_to_byte cls :=
  Byte.repr (elf_class_value cls).

(** Encoding data format *)
Inductive elf_data :Type := 
| ELFDATANONE 
| ELFDATA2LSB   (** little endian *) 
| ELFDATA2MSB   (** big endian *)
.

Definition elf_data_value ecd :=
  match ecd with
  | ELFDATANONE => 0
  | ELFDATA2LSB => 1
  | ELFDATA2MSB => 2
  end.

Definition elf_data_to_byte ecd := 
  Byte.repr (elf_data_value ecd).

(** Version info *)
Inductive elf_version : Type :=
| EV_NONE
| EV_CURRENT.

Definition elf_version_value ev :=
  match ev with
  | EV_NONE => 0
  | EV_CURRENT => 1
  end.

Definition elf_version_to_byte ev :=
  Byte.repr (elf_version_value ev).

(** File type
    We only support relocatable Elf *)
Inductive elf_file_type : Type := 
| ET_REL    (* Relocatable *)
.

Definition elf_file_type_value typ :=
  match typ with
  | ET_REL => 1
  end.

Definition encode_elf_file_type typ :=
  encode_int 2 (elf_file_type_value typ).

(** Machine architecture 
    We only support x86-32 for now *)
(** Update: support x86-64 now*)
Inductive elf_machine :Type := 
| EM_386
| EM_x86_64.

Definition elf_machine_value m :=
  match m with
  | EM_386 => 3
  | EM_x86_64 => 62
  end.

Definition encode_elf_machine m :=
  encode_int 2 (elf_machine_value m).

(** 32 and 64 bit have the same file header structure  *)
Record elf_header : Type :=
{
    e_class      : elf_file_class;
    e_encoding   : elf_data;
    e_version   : elf_version;
    e_type       : elf_file_type;
    e_machine    : elf_machine;
    e_entry      : Z; (* entry point of the program, 4 or 8 bytes *)
    e_phoff      : Z; (* offset to the first program header, 4 or 8 bytes*)
    e_shoff      : Z; (* offset to the first section header , 4 or 8 bytes*)
    e_flags      : Z; 
    e_ehsize     : Z; (* size of the elf header, i.e., 52 of 64 bytes *)
    e_phentsize  : Z; (* size of a program header *)
    e_phnum      : Z; (* number of program headers *)
    e_shentsize  : Z; (* size of a section header *)
    e_shnum      : Z; (* number of section headers *)
    e_shstrndx   : Z; (* index to the section header for the string table *)
}.


(* indexes to the array e_ident *)
Definition ei_mag0 := 0.
Definition ei_mag1 := 1.
Definition ei_mag2 := 2.
Definition ei_mag3 := 3.
Definition ei_class := 4.
Definition ei_data := 5.
Definition ei_version := 6.
Definition ei_pad := 7.
Definition ei_size := 16.


(** ** Section Header Table *)
Inductive section_type := 
| SHT_NULL
| SHT_PROGBITS  (* program *)
| SHT_STRTAB    (* string table *)
| SHT_SYMTAB    (* symbol table *)
| SHT_REL       (* relocation table *)
| SHT_RELA      (* relocation table with explicit addends *)
| SHT_NOBITS    (* unintialized data *)
.

Definition section_type_value sht :=
  match sht with
  | SHT_NULL => 0
  | SHT_PROGBITS => 1
  | SHT_STRTAB => 3
  | SHT_SYMTAB => 2
  | SHT_REL    => 9
  | SHT_RELA   => 4
  | SHT_NOBITS => 8
  end.

Definition encode_section_type sht :=
  encode_int32 (section_type_value sht).

Inductive section_flag := 
| SHF_WRITE       (* writable section *)
| SHF_ALLOC       (* section will be allocated in memory *)
| SHF_EXECINSTR   (* executable section *)
.

Definition section_flag_value flag :=
  match flag with
  | SHF_WRITE => 1
  | SHF_ALLOC => 2
  | SHF_EXECINSTR => 4
  end.

Definition encode_section_flags flags :=
  let vl := map section_flag_value flags in
  let v := fold_left (fun acc v => acc + v) vl 0 in
  if ptr64 then
    encode_int64 v
  else
    encode_int32 v.


Record section_header :=
{
  sh_name        : Z;   (* offset in the string table to the name of the section *)
  sh_type        : section_type; 
  sh_flags       : list section_flag;
  sh_addr        : Z;   (* starting address of the section in the memory *)
  sh_offset      : Z;   (* offset to the beginning of the section in the file *)
  sh_size        : Z;   (* size of the section *)
  sh_link        : Z;   (* when sh_type is STH_REL, it contains 
                           the section header index of the associated symbol table *)
  sh_info        : Z;   (* when sh_type is STH_REL, it contains 
                           the section header index of the section to which the relocation applies *)
  sh_addralign   : Z;   (* alignment of the section *)
  sh_entsize     : Z;   (* size of each entry in this section *)
}.

(* let sec_header_to_bytes sh little_endian = *)
(*   (int32_to_bytes sh.sh_name little_endian) @ *)
(*   (int32_to_bytes (sec_type_to_int32 sh.sh_type) little_endian) @ *)
(*   (int32_to_bytes (sec_flags_to_int32 sh.sh_flags) little_endian) @ *)
(*   (int32_to_bytes sh.sh_addr little_endian) @ *)
(*   (int32_to_bytes sh.sh_offset little_endian) @ *)
(*   (int32_to_bytes sh.sh_size little_endian) @ *)
(*   (int32_to_bytes 0 little_endian) @ (* link *) *)
(*   (int32_to_bytes 0 little_endian) @ (* info *) *)
(*   (int32_to_bytes sh.sh_addralign little_endian) @  *)
(*   (int32_to_bytes 0 little_endian) (* entsize *) *)

Definition null_section_header := 
  {|
    sh_name       := 0;
    sh_type       := SHT_NULL;
    sh_flags      := [];
    sh_addr       := 0;
    sh_offset     := 0;
    sh_size       := 0;
    sh_link       := 0;
    sh_info       := 0;
    sh_addralign  := 0;
    sh_entsize    := 0;
  |}.


(** ** Symbol table entry *)

(** Binding of the symbol.
    We only support global symbol for the moment *)
Inductive symb_binding :=
| STB_GLOBAL.

Definition symb_binding_value b := 
  match b with
  | STB_GLOBAL => 1
  end.

Definition encode_symb_binding b :=
  encode_int32 (symb_binding_value b).

(** Symbol type *)
Inductive symb_type :=
| STT_NOTYPE
| STT_OBJECT
| STT_FUNC
.

Definition symb_type_value t :=
  match t with
  | STT_NOTYPE => 0
  | STT_OBJECT => 1
  | STT_FUNC => 2
  end.

(** Symbol entries *)
Record symb_entry :=
{
  st_name   : Z;   (** Index into the symbol string table *)
  st_value  : Z;   
  st_size   : Z;
  st_bind   : symb_binding;
  st_type   : symb_type;
  st_other  : Z;
  st_shndx  : Z    (** Index into the section header table *)
}.

(** ** Reloc entries with addenddum *)
Record reloc_entry (rel_type:Type) :=
{
  r_offset : Z;   (** Offset to the relocation location *)
  r_symb   : Z;   (** Index to the symbol table *)
  r_type   : rel_type;  (** Relocation type is processor specific *)
  r_addend : Z;   (** addenddum *)
}.
  
(** ** ELF file *)

Definition section := list byte.

Record elf_file :=
{
  (** The definitions are kept for defining the semantics
      of external functions *)
  prog_defs: list (ident * (AST.globdef fundef unit));
  prog_public: list ident;
  prog_main: ident;
  prog_senv: Globalenvs.Senv.t;
  
  elf_head         : elf_header;           (** ELF header *)
  elf_sections     : list section;        (** Sections *)
  elf_section_headers : list section_header  (** Section headers *)
}.


Record valid_elf_header (eh: elf_header) :=
  {
    valid_entry: 0 <= e_entry eh < two_p (if ptr64 then 64 else  32);
    valid_phoff: 0 <= e_phoff eh < two_p (if ptr64 then 64 else  32);
    valid_shoff: 0 <= e_shoff eh < two_p (if ptr64 then 64 else  32);
    valid_flags: 0 <= e_flags eh < two_p 32;
    valid_ehsize: 0 <= e_ehsize eh < two_p 16;
    valid_phentsize: 0 <= e_phentsize eh < two_p 16;
    valid_phnum: 0 <= e_phnum eh < two_p 16;
    valid_shentsize: 0 <= e_shentsize eh < two_p 16;
    valid_shnum: 0 <= e_shnum eh < two_p 16;
    valid_shstrndx: 0 <= e_shstrndx eh < two_p 16;
  }.


Notation " 'check' A ; B" := (if A then B else Error nil) (at level 100).


Fixpoint check_sizes shs (ss: list section) ofs :=
  match shs, ss with
  | [], [] => OK tt
  | sh::shs, s::ss =>
    check (Z.eqb (sh_size sh) (Z.of_nat (length s)));
      check (Z.eqb (sh_offset sh) ofs);
      check_sizes shs ss (ofs + Z.of_nat (length s))
  | _, _ => Error (msg "Should be as much sections as section headers")
  end.

Inductive valid_section_flags : list section_flag -> Prop :=
| vsf_nil : valid_section_flags []
| vsf_alloc : valid_section_flags [SHF_ALLOC]
| vsf_alloc_write : valid_section_flags [SHF_ALLOC; SHF_WRITE]
| vsf_alloc_exec : valid_section_flags [SHF_ALLOC; SHF_EXECINSTR].


Record valid_section_header sh :=
  {
    vsh_name: 0 <= sh_name sh < two_p 32;
    vsh_addr: 0 <= sh_addr sh < two_p (if ptr64 then 64 else 32);
    vsh_offset: 0 <= sh_offset sh < two_p (if ptr64 then 64 else 32);
    vsh_size: 0 <= sh_size sh < two_p (if ptr64 then 64 else 32);
    vsh_link: 0 <= sh_link sh < two_p 32;
    vsh_info: 0 <= sh_info sh < two_p 32;
    vsh_addralign: 0 <= sh_addralign sh < two_p (if ptr64 then 64 else 32);
    vsh_entsize: 0 <= sh_entsize sh < two_p (if ptr64 then 64 else 32);
    vsh_flags: valid_section_flags (sh_flags sh);
  }.

Record valid_elf_file ef :=
  {
    vef_header: valid_elf_header (elf_head ef);
    vef_shs: Forall valid_section_header (elf_section_headers ef);
    vef_shoff: e_shoff (elf_head ef) = elf_header_size + fold_right (fun s acc => acc + Z.of_nat (length s)) 0 (elf_sections ef);
    vef_shnum: e_shnum (elf_head ef) = Z.of_nat (length (elf_section_headers ef));
    vef_check_sizes:
      check_sizes (tl (elf_section_headers ef)) (elf_sections ef) elf_header_size = OK tt;
    vef_first_section_null:
      nth_error (elf_section_headers ef) O = Some null_section_header;
 }.

Lemma intv_dec: forall lo hi x, {lo <= x < hi} + {~ lo <= x < hi}.
Proof.
  intros.
  destruct (zle lo x). 2: right; intro A; lia.
  destruct (zlt x hi). left; lia. right; intro A; lia.
Defined.

Lemma valid_section_flags_dec: forall l, {valid_section_flags l} + { ~ valid_section_flags l}.
Proof.
  destruct l. left; constructor.
  destruct l. destruct s. right. intro A. inv A.
  left. constructor. right. intro A. inv A.
  destruct s. right; intro A; inv A.
  destruct l. 2: right; intro A; inv A.
  destruct s0; try (right; intro A; inv A; fail); left; try constructor.
  right; intro A; inv A.
Defined.

Lemma valid_elf_header_dec: forall eh, {valid_elf_header eh} + {~ valid_elf_header eh}.
Proof.
  intros.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (e_entry eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (e_phoff eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (e_shoff eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 32) (e_flags eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_ehsize eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_phentsize eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_phnum eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_shentsize eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_shnum eh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 16) (e_shstrndx eh)). 2: right; intro A; inv A; lia.
  left; constructor; auto.
Defined.

Lemma valid_section_header_dec: forall sh, {valid_section_header sh} + {~ valid_section_header sh}.
Proof.
  intros.
  destruct (intv_dec 0 (two_p 32) (sh_name sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (sh_addr sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (sh_offset sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (sh_size sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 32) (sh_link sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p 32) (sh_info sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (sh_addralign sh)). 2: right; intro A; inv A; lia.
  destruct (intv_dec 0 (two_p (if ptr64 then 64 else 32)) (sh_entsize sh)). 2: right; intro A; inv A; lia.
  destruct (valid_section_flags_dec (sh_flags sh)). 2: right; intro A; inv A; congruence.
  left; constructor; auto.
Defined.

Lemma section_header_dec: forall sh1 sh2 : section_header, {sh1 = sh2} + {sh1 <> sh2}.
Proof.
  intros.
  decide equality; try apply zeq.
  apply list_eq_dec. intros; decide equality.
  decide equality.
Defined.

Lemma valid_elf_file_dec: forall ef, {valid_elf_file ef} + {~ valid_elf_file ef}.
Proof.
  intros.
  destruct (valid_elf_header_dec (elf_head ef)). 2: right; intro A; inv A; congruence.
  destruct (Forall_dec _ (valid_section_header_dec) (elf_section_headers ef)).
  2: right; intro A; inv A; congruence.
  destruct (zeq (e_shoff (elf_head ef)) (elf_header_size + fold_right (fun s acc => acc + Z.of_nat (length s)) 0 (elf_sections ef))).
  2: right; intro A; inv A; congruence.
  destruct (zeq (e_shnum (elf_head ef)) (Z.of_nat (length (elf_section_headers ef)))).
  2: right; intro A; inv A; congruence.
  destruct (check_sizes (tl (elf_section_headers ef)) (elf_sections ef) elf_header_size) eqn:?.
  2: right; intro A; inv A; congruence.
  destruct u.
  destruct (nth_error (elf_section_headers ef) 0) eqn:NTH.
  2: right; intro A; inv A; congruence.
  destruct (section_header_dec s null_section_header). subst.
  2: right; intro A; inv A; congruence.
  left; constructor; auto.
Defined.
