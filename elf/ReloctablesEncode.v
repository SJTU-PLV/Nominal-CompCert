(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 21, 2019 *)
(* *******************  *)

(** * Encoding of the relocation tables into sections *)

Require Import Coqlib lib.Integers AST Maps.
Require Import Errors.
Require Import RelocProg Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(** Relocation entry definition:

    typedef struct {
      Elf32_Addr     r_offset;
      Elf32_Word     r_info;
    }

    typedef struct
    {       
      Elf64_Addr	r_offset;		/* Address */
      Elf64_Xword	r_info;			/* Relocation type and symbol index */
    } Elf64_Rel;
    

*)

Definition encode_reloctype (t:reloctype) :=
  match t with
  | reloc_null => 0     (* R_386_NONE *)
  | reloc_abs  => 1     (* R_386_32, addend 64bit in 64bit mode*)
  | reloc_rel  => 2     (* R_386_PC32, addend 32bit in 64bit mode*)
  end.

Section WITH_IDXMAP.
Variable  (idxmap: PTree.t Z).

Definition encode_reloc_info (t:reloctype) (symb:ident)  : res (list byte) :=
  let te := encode_reloctype t in
  match idxmap!symb with
  | None => Error [MSG "Relocation target symbol doesn't exist!"; CTX symb]
  | Some idx =>
    if Archi.ptr64 then
      OK (encode_int64 (idx * (Z.pow 2 32) + te))
    else
      OK (encode_int32 (idx * (Z.pow 2 8) + te))
  end.

Definition encode_relocentry (e:relocentry) : res (list byte) :=
  if Z.eqb (reloc_addend e) 0 then
    let r_offset_bytes := if Archi.ptr64 then encode_int64 (reloc_offset e)  else  encode_int32 (reloc_offset e) in
    do r_info_bytes <- encode_reloc_info (reloc_type e) (reloc_symb e);
    OK (r_offset_bytes ++ r_info_bytes)
  else Error [MSG "Relocation addend is not zero!";CTX (reloc_symb e)].

Definition acc_reloctable  acc e :=
  do acc' <- acc;
  do bs <- encode_relocentry e;
  OK (acc' ++ bs).

Definition encode_reloctable (t: list relocentry) : res (list byte) :=
    fold_left acc_reloctable t (OK []).

End WITH_IDXMAP.
(* Definition create_reloctable_section (t:reloctable) : section := *)
(*   let bytes := encode_reloctable t in *)
(*   sec_bytes bytes. *)
  

(* Definition create_reloctables_sections p : list section := *)
(*   [create_reloctable_section (reloctable_rodata (prog_reloctables p)); *)
(*   create_reloctable_section (reloctable_data (prog_reloctables p)); *)
(*   create_reloctable_section (reloctable_code (prog_reloctables p))]. *)

(* (** Transforma the program *) *)
(* Definition transf_program p : res program := *)
(*   let s := create_reloctables_sections p in *)
(*   let sect := prog_sectable p ++ s in *)
(*   if beq_nat (length sect) 9 then *)
(*     OK {| prog_defs := prog_defs p; *)
(*           prog_public := prog_public p; *)
(*           prog_main := prog_main p; *)
(*           prog_sectable := (prog_sectable p) ++ s; *)
(*           prog_strtable := (prog_strtable p); *)
(*           prog_symbtable := prog_symbtable p; *)
(*           prog_reloctables := prog_reloctables p; *)
(*           prog_senv := prog_senv p; *)
(*        |} *)
(*   else Error []. *)
