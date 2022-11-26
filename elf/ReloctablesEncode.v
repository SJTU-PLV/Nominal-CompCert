(** * Encoding of the relocation tables into sections *)

Require Import Coqlib lib.Integers AST Maps.
Require Import Errors.
Require Import RelocProg Encode RelocationTypes.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Require Import ReloctablesEncodeArchi.
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
      Elf64_Sxword	r_addend;		/* Addend */
    } Elf64_Rela;
    

*)

Section WITH_IDXMAP.
Variable  (idxmap: PTree.t Z).


Definition acc_reloctable  acc e :=
  do acc' <- acc;
  do bs <- encode_relocentry idxmap e;
  OK (acc' ++ bs).

Definition encode_reloctable (t: list relocentry) : res (list byte) :=
    fold_left acc_reloctable t (OK []).  
  
End WITH_IDXMAP.

