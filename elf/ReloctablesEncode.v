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

Definition encode_reloc_info (idxmap: PTree.t Z) (t:reloctype) (symb:ident)  : res (list byte) :=
  let te := encode_reloctype t in
  match idxmap!symb with
  | None => Error [MSG "Relocation target symbol doesn't exist!"; CTX symb]
  | Some idx =>
    if Archi.ptr64 then
      if (0 <? idx) && (idx <? Z.pow 2 32) then
        OK (encode_int64 (idx * (Z.pow 2 32) + te))
      else Error (msg "Overflow in encode_reloc_info")
    else
      if (0 <? idx) && (idx <? Z.pow 2 24) then
        OK (encode_int32 (idx * (Z.pow 2 8) + te))
      else Error (msg "Overflow in encode_reloc_info")
  end.

Lemma encode_reloc_info_len: forall m r id bs,
    encode_reloc_info m r id = OK bs ->
    length bs = if Archi.ptr64 then 8%nat else 4%nat.
Proof.
  unfold encode_reloc_info.
  intros. repeat destr_in H.
  - unfold encode_int64.
    eapply encode_int_length.
  - unfold encode_int32.
    eapply encode_int_length.
Qed.


Section WITH_IDXMAP.
Variable  (idxmap: PTree.t Z).

    
Definition acc_reloctable  acc e :=
  do acc' <- acc;
  do bs <- encode_relocentry idxmap encode_reloc_info e;
  OK (acc' ++ bs).

Definition encode_reloctable (t: list relocentry) : res (list byte) :=
    fold_left acc_reloctable t (OK []).  
  
End WITH_IDXMAP.

