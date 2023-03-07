(** * Encoding of the relocation tables into sections *)

Require Import Coqlib lib.Integers AST Maps.
Require Import Errors.
Require Import RelocProg Encode RelocationTypes.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Require Import LocalLib.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Section WITH_IDXMAP.
Variable  (idxmap: PTree.t Z).
Variable (encode_reloc_info: PTree.t Z -> reloctype -> ident -> res (list byte)).

Hypothesis encode_reloc_info_len: forall m r id bs,
    encode_reloc_info m r id = OK bs ->
    length bs = if Archi.ptr64 then 8%nat else 4%nat.


Definition encode_relocentry (e:relocentry) : res (list byte) :=
  let len := if Archi.ptr64 then 64 else 32 in
  if (0 <=? e.(reloc_offset)) && (e.(reloc_offset) <? Z.pow 2 len) then
    let r_offset_bytes := if Archi.ptr64 then encode_int64 (reloc_offset e)  else  encode_int32 (reloc_offset e) in    
    do r_info_bytes <- encode_reloc_info idxmap (reloc_type e) (reloc_symb e);
    if Archi.ptr64 then
      if (- (Z.pow 2 63) <=? (reloc_addend e)) && ((reloc_addend e) <? (Z.pow 2 63)) then
        OK (r_offset_bytes ++ r_info_bytes ++ encode_int64 ((reloc_addend e) mod (Z.pow 2 64)))
      else
        Error [MSG "Reloc addend overflow in 64bit mode";CTX (reloc_symb e)]
    else
      if (- (Z.pow 2 31) <=? (reloc_addend e)) && ((reloc_addend e) <? (Z.pow 2 31)) then
        OK (r_offset_bytes ++ r_info_bytes ++ encode_int32 ((reloc_addend e) mod (Z.pow 2 32)))
      else
        Error [MSG "Reloc addend overflow in 32bit mode";CTX (reloc_symb e)]

  else Error [MSG "Reloc offset overflow";CTX (reloc_symb e)].

Lemma encode_relocentry_len: forall l e,
    encode_relocentry e = OK l ->
    length l = if Archi.ptr64 then 24%nat else 12%nat.
Proof.
  unfold encode_relocentry.
  intros. repeat destr_in H.  
  monadInv H11. 
  unfold encode_int64. repeat rewrite app_length.
  exploit encode_reloc_info_len;eauto;intros INFOLEN;rewrite INFOLEN.
  do 2 rewrite encode_int_length. lia.
  
  monadInv H11.

  monadInv H11. unfold encode_int32. repeat rewrite app_length.
  exploit encode_reloc_info_len;eauto;intros INFOLEN;try rewrite INFOLEN.
  do 2 rewrite encode_int_length. lia.

  monadInv H11. 
Qed.  

End WITH_IDXMAP.





    
