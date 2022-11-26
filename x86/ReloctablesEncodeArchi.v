(** * Encoding of the relocation tables into sections *)

Require Import Coqlib lib.Integers AST Maps.
Require Import Errors.
Require Import RelocProg Encode RelocationTypes.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Section WITH_IDXMAP.
Variable  (idxmap: PTree.t Z).

Definition encode_reloc_info (t:reloctype) (symb:ident)  : res (list byte) :=
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

Definition encode_relocentry (e:relocentry) : res (list byte) :=
  let len := if Archi.ptr64 then 64 else 32 in
  if (0 <=? e.(reloc_offset)) && (e.(reloc_offset) <? Z.pow 2 len) then
    let r_offset_bytes := if Archi.ptr64 then encode_int64 (reloc_offset e)  else  encode_int32 (reloc_offset e) in    
    do r_info_bytes <- encode_reloc_info (reloc_type e) (reloc_symb e);
    if Archi.ptr64 then
      if (- (Z.pow 2 63) <=? (reloc_addend e)) && ((reloc_addend e) <? (Z.pow 2 63)) then
        OK (r_offset_bytes ++ r_info_bytes ++ encode_int64 ((reloc_addend e) mod (Z.pow 2 64)))
      else
        Error [MSG "Reloc addend overflow in 64bit mode";CTX (reloc_symb e)]
    else
      if Z.eqb (reloc_addend e) 0 then
        OK (r_offset_bytes ++ r_info_bytes)
      else Error [MSG "Relocation addend is not zero in 32bit mode!";CTX (reloc_symb e)]
  else Error [MSG "Reloc offset overflow";CTX (reloc_symb e)].


Lemma encode_relocentry_len: forall l e,
    encode_relocentry e = OK l ->
    length l = if Archi.ptr64 then 24%nat else 8%nat.
Proof.
  unfold encode_relocentry.
  intros. repeat destr_in H.
  monadInv H11. unfold encode_reloc_info in EQ.
  repeat destr_in EQ.
  unfold encode_int64. repeat rewrite app_length.
  do 3 rewrite encode_int_length. lia.
  monadInv H11. unfold encode_reloc_info in H11.
  
  repeat destr_in H11.
  unfold encode_int32. rewrite app_length.
  do 2 rewrite encode_int_length. lia.
  monadInv H11.
Qed.

End WITH_IDXMAP.
