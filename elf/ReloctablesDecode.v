Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.
Require Import SymbtableDecode ReloctablesEncode.
Require Import RelocationTypes ReloctablesEncodeArchi ReloctablesDecodeArchi.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope Z_scope.


Definition decode_reloc_info (m: ZTree.t ident) (lb: list byte) : res (reloctype * ident) :=
  if Archi.ptr64 then
    let z := decode_int lb in
    do rt <- decode_reloctype (z mod Z.pow 2 32);
    let symb := z / (Z.pow 2 32) in
    match ZTree.get symb m with
    | Some id =>
      OK (rt, id)
    | _ => Error (msg "no ident in decode_reloc_info")
    end
  else
    let z := decode_int lb in
    do rt <- decode_reloctype (z mod Z.pow 2 8);
    let symb := z / (Z.pow 2 8) in
    match ZTree.get symb m with
    | Some id =>
      OK (rt, id)
    | _ => Error (msg "no ident in decode_reloc_info")
    end.



Lemma decode_encode_reloc_info: forall bs rt symb m1 m2 (M: match_idxmap m1 m2),
    encode_reloc_info m1 rt symb = OK bs ->
    decode_reloc_info m2 bs = OK (rt, symb).
Proof.
  unfold decode_reloc_info, encode_reloc_info, match_idxmap.
  intros.
  destr_in H. apply M in Heqo.
  destr.
  - destr_in H.
    inv H. unfold encode_int64.
    rewrite decode_encode_int.
    simpl.
    rewrite Z.mod_small with (b:=two_p (Z.of_nat 64)).
    rewrite Z.add_comm. rewrite Z_mod_plus_full.
    rewrite Z.div_add.
    rewrite Z.div_small. rewrite Z.add_0_l.
    rewrite Z.mod_small.
    rewrite decode_encode_reloctype. simpl.
    rewrite Heqo. auto.
    destruct rt;simpl;lia.
    destruct rt;simpl;lia.
    apply andb_true_iff in Heqb0. destruct Heqb0.
    apply Z.ltb_lt in H10. apply Z.ltb_lt in H. lia.
    simpl.
    apply andb_true_iff in Heqb0. destruct Heqb0.
    apply Z.ltb_lt in H10. apply Z.ltb_lt in H.
    split.    
    destruct rt;simpl;lia.
    rewrite two_power_pos_equiv.
    destruct rt;simpl;lia.
  - destr_in H.
    inv H. unfold encode_int32.
    rewrite decode_encode_int.
    
    rewrite Z.mod_small with (b:=two_p (Z.of_nat 4*8)).
    rewrite Z.add_comm. rewrite Z_mod_plus_full.
    rewrite Z.div_add.
    rewrite Z.div_small. rewrite Z.add_0_l.
    rewrite Z.mod_small.
    rewrite decode_encode_reloctype. simpl.
    rewrite Heqo. auto.
    destruct rt;simpl;lia.
    destruct rt;simpl;lia.
    apply andb_true_iff in Heqb0. destruct Heqb0.
    apply Z.ltb_lt in H10. apply Z.ltb_lt in H. lia.
    simpl.
    apply andb_true_iff in Heqb0. destruct Heqb0.
    apply Z.ltb_lt in H10. apply Z.ltb_lt in H.
    split.    
    destruct rt;simpl;lia.
    rewrite two_power_pos_equiv.
    destruct rt;simpl;lia.

Qed.

Definition acc_decode_reloctable_section (reloclen: nat) (m: ZTree.t ident) (acc: res (reloctable * list byte * nat)) (b:byte) :=
  do acc' <- acc;
  let '(reloctbl, reloce, len) := acc' in
  if Nat.eq_dec len reloclen then
    do e <- decode_relocentry decode_reloc_info Archi.ptr64 m (reloce ++ [b]);
    OK (reloctbl ++ [e], [], 1%nat)
  else
    OK (reloctbl, reloce ++ [b], S len).
  
Definition decode_reloctable_section (reloclen: nat) (l: list byte) (m:ZTree.t ident) :=
  (* let reloclen := if Archi.ptr64 then 24%nat else 12%nat in *)
  do r <- fold_left (acc_decode_reloctable_section reloclen m) l (OK ([], [], 1%nat));
  OK (fst (fst r)).
