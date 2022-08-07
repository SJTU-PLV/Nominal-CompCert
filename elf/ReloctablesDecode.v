Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.
Require Import SymbtableDecode ReloctablesEncode.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope Z_scope.

Definition decode_reloctype (z: Z) : res reloctype :=
  match z with
  | 0 => OK reloc_null
  | 1 => OK reloc_abs
  | 2 => OK reloc_rel
  | _ => Error (msg "decode_reloctype: Unexpected value for symbtype")
  end.

Lemma decode_encode_reloctype rt:
  decode_reloctype (encode_reloctype rt) = OK rt.
Proof. destruct rt; reflexivity. Qed.

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

Definition decode_relocentry (m: ZTree.t ident) (l: list byte) : res relocentry :=
  if Archi.ptr64 then
    do (ofsbytes, l) <- take_drop 8 l;
    do (infobytes, l) <- take_drop 8 l;
    let ofs := decode_int ofsbytes in
    do (rt, sym) <- decode_reloc_info m infobytes;
    OK ({| reloc_offset := ofs; reloc_type := rt; reloc_symb := sym; reloc_addend := 0 |})
  else
    do (ofsbytes, l) <- take_drop 4 l;
    do (infobytes, l) <- take_drop 4 l;
    let ofs := decode_int ofsbytes in
    do (rt, sym) <- decode_reloc_info m infobytes;
    OK ({| reloc_offset := ofs; reloc_type := rt; reloc_symb := sym; reloc_addend := 0 |}).
