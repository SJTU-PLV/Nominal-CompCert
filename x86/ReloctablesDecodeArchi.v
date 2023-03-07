Require Import Coqlib Integers AST Maps.
Require Import Errors.
Require Import RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.
Require Import SymbtableDecode ReloctablesEncode.
Require Import RelocationTypes ReloctablesEncodeArchi.
Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope Z_scope.


(* Decoding of relocation typem. I do not know where to place *)
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

Section INFO_DECODE.
  Variable (encode_reloc_info: PTree.t Z -> reloctype -> ident -> res (list byte)).
  Variable decode_reloc_info: ZTree.t ident -> list byte -> res (reloctype * ident).

  Hypothesis encode_reloc_info_len: forall m r id bs,
    encode_reloc_info m r id = OK bs ->
    length bs = if Archi.ptr64 then 8%nat else 4%nat.
  
  Hypothesis decode_encode_reloc_info: forall bs rt symb m1 m2 (M: match_idxmap m1 m2),
    encode_reloc_info m1 rt symb = OK bs ->
    decode_reloc_info m2 bs = OK (rt, symb).

   
Definition decode_relocentry (elf64: bool) (m: ZTree.t ident) (l: list byte) : res relocentry :=
  if elf64 then
    do (ofsbytes, l) <- take_drop 8 l;
    do (infobytes, l) <- take_drop 8 l;
    do (addendbytes,_) <- take_drop 8 l;
    let ofs := decode_int ofsbytes in
    let addend := (decode_int addendbytes) in
    do (rt, sym) <- decode_reloc_info m infobytes;
    OK ({| reloc_offset := ofs; reloc_type := rt; reloc_symb := sym; reloc_addend := (if zlt addend (Z.pow 2 63) then addend else addend - (Z.pow 2 64)) |})
  else
    do (ofsbytes, l) <- take_drop 4 l;
    do (infobytes, l) <- take_drop 4 l;
    let ofs := decode_int ofsbytes in
    do (rt, sym) <- decode_reloc_info m infobytes;
    OK ({| reloc_offset := ofs; reloc_type := rt; reloc_symb := sym; reloc_addend := 0 |}).

Lemma decode_encode_relocentry: forall e m1 m2 bs (M:match_idxmap m1 m2),
    encode_relocentry m1 e = OK bs ->
    decode_relocentry Archi.ptr64 m2 bs = OK e.
Proof.
  unfold encode_relocentry,decode_relocentry.
  intros. repeat destr_in H.
  monadInv H11.
  unfold encode_int64.
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_length_app. cbn [bind2].
  rewrite take_drop_length. simpl. erewrite decode_encode_reloc_info;eauto.
  simpl. destruct e. simpl in *. 
  rewrite decode_encode_int. simpl.
  apply andb_true_iff in Heqb. destruct Heqb.
  rewrite Z.ltb_lt in H10.
  rewrite Z.leb_le in H.
  apply andb_true_iff in Heqb1. destruct Heqb1.
  rewrite Z.ltb_lt in H12.
  rewrite Z.leb_le in H11.
  
  rewrite Z.mod_small;auto.
  rewrite decode_encode_int.
  rewrite Z.mod_small;auto.
  unfold encode_reloc_info in EQ. repeat destr_in EQ.
  f_equal. repeat f_equal.
  destr.

  destruct (zlt reloc_addend 0).
  (* prove l is contradiction *)
  apply (Z.sub_lt_mono_l _ _ (Z.pow_pos 2 64)) in l.
  rewrite <- Z.mod_opp_l_nz in l;try lia.
  simpl in l.
  rewrite Z.mod_small in l;try lia.
  unfold not. intros. apply Z.mod_opp_l_z in H13.
  rewrite Z.mod_small in H13;try lia. lia.

  rewrite Z.mod_small;try lia.

  destruct (zlt reloc_addend 0).
  apply Z.opp_inj.
  rewrite Z.opp_sub_distr.
  rewrite Z.add_comm. rewrite Z.add_opp_r.
  rewrite <- Z.mod_opp_l_nz;try lia. rewrite Z.mod_small;try lia.

  rewrite Z.mod_small in g;try lia.

  unfold two_p. simpl. apply Z.mod_pos_bound.
  unfold two_power_pos. simpl. lia.

  rewrite encode_int_length. lia.

  unfold encode_reloc_info in EQ. repeat destr_in EQ.
  unfold encode_int64.   rewrite encode_int_length. auto.
  
  monadInv H11.

  monadInv H11.
  unfold encode_int32.
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_length. simpl. erewrite decode_encode_reloc_info;eauto.
  simpl. destruct e. simpl in *. 
  rewrite Z.eqb_eq in Heqb1. rewrite Heqb1.
  rewrite decode_encode_int. simpl.
  apply andb_true_iff in Heqb. destruct Heqb.
  rewrite Z.ltb_lt in H10.
  rewrite Z.leb_le in H.
  rewrite Z.mod_small;auto.
  unfold encode_reloc_info in EQ. repeat destr_in EQ. 
  unfold encode_int32. rewrite encode_int_length. auto.
  monadInv H11.
Qed.


End INFO_DECODE.
