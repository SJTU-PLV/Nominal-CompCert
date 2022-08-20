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
  (* destruct  *)
  (* Z.mod_opp_opp *)
  admit. admit.
  admit. admit.
  (* rewrite Z.mod_small;try lia. *)
  (* simpl. unfold two_power_pos. simpl. lia. *)
  (* rewrite encode_int_length. auto. *)
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
Admitted.

