Require Import Coqlib Integers String AST Maps.
Require Import Asm Errors.
Require Import RelocProg RelocProgram Encode.
Require Import Memdata.
Require Import Hex encode.Bits.
Import Hex Bits.
Import ListNotations.
Require Import SymbtableEncode.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope string_scope.

Definition decode_symbtype (z: Z) : res symbtype :=
  match z with
  | 0 => OK symb_notype
  | 1 => OK symb_data
  | 2 => OK symb_func
  | _ => Error (msg "decode_symbtype: Unexpected value for symbtype")
  end.

Lemma decode_encode_symbtype st:
  decode_symbtype (encode_symbtype st) = OK st.
Proof.
  destruct st; reflexivity.
Qed.


Definition decode_bindtype (z: Z) : res bindtype :=
  match z with
  | 0 => OK bind_local
  | 1 => OK bind_global
  | _ => Error (msg "decode_bindtype: Unexpected value for bindtype")
  end.

Lemma decode_encode_bindtype bt:
  decode_bindtype (encode_symbbind bt) = OK bt.
Proof.
  destruct bt; reflexivity.
Qed.


Definition decode_glob_symb_info (z: Z) :=
  let st := z mod 16 in
  let bt := z / 16 in
  do st <- decode_symbtype st;
    do bt <- decode_bindtype bt;
    OK (st, bt).

Lemma decode_encode_glob_symb_info st bt :
  decode_glob_symb_info (encode_glob_symb_info bt st) = OK (st, bt).
Proof.
  unfold decode_glob_symb_info, encode_glob_symb_info.
  change (2 ^ 4) with 16.
  rewrite Z.add_comm, Z_mod_plus_full, <- Z.add_comm.
  rewrite Z_div_plus_full_l by lia.
  rewrite Z.div_small, Z.mod_small, Z.add_0_r.
  rewrite decode_encode_symbtype, decode_encode_bindtype. reflexivity.
  destruct st; simpl; lia.
  destruct st; simpl; lia.
Qed.



Definition decode_secindex (lb: list byte) (m: ZTree.t ident) : res secindex :=
  let i := decode_int lb in
  if zeq i HZ["FFF2"]
  then OK secindex_comm
  else if zeq i 0
       then OK secindex_undef
       else
         match ZTree.get i m with
         | Some id =>
           OK (secindex_normal id)
         | _ => Error (msg "no ident in map to secindex")
         end.

Definition match_idxmap (m1:PTree.t Z) (m2: ZTree.t ident) :=
  forall id z (H: m1 ! id = Some z), ZTree.get z m2 = Some id.

Lemma decode_encode_secindex: forall i bs m1 m2 (M: match_idxmap m1 m2),    
    encode_secindex i m1 = OK bs ->
    decode_secindex bs m2 = OK i.
Proof.
  unfold decode_secindex, encode_secindex, match_idxmap.
  intros.
  destr_in H.
  - destr_in H. destr_in H.
    apply andb_true_iff in Heqb. simpl in Heqb.
    destruct Heqb as (A & B).
    apply Z.ltb_lt in A.  apply Z.ltb_lt in B.
    simpl. inv H. rewrite decode_encode_int.        
    simpl. rewrite Z.mod_small.
    rewrite pred_dec_false. rewrite pred_dec_false.
    erewrite M;eauto. lia. lia. change (two_power_pos 16) with 65536.
    lia.
  - inv H. rewrite decode_encode_int.
    simpl. auto.
  - inv H. rewrite decode_encode_int. 
    simpl. auto.
Qed.

Definition decode_symbentry32 (lb: list byte) (m: ZTree.t ident): res symbentry :=
  do (st_name_bytes, lb) <- take_drop 4 lb;
  do (st_value_bytes, lb) <- take_drop 4 lb;
  do (st_size_bytes, lb) <- take_drop 4 lb;
  do (st_info_bytes, lb) <- take_drop 1 lb;
  do (st_other_bytes, lb) <- take_drop 1 lb;
  do (st_shndx_bytes, lb) <- take_drop 2 lb;

  let svalue := decode_int32 st_value_bytes in
  let ssize := decode_int32 st_size_bytes in
  do (st, bt) <- decode_glob_symb_info (decode_int st_info_bytes);
  do secindex <- decode_secindex st_shndx_bytes m;
  OK (
      {|
        symbentry_bind := bt;
        symbentry_type := st;
        symbentry_value := svalue;
        symbentry_secindex := secindex;
        symbentry_size := ssize
      |}
    ).

Definition decode_symbentry64 (lb: list byte) (m: ZTree.t ident): res symbentry :=
  do (st_name_bytes, lb) <- take_drop 4 lb;
  do (st_info_bytes, lb) <- take_drop 1 lb;
  do (st_other_bytes, lb) <- take_drop 1 lb;
  do (st_shndx_bytes, lb) <- take_drop 2 lb;
  do (st_value_bytes, lb) <- take_drop 8 lb;
  do (st_size_bytes, lb) <- take_drop 8 lb;

  let svalue := decode_int st_value_bytes in
  let ssize := decode_int st_size_bytes in
  do (st, bt) <- decode_glob_symb_info (decode_int st_info_bytes);
  do secindex <- decode_secindex st_shndx_bytes m;
  OK (
      {|
        symbentry_bind := bt;
        symbentry_type := st;
        symbentry_value := svalue;
        symbentry_secindex := secindex;
        symbentry_size := ssize
      |}
    ).

Lemma decode_encode_symbentry32 : forall e bs nidx m1 m2 (M: match_idxmap m1 m2),
    encode_symbentry32 e nidx m1 = OK bs ->
    decode_symbentry32 bs m2 = OK e.
Proof.
  unfold encode_symbentry32,decode_symbentry32.
  intros. destr_in H.
  monadInv H.
  apply andb_true_iff in Heqb. destruct Heqb.
  apply andb_true_iff in H. destruct H.
  unfold check_range32 in *.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H11. destruct H11.
  apply andb_true_iff in H10. destruct H10.
  apply Z.leb_le in H.
  apply Z.leb_le in H11.
  apply Z.leb_le in H10.
  apply Z.ltb_lt in H12.
  apply Z.ltb_lt in H13.
  apply Z.ltb_lt in H14.

  unfold encode_int32.
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_cons. cbn [bind2].
  rewrite take_drop_length. cbn [bind2].
  rewrite decode_encode_int.
  rewrite Z.mod_small. rewrite decode_encode_glob_symb_info.
  simpl. erewrite decode_encode_secindex;eauto.
  simpl. destruct e. simpl in *.
  unfold decode_int32.
  repeat rewrite decode_encode_int.
  repeat rewrite Z.mod_small. auto.
  
  simpl in *.  lia.
  simpl in *.  lia.
  generalize (encode_glob_symb_info_range (symbentry_bind e) (symbentry_type e)). intros.
  simpl. rewrite two_power_pos_equiv. lia.
  eapply encode_secindex_len. eauto.
Qed.

  
Lemma decode_encode_symbentry64 : forall e bs nidx m1 m2 (M: match_idxmap m1 m2),
    encode_symbentry64 e nidx m1 = OK bs ->
    decode_symbentry64 bs m2 = OK e.
Proof.
  unfold encode_symbentry64,decode_symbentry64.
  intros. destr_in H.
  monadInv H.
  apply andb_true_iff in Heqb. destruct Heqb.
  apply andb_true_iff in H. destruct H.
  unfold check_range32 in *.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H11. destruct H11.
  apply andb_true_iff in H10. destruct H10.
  apply Z.leb_le in H.
  apply Z.leb_le in H11.
  apply Z.leb_le in H10.
  apply Z.ltb_lt in H12.
  apply Z.ltb_lt in H13.
  apply Z.ltb_lt in H14.

  unfold encode_int32, encode_int64.
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_cons. cbn [bind2].
  generalize (encode_secindex_len _ _ EQ). intros.
  rewrite (take_drop_length_app _  _ _ H15). cbn [bind2].
  rewrite take_drop_encode_int. cbn [bind2].
  rewrite take_drop_length. cbn [bind2].
  

  rewrite decode_encode_int.
  rewrite Z.mod_small. rewrite decode_encode_glob_symb_info.
  simpl. erewrite decode_encode_secindex;eauto.
  simpl. destruct e. simpl in *.
  repeat rewrite decode_encode_int.
  repeat rewrite Z.mod_small. auto.
  
  simpl in *.  lia.
  simpl in *.  lia.
  generalize (encode_glob_symb_info_range (symbentry_bind e) (symbentry_type e)). intros.
  simpl. rewrite two_power_pos_equiv. lia.
  apply encode_int_length.
Qed.


  
Admitted.

