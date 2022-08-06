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
  do (st_value_bytes, lb) <- take_drop 8 lb;
  do (st_size_bytes, lb) <- take_drop 8 lb;
  do (st_info_bytes, lb) <- take_drop 1 lb;
  do (st_other_bytes, lb) <- take_drop 1 lb;
  do (st_shndx_bytes, lb) <- take_drop 2 lb;

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
Admitted.
