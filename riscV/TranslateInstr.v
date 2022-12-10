Require Import Coqlib Maps lib.Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm.
Require Import encode.Bits Memdata.
Require Import EncDecRet.
Require Import Coq.Logic.Eqdep_dec.
Import Bits.
Import ListNotations.
Require Import BPProperty.
Local Open Scope bits_scope.

Local Open Scope error_monad_scope.

Global Obligation Tactic := simpl;auto.

Fixpoint bits_of_int_rec (n: nat) (x: Z) {struct n}: list bool :=
  match n with
  | O => nil
  | S m => ((x mod 2)=?1) :: bits_of_int_rec m (x / 2)
  end.

Definition bits_of_int (n: nat) (x: Z) : list bool :=
  rev (bits_of_int_rec n x).

Lemma bits_of_int_length': forall n x,
  length(bits_of_int_rec n x)=n.
Proof.
  intro n. induction n.
  - auto.
  - simpl. intros. f_equal. apply IHn. Qed.

Lemma bits_of_int_length: forall n x,
  length(bits_of_int n x)=n.
Proof. unfold bits_of_int. intros.
  assert (length (rev (bits_of_int_rec n x))=
    length (bits_of_int_rec n x)). apply rev_length.
  rewrite H. apply bits_of_int_length'. Qed.

Fixpoint int_of_bits_rec (l: list bool): Z :=
  match l with
  | nil => 0
  | false :: l' =>  2 * (int_of_bits_rec l')
  | true  :: l' => 2 * (int_of_bits_rec l')+1
  end. 

Definition int_of_bits (l: list bool): Z :=
  int_of_bits_rec(rev l).

Lemma bits_of_int_consistency': forall n x l,
  -1 < x < two_power_nat n ->
  bits_of_int_rec n x = l ->
  int_of_bits_rec l = x.
Proof.
  induction n.
  - intros. rewrite <- H0. simpl. destruct H.
    unfold two_power_nat in H1. simpl in H1. lia.
  - intros. destruct (Z.even x) eqn: Heven.
    + assert (exists p : Z, x = 2 * p + (if Z.even x then 0 else 1)).
      { apply Zaux.Zeven_ex. }
      rewrite Heven in H1. destruct H1.
      rewrite <- Zred_factor6 in H1. rewrite H1 in H.
      simpl in H0. rewrite Zmod_even in H0. rewrite Heven in H0.
      simpl in H0. rewrite <- H0.
      assert (int_of_bits_rec (false :: bits_of_int_rec n (x / 2)) = 2 * int_of_bits_rec (bits_of_int_rec n (x / 2))).
      { simpl. reflexivity. }
      rewrite -> H2.
      destruct H. rewrite two_power_nat_S in H3.
      assert (-1 < x0 < two_power_nat n).
      { lia. }
      remember (bits_of_int_rec n (x / 2)) as l0. symmetry in Heql0.
      rewrite H1 in Heql0. rewrite Z.mul_comm in Heql0. 
      rewrite Z_div_mult_full in Heql0.
      remember (IHn x0 l0 H4 Heql0) as H5. rewrite H5.
      symmetry. apply H1. lia.
    + assert (exists p : Z, x = 2 * p + (if Z.even x then 0 else 1)).
      { apply Zaux.Zeven_ex. }
      rewrite Heven in H1. destruct H1. rewrite H1 in H.
      rewrite two_power_nat_S in H.
      assert (-1 < x0 < two_power_nat n).
      { lia. }
      simpl in H0. rewrite Zmod_even in H0. rewrite Heven in H0.
      simpl in H0. assert (int_of_bits_rec (true :: bits_of_int_rec n (x / 2)) = 2 * int_of_bits_rec (bits_of_int_rec n (x / 2)) + 1).
      { simpl. reflexivity. }
      rewrite <- H0. rewrite -> H3.
      remember (bits_of_int_rec n (x / 2)) as l0. symmetry in Heql0.
      rewrite H1 in Heql0. rewrite Z.mul_comm in Heql0. 
      assert ((x0 * 2 + 1) / 2 = x0).
      (* { remember (Z_div_mod_eq_full (x0 * 2 + 1) 2). *)
      { assert ((x0 * 2 + 1) mod 2 = 1).
        { rewrite Zmod_even. rewrite Z.mul_comm.
          rewrite <- H1. rewrite Heven. reflexivity. }
        assert (x0 * 2 + 1 = 2 * ((x0 * 2 + 1) / 2) + (x0 * 2 + 1) mod 2).
        { apply Z_div_mod_eq_full. lia. }
        rewrite H4 in H5. apply Z.add_cancel_r in H5.
        rewrite Z.mul_comm in H5.
        apply Z.mul_cancel_l in H5. symmetry in H5.
        rewrite Z.mul_comm. apply H5. lia. }
      rewrite H4 in Heql0. remember (IHn x0 l0 H2 Heql0) as H5.
      rewrite H5. rewrite H1. reflexivity.
Qed.

Lemma bits_of_int_consistency: forall n x l,
  -1 < x < two_power_nat n ->
  bits_of_int n x = l ->
  int_of_bits l = x.
Proof. 
  intros. unfold bits_of_int in H0. unfold int_of_bits.
  assert (rev (rev (bits_of_int_rec n x)) = rev l).
  { rewrite H0. reflexivity. }
  rewrite rev_involutive in H1.
  apply (bits_of_int_consistency' n x (rev l) H H1).
Qed.

  Lemma int_of_bits'_append: forall b l,
  int_of_bits_rec (l++[b])=
    if b then (two_power_nat (length l)) + int_of_bits_rec l
    else int_of_bits_rec l.
Proof.
  intros. generalize dependent b. induction l.
  - intros. destruct b; unfold two_power_nat; reflexivity.
  - intros. remember (length l) as n.
    replace (length (a :: l)) with (S n).
    rewrite two_power_nat_S.
    remember (int_of_bits_rec ((a :: l) ++ [b])) as LHS.
    simpl in HeqLHS. 
    replace (match int_of_bits_rec (l ++ [b]) with
    | 0 => 0
    | Z.pos y' => Z.pos y'~0
    | Z.neg y' => Z.neg y'~0
    end) with (2*(int_of_bits_rec (l ++ [b]))) in HeqLHS.
    replace (int_of_bits_rec (a :: l)) with 
    (if a then 2 * (int_of_bits_rec l) + 1
          else 2 * (int_of_bits_rec l)).
    rewrite IHl in HeqLHS.
    remember (two_power_nat n) as two_n.
    remember (int_of_bits_rec l) as x.
    destruct a eqn:HA; destruct b eqn:HB; lia.
    auto. auto. 
    simpl. rewrite Heqn. reflexivity. Qed.

Lemma int_of_bits_append: forall b l,
  int_of_bits (b::l)=
    if b then (two_power_nat (length l)) + int_of_bits l
    else int_of_bits l. 
Proof.
  unfold int_of_bits. intros.
  simpl.
  replace (length l) with (length (rev l)).
  apply (int_of_bits'_append b (rev l)).
  apply rev_length. Qed.

Lemma int_of_bits_range: forall l,
  -1 < int_of_bits l < two_power_nat (length l).
Proof. 
  intros. induction l.
  unfold int_of_bits , two_power_nat. simpl. lia.
  simpl. rewrite two_power_nat_S.
  remember (two_power_nat (length l)) as two_n eqn:H1.
  rewrite int_of_bits_append.
  destruct a; lia. Qed.

(* NEW: signed version of conversion between bits and ints *)
Definition bits_of_int_signed (n:nat) (ofs:Z) : res bits :=
  if ( 0 <=? ofs) && (ofs <? (two_power_nat (n-1))) then
    OK (bits_of_int n ofs)
  else
    if ( -(two_power_nat (n-1)) <=? ofs) && (ofs <? 0) then    
    OK (bits_of_int n (ofs + (two_power_nat n)))
    else Error (msg "Offset overflow in bits_of_int_signed").

Definition int_of_bits_signed (l: list bool): res Z :=
  match l with
  | nil => Error (msg "need at least a sign bit!")
  | false :: l' => OK (int_of_bits l')
  | true  :: l' => OK ((int_of_bits l') - two_power_nat (length l'))
  end.

Lemma bits_of_int_signed_consistency: forall n ofs l,
  n <> O ->
  bits_of_int_signed n ofs = OK l ->
  int_of_bits_signed l = OK ofs.
Proof.
  unfold bits_of_int_signed,int_of_bits_signed.
  intros. destruct n as [|n']. congruence.
  replace (two_power_nat (S n' - 1)) with (two_power_nat n') in *.
  do 1 destr_in H0; inversion H0.
  assert (length l = S n'). rewrite <- H2. apply bits_of_int_length.
  rewrite H2 in *.
  assert (ofs = int_of_bits l). {
    symmetry. apply (bits_of_int_consistency (S n')).
    eapply andb_true_iff in Heqb. destruct Heqb as [Heqb1 Heqb2].
    apply Z.leb_le in Heqb1. split. lia.
    apply Z.ltb_lt in Heqb2. rewrite two_power_nat_S.
    lia. auto. }
  destruct l;
  (* l=[] *)simpl in H1; try (congruence);
  injection H1 as H1. 
  destruct b;simpl;f_equal.
  (* ofs >= 0; sign=1, impossible *)
  rewrite int_of_bits_append in H3.
  rewrite H1 in *. 
  assert (-1 < int_of_bits l). apply int_of_bits_range.
  assert (ofs >= two_power_nat n'). lia. 
  eapply andb_true_iff in Heqb. destruct Heqb as [Heqb1 Heqb2].
  apply Z.ltb_lt in Heqb2. simpl in Heqb2. congruence.
  (* ofs >= 0; sign=0, ok *)
  rewrite int_of_bits_append in H3. rewrite H3. auto.
  
  do 1 destr_in H0. injection H0 as H0. 
  assert (length l = S n'). rewrite <- H0. apply bits_of_int_length.
  rewrite H0 in *. 
  assert (ofs + two_power_nat (S n')=int_of_bits l). 
    symmetry. apply (bits_of_int_consistency (S n')).
    assert (-1 < ofs + two_power_nat (S n') < two_power_nat (S n')).
    { eapply andb_true_iff in Heqb0. destruct Heqb0 as [Heqb1 Heqb2].
      apply Z.leb_le in Heqb1. apply Z.ltb_lt in Heqb2. 
      rewrite two_power_nat_S. lia. }
    apply H3. apply H0.

  destruct l as [|? l'];
  (* l=[] *)simpl in H1; try (congruence);
  injection H1 as H1.
  destruct b;simpl;f_equal.
  (* ofs <  0; sign=1, ok *)
  rewrite (two_power_nat_S n') in H3.
  rewrite int_of_bits_append in H3. rewrite H1 in *. lia.
  (* ofs <  0; sign=0, impossible *)
  eapply andb_true_iff in Heqb0. destruct Heqb0 as [Heqb1 Heqb2].
  apply Z.leb_le in Heqb1. apply Z.ltb_lt in Heqb2.
  rewrite int_of_bits_append in H3. rewrite two_power_nat_S in H3.
  assert (int_of_bits l' < two_power_nat n'). 
    rewrite <- H1. apply int_of_bits_range. 
  assert (ofs < - two_power_nat n'). lia. 
  assert (ofs >= - two_power_nat n'). lia.
  congruence.
  f_equal. lia. Qed.

Program Definition zero5  : u5  := b["00000"].
Program Definition zero12 : u12 := b["000000000000"].

(** * Encoding of instructions and functions *)

Program Definition encode_ireg (r: ireg) : res (u5) :=
  match r with
  | X1 => OK  (b["00001"])
  | X2 => OK  (b["00010"])
  | X3 => OK  (b["00011"])
  | X4 => OK  (b["00100"])
  | X5 => OK  (b["00101"])
  | X6 => OK  (b["00110"])
  | X7 => OK  (b["00111"])
  | X8 => OK  (b["01000"])
  | X9 => OK  (b["01001"])
  | X10 => OK (b["01010"])
  | X11 => OK (b["01011"])
  | X12 => OK (b["01100"])
  | X13 => OK (b["01101"])
  | X14 => OK (b["01110"])
  | X15 => OK (b["01111"])
  | X16 => OK (b["10000"])
  | X17 => OK (b["10001"])
  | X18 => OK (b["10010"])
  | X19 => OK (b["10011"])
  | X20 => OK (b["10100"])
  | X21 => OK (b["10101"])
  | X22 => OK (b["10110"])
  | X23 => OK (b["10111"])
  | X24 => OK (b["11000"])
  | X25 => OK (b["11001"])
  | X26 => OK (b["11010"])
  | X27 => OK (b["11011"])
  | X28 => OK (b["11100"])
  | X29 => OK (b["11101"])
  | X30 => OK (b["11110"])
  | X31 => OK (b["11111"])
  end.

Definition decode_ireg (bs: u5) : res ireg :=
    let bs' := proj1_sig bs in
    let n := bits_to_Z bs' in
    if      Z.eqb n 1  then OK(X1 )      (**r b["00001"] *)
    else if Z.eqb n 2  then OK(X2 )      (**r b["00010"] *)
    else if Z.eqb n 3  then OK(X3 )      (**r b["00011"] *)
    else if Z.eqb n 4  then OK(X4 )      (**r b["00100"] *)
    else if Z.eqb n 5  then OK(X5 )      (**r b["00101"] *)
    else if Z.eqb n 6  then OK(X6 )      (**r b["00110"] *)
    else if Z.eqb n 7  then OK(X7 )      (**r b["00111"] *)
    else if Z.eqb n 8  then OK(X8 )      (**r b["01000"] *)
    else if Z.eqb n 9  then OK(X9 )      (**r b["01001"] *)
    else if Z.eqb n 10 then OK(X10)      (**r b["01010"] *)
    else if Z.eqb n 11 then OK(X11)      (**r b["01011"] *)
    else if Z.eqb n 12 then OK(X12)      (**r b["01100"] *)
    else if Z.eqb n 13 then OK(X13)      (**r b["01101"] *)
    else if Z.eqb n 14 then OK(X14)      (**r b["01110"] *)
    else if Z.eqb n 15 then OK(X15)      (**r b["01111"] *)
    else if Z.eqb n 16 then OK(X16)      (**r b["10000"] *)
    else if Z.eqb n 17 then OK(X17)      (**r b["10001"] *)
    else if Z.eqb n 18 then OK(X18)      (**r b["10010"] *)
    else if Z.eqb n 19 then OK(X19)      (**r b["10011"] *)
    else if Z.eqb n 20 then OK(X20)      (**r b["10100"] *)
    else if Z.eqb n 21 then OK(X21)      (**r b["10101"] *)
    else if Z.eqb n 22 then OK(X22)      (**r b["10110"] *)
    else if Z.eqb n 23 then OK(X23)      (**r b["10111"] *)
    else if Z.eqb n 24 then OK(X24)      (**r b["11000"] *)
    else if Z.eqb n 25 then OK(X25)      (**r b["11001"] *)
    else if Z.eqb n 26 then OK(X26)      (**r b["11010"] *)
    else if Z.eqb n 27 then OK(X27)      (**r b["11011"] *)
    else if Z.eqb n 28 then OK(X28)      (**r b["11100"] *)
    else if Z.eqb n 29 then OK(X29)      (**r b["11101"] *)
    else if Z.eqb n 30 then OK(X30)      (**r b["11110"] *)
    else if Z.eqb n 31 then OK(X31)      (**r b["11111"] *)
    else Error(msg "reg not found")
  .

Theorem encode_ireg_consistency: forall ireg ireg_bits,
  encode_ireg ireg = OK (ireg_bits) ->
  decode_ireg ireg_bits = OK ireg.
Proof.
  unfold encode_ireg. unfold decode_ireg.
  intro ireg. destruct ireg; simpl; intros; inv H; simpl; eauto.
Qed.

Program Definition encode_ireg0 (r: ireg0) : res (u5) :=
  match r with
  | X0 => OK  (b["00000"])
  | X Xa => encode_ireg Xa
  end.


Definition decode_ireg0 (bs: u5) : res ireg0 :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if      Z.eqb n 0  then OK(X0 )        (**r b["00000"] *)
  else if Z.eqb n 1  then OK(X X1)       (**r b["00001"] *)
  else if Z.eqb n 2  then OK(X X2 )      (**r b["00010"] *)
  else if Z.eqb n 3  then OK(X X3 )      (**r b["00011"] *)
  else if Z.eqb n 4  then OK(X X4 )      (**r b["00100"] *)
  else if Z.eqb n 5  then OK(X X5 )      (**r b["00101"] *)
  else if Z.eqb n 6  then OK(X X6 )      (**r b["00110"] *)
  else if Z.eqb n 7  then OK(X X7 )      (**r b["00111"] *)
  else if Z.eqb n 8  then OK(X X8 )      (**r b["01000"] *)
  else if Z.eqb n 9  then OK(X X9 )      (**r b["01001"] *)
  else if Z.eqb n 10 then OK(X X10)      (**r b["01010"] *)
  else if Z.eqb n 11 then OK(X X11)      (**r b["01011"] *)
  else if Z.eqb n 12 then OK(X X12)      (**r b["01100"] *)
  else if Z.eqb n 13 then OK(X X13)      (**r b["01101"] *)
  else if Z.eqb n 14 then OK(X X14)      (**r b["01110"] *)
  else if Z.eqb n 15 then OK(X X15)      (**r b["01111"] *)
  else if Z.eqb n 16 then OK(X X16)      (**r b["10000"] *)
  else if Z.eqb n 17 then OK(X X17)      (**r b["10001"] *)
  else if Z.eqb n 18 then OK(X X18)      (**r b["10010"] *)
  else if Z.eqb n 19 then OK(X X19)      (**r b["10011"] *)
  else if Z.eqb n 20 then OK(X X20)      (**r b["10100"] *)
  else if Z.eqb n 21 then OK(X X21)      (**r b["10101"] *)
  else if Z.eqb n 22 then OK(X X22)      (**r b["10110"] *)
  else if Z.eqb n 23 then OK(X X23)      (**r b["10111"] *)
  else if Z.eqb n 24 then OK(X X24)      (**r b["11000"] *)
  else if Z.eqb n 25 then OK(X X25)      (**r b["11001"] *)
  else if Z.eqb n 26 then OK(X X26)      (**r b["11010"] *)
  else if Z.eqb n 27 then OK(X X27)      (**r b["11011"] *)
  else if Z.eqb n 28 then OK(X X28)      (**r b["11100"] *)
  else if Z.eqb n 29 then OK(X X29)      (**r b["11101"] *)
  else if Z.eqb n 30 then OK(X X30)      (**r b["11110"] *)
  else if Z.eqb n 31 then OK(X X31)      (**r b["11111"] *)
  else Error(msg "reg not found")
.

(*encode 64bit reg ,return *)
Program Definition encode_freg (r:freg) : res (u5):=
  match r with
  | F0 => OK  (b["00000"])
  | F1 => OK  (b["00001"])
  | F2 => OK  (b["00010"])
  | F3 => OK  (b["00011"])
  | F4 => OK  (b["00100"])
  | F5 => OK  (b["00101"])
  | F6 => OK  (b["00110"])
  | F7 => OK  (b["00111"])
  | F8 => OK  (b["01000"])
  | F9 => OK  (b["01001"])
  | F10 => OK (b["01010"])
  | F11 => OK (b["01011"])
  | F12 => OK (b["01100"])
  | F13 => OK (b["01101"])
  | F14 => OK (b["01110"])
  | F15 => OK (b["01111"])
  | F16 => OK (b["10000"])
  | F17 => OK (b["10001"])
  | F18 => OK (b["10010"])
  | F19 => OK (b["10011"])
  | F20 => OK (b["10100"])
  | F21 => OK (b["10101"])
  | F22 => OK (b["10110"])
  | F23 => OK (b["10111"])
  | F24 => OK (b["11000"])
  | F25 => OK (b["11001"])
  | F26 => OK (b["11010"])
  | F27 => OK (b["11011"])
  | F28 => OK (b["11100"])
  | F29 => OK (b["11101"])
  | F30 => OK (b["11110"])
  | F31 => OK (b["11111"])
end.

Definition decode_freg (bs: u5) : res freg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if      Z.eqb n 0  then OK(F0 )      (**r b["00000"] *)
  else if Z.eqb n 1  then OK(F1 )      (**r b["00001"] *)
  else if Z.eqb n 2  then OK(F2 )      (**r b["00010"] *)
  else if Z.eqb n 3  then OK(F3 )      (**r b["00011"] *)
  else if Z.eqb n 4  then OK(F4 )      (**r b["00100"] *)
  else if Z.eqb n 5  then OK(F5 )      (**r b["00101"] *)
  else if Z.eqb n 6  then OK(F6 )      (**r b["00110"] *)
  else if Z.eqb n 7  then OK(F7 )      (**r b["00111"] *)
  else if Z.eqb n 8  then OK(F8 )      (**r b["01000"] *)
  else if Z.eqb n 9  then OK(F9 )      (**r b["01001"] *)
  else if Z.eqb n 10 then OK(F10)      (**r b["01010"] *)
  else if Z.eqb n 11 then OK(F11)      (**r b["01011"] *)
  else if Z.eqb n 12 then OK(F12)      (**r b["01100"] *)
  else if Z.eqb n 13 then OK(F13)      (**r b["01101"] *)
  else if Z.eqb n 14 then OK(F14)      (**r b["01110"] *)
  else if Z.eqb n 15 then OK(F15)      (**r b["01111"] *)
  else if Z.eqb n 16 then OK(F16)      (**r b["10000"] *)
  else if Z.eqb n 17 then OK(F17)      (**r b["10001"] *)
  else if Z.eqb n 18 then OK(F18)      (**r b["10010"] *)
  else if Z.eqb n 19 then OK(F19)      (**r b["10011"] *)
  else if Z.eqb n 20 then OK(F20)      (**r b["10100"] *)
  else if Z.eqb n 21 then OK(F21)      (**r b["10101"] *)
  else if Z.eqb n 22 then OK(F22)      (**r b["10110"] *)
  else if Z.eqb n 23 then OK(F23)      (**r b["10111"] *)
  else if Z.eqb n 24 then OK(F24)      (**r b["11000"] *)
  else if Z.eqb n 25 then OK(F25)      (**r b["11001"] *)
  else if Z.eqb n 26 then OK(F26)      (**r b["11010"] *)
  else if Z.eqb n 27 then OK(F27)      (**r b["11011"] *)
  else if Z.eqb n 28 then OK(F28)      (**r b["11100"] *)
  else if Z.eqb n 29 then OK(F29)      (**r b["11101"] *)
  else if Z.eqb n 30 then OK(F30)      (**r b["11110"] *)
  else if Z.eqb n 31 then OK(F31)      (**r b["11111"] *)
  else Error(msg "reg not found")
.

Theorem encode_freg_consistency: forall freg freg_bits,
  encode_freg freg = OK (freg_bits) ->
  decode_freg freg_bits = OK freg.
Proof.
  unfold encode_freg. unfold decode_freg.
  intro freg. destruct freg; simpl; intros; inv H; simpl; eauto.
Qed.

Definition ofs_to_Z (ofs: offset) : res Z :=
  match ofs with
  | Ofsimm ptrofs =>
      OK (Ptrofs.signed ptrofs)
  | Ofslow _ _ => 
    Error (msg "offset not transferred")
  end.

Program Definition Z_to_ofs (z: Z) : res offset :=
  if (Ptrofs.min_signed <=? z) && (z <=? Ptrofs.max_signed) then
    OK (Ofsimm (Ptrofs.repr z))
  else Error (msg "Out of range").

Definition decode_ireg0_u5 (bs:u5) : res ireg0 :=
    match (proj1_sig bs) with
    | [false;false;false;false;false] => OK X0
    | _ => decode_ireg0 bs
    end.

Definition decode_ireg_u5 (bs:u5) : res ireg :=
    match (proj1_sig bs) with
    | [false;false;false;false;false] => Error (msg "X0 register unsupported")
    | _ => decode_ireg bs
    end.

(* Previous version: *)
(* Program Definition encode_ofs_u12 (ofs:Z) :res u12 :=  
  do ofs <- if ( -(two_power_nat 11) <=? ofs) && (ofs <? 0) then
             OK (ofs + (two_power_nat 12))
           else if ( 0 <=? ofs) && (ofs <? (two_power_nat 11)) then
                  OK ofs
                else Error (msg "Offset overflow in encode_ofs_u12");
  let ofs12 := (bits_of_int 12 ofs) in
  if assertLength ofs12 12 then
    OK (exist _ ofs12 _)
  else Error (msg "impossible"). *)
(* Definition decode_ofs_u12 (bs:u12) : res int :=
  let bs' := proj1_sig bs in
  match bs' with
  | b0 :: bs1 => 
      if b0 then OK (Int.repr ((int_of_bits bs') - two_power_nat 12)) 
        else OK (Int.repr (int_of_bits bs'))
  | nil => Error(msg "impossible")
  end. *)

(* New ddefinition of encode_ofs_u12 *)
Program Definition encode_ofs_u12 (ofs:Z) :res u12 :=
  let l0 := bits_of_int_signed 12 ofs in
  match l0 with
  | OK _ => 
      do l <- l0;
      if assertLength l 12 then
        OK (exist _ l _)
      else Error (msg "impossible")
  | Error _ => Error (msg "Offset overflow in encode_ofs_u12")
  end.

Definition decode_ofs_u12 (bs:u12) : res Z :=
  int_of_bits_signed (proj1_sig bs).

Lemma encode_ofs_u12_consistency:forall ofs l, 
    encode_ofs_u12 ofs = OK l ->
    decode_ofs_u12 l = OK ofs.
Proof.
  unfold encode_ofs_u12,decode_ofs_u12.
  intros. do 2 destr_in H.
  inversion Heqr.
  unfold bits_of_int_signed in H0.
  destruct ((0 <=? ofs) &&
  (ofs <? two_power_nat (12 - 1))) eqn:Ha.
  (* case sign = 0 *)
  apply bits_of_int_signed_consistency in Heqr.
  destruct l.
  cbn [proj1_sig].
  destruct (assertLength b 12) eqn:H3.
  inversion H1. subst. assumption.
  congruence. lia.
  (* case sign = 1  *)
  destruct ((- two_power_nat (12 - 1) <=? ofs) &&
  (ofs <? 0)) eqn: Hb.
  apply bits_of_int_signed_consistency in Heqr.
  destruct l.
  cbn [proj1_sig].
  destruct (assertLength b 12) eqn:H3.
  inversion H1. subst. assumption.
  congruence. lia. congruence. Qed.  

Program Definition encode_ofs_u5 (ofs:Z) :res u5 :=
  if ( -1 <? ofs) && (ofs <? (two_power_nat 5)) then
    let ofs5 := (bits_of_int 5 ofs) in
    if assertLength ofs5 5 then
      OK (exist _ ofs5 _)
    else Error (msg "impossible")
  else Error (msg "Offset overflow in encode_ofs_u5").

Definition decode_ofs_u5 (bs:u5) : res int :=
  let bs' := proj1_sig bs in
  OK (Int.repr (int_of_bits bs')).

Program Definition encode_ofs_u20 (ofs:Z) :res u20 :=
  let l0 := bits_of_int_signed 20 ofs in
  match l0 with
  | OK _ => 
      do l <- l0;
      if assertLength l 20 then
        OK (exist _ l _)
      else Error (msg "impossible")
  | Error _ => Error (msg "Offset overflow in encode_ofs_u20")
  end.

Definition decode_ofs_u20 (bs:u20) : res Z :=
  int_of_bits_signed (proj1_sig bs).


Lemma encode_ofs_u20_consistency:forall ofs l, 
    encode_ofs_u20 ofs = OK l ->
    decode_ofs_u20 l = OK ofs.
Proof.
  unfold encode_ofs_u20,decode_ofs_u20.
  intros. do 2 destr_in H.
  inversion Heqr.
  unfold bits_of_int_signed in H0.
  destruct ((0 <=? ofs) &&
  (ofs <? two_power_nat (20 - 1))) eqn:Ha.
  (* case sign = 0 *)
  apply bits_of_int_signed_consistency in Heqr.
  destruct l.
  cbn [proj1_sig].
  destruct (assertLength b 20) eqn:H3.
  inversion H1. subst. assumption.
  congruence. lia.
  (* case sign = 1  *)
  destruct ((- two_power_nat (20 - 1) <=? ofs) &&
  (ofs <? 0)) eqn: Hb.
  apply bits_of_int_signed_consistency in Heqr.
  destruct l.
  cbn [proj1_sig].
  destruct (assertLength b 20) eqn:H3.
  inversion H1. subst. assumption.
  congruence. lia. congruence. Qed.  

(* lui use unsigned offset as the upper 20bits (Asmgen.v)*)
Program Definition encode_ofs_u20_unsigned (ofs:Z) : res u20 :=
  if ( -1 <? ofs) && (ofs <? (two_power_nat 20)) then
  let bs := (bits_of_int 20 ofs) in
    if assertLength bs 20 then
      OK (exist _ bs _)
    else Error (msg "impossible")
  else Error (msg "Offset overflow in encode_ofs_u20").

  
Program Definition encode_S1 (imm: Z) : res u5 :=
  do immbits <- encode_ofs_u12 imm;
  let S1 := immbits>@[7] in
  if assertLength S1 5 then
    OK (exist _ S1 _)
  else Error(msg "illegal length in encode_S1").

Program Definition encode_S2 (imm: Z) : res u7 :=
  do immbits <- encode_ofs_u12 imm;
  let S2 := immbits~@[7] in
  if assertLength S2 7 then
    OK (exist _ S2 _)
  else Error(msg "illegal length in encode_S2").

(* subtle: we treat imm as an offset multiple of 2 bytes, so we need to preserve the least bit
   20     10:1          11         19:12  
   J4      J3           J2           J1
   ~@[1]  >@[10]    >@[9]~@[1]   >@[1]~@[8]
 *)
Program Definition encode_J1 (imm: Z) : res u8 :=
  do immbits <- encode_ofs_u20 imm;
  (* let B1_withtail := skipn 11 immbits in *)
  (* let B1 := firstn 8 B1_withtail in *)
  let B1 := immbits>@[1]~@[8] in
  if assertLength B1 8 then
    OK (exist _ B1 _)
  else Error(msg "illegal length in encode_J1").

Program Definition encode_J2 (imm: Z) : res u1 :=
  do immbits <- encode_ofs_u20 imm;
  (* let B1_withtail := skipn 10 immbits in *)
  (* let B1 := firstn 1 B1_withtail in *)
  let B1 := immbits>@[9]~@[1] in
  if assertLength B1 1 then
    OK (exist _ B1 _)
  else Error(msg "illegal length in encode_J2").

Program Definition encode_J3 (imm: Z) : res u10 :=
  do immbits <- encode_ofs_u20 imm;
  (* let B2 := firstn 10 immbits in *)
  let B2 := immbits>@[10] in
  if assertLength B2 10 then
    OK (exist _ B2 _)
  else Error(msg "illegal length in encode_J3").

Program Definition encode_J4 (imm: Z) : res u1 :=
  do immbits <- encode_ofs_u20 imm;
  (* let B1_withtail := skipn 19 immbits in *)
  (* let B1 := firstn 1 B1_withtail in *)
  let B1 := immbits~@[1] in
  if assertLength B1 1 then
    OK (exist _ B1 _)
  else Error(msg "illegal length in encode_J4").

Definition decode_immS (S1: u5) (S2: u7) : res Z :=
  let S1_bits := proj1_sig S1 in
  let S2_bits := proj1_sig S2 in
  OK (int_of_bits (S1_bits ++ S2_bits)).

Theorem encode_immS_consistency: forall Z S1 S2,
  encode_S1 Z = OK S1 -> encode_S2 Z = OK S2 ->
  decode_immS S1 S2 = OK Z.
Proof.
  unfold encode_S1, encode_S2, decode_immS.
  intros. Admitted.

(* subtle: we treat imm as an offset multiple of 2 bytes, so we need to preserve the least bit
   12     10:5          4:1          11
   B4      B3           B2           B1
   ~@[1]  >@[2]~[6]    >@[8]~@[4]   >@[1]~@[1]
*)

Program Definition encode_B1 (imm: Z) : res u1 :=
  do immbits <- encode_ofs_u12 imm;
  (* let B1_withtail := skipn 1 immbits in *)
  (* let B1 := firstn 1 B1_withtail in *)
  let B1 := immbits>@[1]~@[1] in
  if assertLength B1 1 then
    OK (exist _ B1 _)
  else Error(msg "illegal length in encode_B1").

Program Definition encode_B2 (imm: Z) : res u4 :=
  do immbits <- encode_ofs_u12 imm;
  (* let B2_withtail := skipn 8 immbits in *)
  (* let B2 := firstn 4 B2_withtail in *)
  let B2 := immbits>@[8]~@[4] in
  if assertLength B2 4 then
    OK (exist _ B2 _)
  else Error(msg "illegal length in encode_B2").

Program Definition encode_B3 (imm: Z) : res u6 :=
  do immbits <- encode_ofs_u12 imm;
  (* let B3_withtail := skipn 2 immbits in *)
  (* let B3 := firstn 6 B3_withtail in *)
  let B3 := immbits>@[2]~@[6] in
  if assertLength B3 6 then
    OK (exist _ B3 _)
  else Error(msg "illegal length in encode_B3").

Program Definition encode_B4 (imm: Z) : res u1 :=
  do immbits <- encode_ofs_u12 imm;
  (* let B4 := firstn 1 immbits in *)
  let B4 := immbits~@[1] in
  if assertLength B4 1 then
    OK (exist _ B4 _)
  else Error(msg "illegal length in encode_B4").

Definition decode_immB (B1: u1) (B2: u4) (B3: u6) (B4: u1) : res Z :=
  let B1_bits := proj1_sig B1 in
  let B2_bits := proj1_sig B2 in
  let B3_bits := proj1_sig B3 in
  let B4_bits := proj1_sig B4 in
  OK (int_of_bits (B2_bits ++ B3_bits ++ B1_bits ++ B4_bits)).

Theorem encode_immB_consistency: forall Z B1 B2 B3 B4,
  encode_B1 Z = OK B1 -> encode_B2 Z = OK B2 ->
  encode_B3 Z = OK B3 -> encode_B4 Z = OK B4 ->
  decode_immB B1 B2 B3 B4 = OK Z.
Proof.
  Admitted.

Program Definition encode_shamt ofs : res u6 :=
  if Archi.ptr64 then
    if ( -1 <? ofs) && (ofs <? (two_power_nat 6)) then
      let bs := (bits_of_int 6 ofs) in
      if assertLength bs 6 then
        OK (exist _ bs _)
      else Error (msg "impossible")
    else Error (msg "Offset overflow in encode_shamt")
  else
    if ( -1 <? ofs) && (ofs <? (two_power_nat 5)) then
      let bs := false :: (bits_of_int 5 ofs) in
      if assertLength bs 6 then
        OK (exist _ bs _)
      else Error (msg "impossible")
    else Error (msg "Offset overflow in encode_shamt").


Definition translate_instr' (i:instruction) : res (Instruction) :=
  match i with
  | Pnop =>
    OK (addi zero5 zero5 zero12)
  | Pjal_ofs rd (inr ofs) =>
    do rdbits <- encode_ireg0 rd;
    do J1 <- encode_J1 ofs;
    do J2 <- encode_J2 ofs;
    do J3 <- encode_J3 ofs;
    do J4 <- encode_J4 ofs;
    OK (jal rdbits J1 J2 J3 J4)
  | Pjal_rr rd rs ofs =>
    do rdbits <- encode_ireg0 rd;
    do rsbits <- encode_ireg0 rs;
    do imm <- encode_ofs_u12 ofs;
    OK (jalr rdbits rsbits imm)
  | Pauipc rd (inr ofs) =>
    do rdbits <- encode_ireg rd;
    do imm20  <- encode_ofs_u20_unsigned ofs;
    OK (auipc rdbits imm20)

  (** 32-bit integer register-immediate instructions *)
  | Paddiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    if Archi.ptr64 then
      OK (addiw rdbits rsbits imm12)
    else
      OK (addi rdbits rsbits imm12)
  | Psltiw rd rs imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int.signed imm);
      OK (slti rdbits rsbits imm12)
  | Psltiuw rd rs imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int.signed imm);
      OK (sltiu rdbits rsbits imm12)
  | Pandiw rd rs imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int.signed imm);
      OK (andi rdbits rsbits imm12)
  | Poriw rd rs imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int.signed imm);
      OK (ori rdbits rsbits imm12)
  | Pxoriw rd rs imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int.signed imm);
      OK (xori rdbits rsbits imm12)
  | Pslliw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    if Archi.ptr64 then
      do imm5  <- encode_ofs_u5 (Int.unsigned imm);
      OK (slliw rdbits rsbits imm5)
    else
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (slli rdbits rsbits imm6)
  | Psrliw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    if Archi.ptr64 then
      do imm5  <- encode_ofs_u5 (Int.unsigned imm);
      OK (srliw rdbits rsbits imm5)
    else
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (srli rdbits rsbits imm6)
  | Psraiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    if Archi.ptr64 then
      do imm5  <- encode_ofs_u5 (Int.unsigned imm);
      OK (sraiw rdbits rsbits imm5)
    else
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (srai rdbits rsbits imm6)
  | Pluiw rd imm =>
    if Archi.ptr64 then
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do imm20  <- encode_ofs_u20_unsigned (Int.signed imm);
      OK (lui rdbits imm20)

  (** 32-bit integer register-register instructions *)
  | Paddw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then 
      OK (addw rdbits rs1bits rs2bits)
    else 
      OK (add rdbits rs1bits rs2bits)
  | Psubw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then 
      OK (subw rdbits rs1bits rs2bits)
    else
      OK (sub rdbits rs1bits rs2bits)
  | Pmulw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then 
      OK (mulw rdbits rs1bits rs2bits)
    else
      OK (mul rdbits rs1bits rs2bits)
  | Pmulhw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (mulh rdbits rs1bits rs2bits)
  | Pmulhuw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (mulhu rdbits rs1bits rs2bits)
  | Pdivw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then
      OK (divw rdbits rs1bits rs2bits)
    else
      OK (div rdbits rs1bits rs2bits)
  | Pdivuw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then
      OK (divuw rdbits rs1bits rs2bits)
    else
      OK (divu rdbits rs1bits rs2bits)
  | Premw rd rs1 rs2 =>
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      if Archi.ptr64 then
        OK (remw rdbits rs1bits rs2bits)
      else 
        OK (rem rdbits rs1bits rs2bits)
  | Premuw rd rs1 rs2 =>
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;    
      if Archi.ptr64 then
        OK (remuw rdbits rs1bits rs2bits)
      else 
        OK (remu rdbits rs1bits rs2bits)
  | Psltw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (slt rdbits rs1bits rs2bits)
  | Psltuw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (sltu rdbits rs1bits rs2bits)
  | Pandw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (and rdbits rs1bits rs2bits)
  | Porw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (or rdbits rs1bits rs2bits)
  | Pxorw rd rs1 rs2 =>
    if Archi.ptr64 then 
      Error [MSG "Only in rv32: "; MSG (instr_to_string i)]
    else
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (xor rdbits rs1bits rs2bits)
  | Psllw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then
      OK (sllw rdbits rs1bits rs2bits)
    else
      OK (sll rdbits rs1bits rs2bits)
  | Psrlw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then
      OK (srlw rdbits rs1bits rs2bits)
    else
      OK (srl rdbits rs1bits rs2bits)
  | Psraw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    if Archi.ptr64 then
      OK (sraw rdbits rs1bits rs2bits)
    else
      OK (sra rdbits rs1bits rs2bits)

         
  (** 64-bit integer register-immediate instructions *)
  | Paddil rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (addi rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psltil rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (slti rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psltiul rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (sltiu rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pandil rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (andi rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Poril rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (ori rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pxoril rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm12  <- encode_ofs_u12 (Int64.signed imm);
      OK (xori rdbits rsbits imm12)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psllil rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (slli rdbits rsbits imm6)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psrlil rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (srli rdbits rsbits imm6)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psrail rd rs imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rsbits <- encode_ireg0 rs;
      do imm6  <- encode_shamt (Int.unsigned imm);
      OK (srai rdbits rsbits imm6)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pluil rd imm =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do imm20  <- encode_ofs_u20_unsigned (Int64.signed imm);
      OK (lui rdbits imm20)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]

  (* 64-bit integer register-register instructions *)
  | Paddl rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (add rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psubl rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (sub rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pmull rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (mul rdbits rs1bits rs2bits)
    else
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pmulhl rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (mulh rdbits rs1bits rs2bits)
    else
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pmulhul rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (mulhu rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pdivl rd rs1 rs2 =>
    if Archi.ptr64 then 
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (div rdbits rs1bits rs2bits)
    else
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pdivul rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (divu rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Preml rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (rem rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Premul rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (remu rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psltl rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (slt rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psltul rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (sltu rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pandl rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (and rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Porl rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (or rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pxorl rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (xor rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pslll rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (sll rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psrll rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (srl rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Psral rd rs1 rs2 =>
    if Archi.ptr64 then     
      do rdbits <- encode_ireg rd;
      do rs1bits <- encode_ireg0 rs1;
      do rs2bits <- encode_ireg0 rs2;
      OK (sra rdbits rs1bits rs2bits)
    else 
      Error [MSG "Only in rv64: "; MSG (instr_to_string i)]

    (* Conditional branches, 32-bit comparisons *)
  | Pbeq_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (beq B1 B2 rs1bits rs2bits B3 B4)
  | Pbne_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bne B1 B2 rs1bits rs2bits B3 B4)
  | Pblt_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (blt B1 B2 rs1bits rs2bits B3 B4)
  | Pbltu_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bltu B1 B2 rs1bits rs2bits B3 B4)
  | Pbge_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bge B1 B2 rs1bits rs2bits B3 B4)
  | Pbgeu_ofs rs1 rs2 ofs =>
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bgeu B1 B2 rs1bits rs2bits B3 B4)

  (* Loads and stores *)
  | Plb rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do ofsbits <- encode_ofs_u12 ofs_Z;
    OK (lb rdbits rabits ofsbits)
  | Plbu rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do ofsbits <- encode_ofs_u12 ofs_Z;
    OK (lbu rdbits rabits ofsbits)
  | Plh rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do ofsbits <- encode_ofs_u12 ofs_Z;
    OK (lh rdbits rabits ofsbits)
  | Plhu rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do ofsbits <- encode_ofs_u12 ofs_Z;
    OK (lhu rdbits rabits ofsbits)
  | Plw rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do ofsbits <- encode_ofs_u12 ofs_Z;
    OK (lw rdbits rabits ofsbits)
  | Pld rd ra ofs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rabits <- encode_ireg ra;
      do ofs_Z <- ofs_to_Z ofs;
      do ofsbits <- encode_ofs_u12 ofs_Z;
      OK (ld rdbits rabits ofsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
      
  | Psb rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (sb immS1bits rabits rdbits immS2bits)
  | Psh rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (sh immS1bits rabits rdbits immS2bits)
  | Psw rd ra ofs =>
    do rdbits <- encode_ireg rd;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (sw immS1bits rabits rdbits immS2bits)
  | Psd rd ra ofs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do rabits <- encode_ireg ra;
      do ofs_Z <- ofs_to_Z ofs;
      do immS1bits <- encode_S1 ofs_Z;
      do immS2bits <- encode_S2 ofs_Z;
      OK (sd immS1bits rabits rdbits immS2bits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
      
  (* floating point register move *)
  | Pfmv fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsgnjd fdbits fsbits fsbits)
  | Pfmvxs rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fmvxw rdbits fsbits)
  | Pfmvsx fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg rs;
    OK (fmvwx fdbits rsbits)
  | Pfmvxd rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fmvxd rdbits fsbits)
  | Pfmvdx fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg rs;
    OK (fmvdx fdbits rsbits)
  
  (* 32-bit (single-precision) floating point *)
  | Pfls fd ra ofs =>
    do fdbits <- encode_freg fd;
    do rabits <- encode_ireg0 ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immbits <- encode_ofs_u12 ofs_Z;
    OK (flw fdbits rabits immbits)
  | Pfss fs ra ofs =>
    do fsbits <- encode_freg fs;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (fsw immS1bits rabits fsbits immS2bits)
  | Pfnegs fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsgnjns fdbits fsbits fsbits)
  | Pfabss fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsgnjxs fdbits fsbits fsbits)
  | Pfadds fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fadds fdbits fs1bits fs2bits)
  | Pfsubs fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fsubs fdbits fs1bits fs2bits)
  | Pfmuls fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmuls fdbits fs1bits fs2bits)
  | Pfdivs fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fdivs fdbits fs1bits fs2bits)
  | Pfmins fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmins fdbits fs1bits fs2bits)
  | Pfmaxs fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmaxs fdbits fs1bits fs2bits)
  | Pfeqs rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (feqs rdbits fs1bits fs2bits)
  | Pflts rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (flts rdbits fs1bits fs2bits)
  | Pfles rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fles rdbits fs1bits fs2bits)
  | Pfsqrts fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsqrts fdbits fsbits)
  | Pfmadds fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fmadds fdbits fs1bits fs2bits fs3bits)
  | Pfmsubs fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fmsubs fdbits fs1bits fs2bits fs3bits)
  | Pfnmadds fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fnmadds fdbits fs1bits fs2bits fs3bits)
  | Pfnmsubs fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fnmsubs fdbits fs1bits fs2bits fs3bits)
  | Pfcvtws rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fcvtws rdbits fsbits)
  | Pfcvtwus rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fcvtwus rdbits fsbits)
  | Pfcvtsw fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtsw fdbits rsbits)
  | Pfcvtswu fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtswu fdbits rsbits)
  
  | Pfcvtls rd fs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do fsbits <- encode_freg fs;
      OK (fcvtls rdbits fsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtlus rd fs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do fsbits <- encode_freg fs;
      OK (fcvtlus rdbits fsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtsl fd rs =>
    if Archi.ptr64 then
      do fdbits <- encode_freg fd;
      do rsbits <- encode_ireg0 rs;
      OK (fcvtsl fdbits rsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtslu fd rs =>
    if Archi.ptr64 then
      do fdbits <- encode_freg fd;
      do rsbits <- encode_ireg0 rs;
      OK (fcvtslu fdbits rsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  
  (* 64-bit (double-precision) floating point *)
  | Pfld fd ra ofs =>
    do fdbits <- encode_freg fd;
    do rabits <- encode_ireg0 ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immbits <- encode_ofs_u12 ofs_Z;
    OK (fload fdbits rabits immbits)
  | Pfsd fs ra ofs =>
    do fsbits <- encode_freg fs;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (fsd immS1bits rabits fsbits immS2bits)
  | Pfnegd fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsgnjnd fdbits fsbits fsbits)
  | Pfabsd fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsgnjxd fdbits fsbits fsbits)
  | Pfaddd fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (faddd fdbits fs1bits fs2bits)
  | Pfsubd fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fsubd fdbits fs1bits fs2bits)
  | Pfmuld fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmuld fdbits fs1bits fs2bits)
  | Pfdivd fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fdivd fdbits fs1bits fs2bits)
  | Pfmind fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmind fdbits fs1bits fs2bits)
  | Pfmaxd fd fs1 fs2 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fmaxd fdbits fs1bits fs2bits)
  | Pfeqd rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (feqd rdbits fs1bits fs2bits)
  | Pfltd rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fltd rdbits fs1bits fs2bits)
  | Pfled rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    OK (fled rdbits fs1bits fs2bits)
  | Pfsqrtd fd fs =>
    do fdbits <- encode_freg fd;
    do fsbits <- encode_freg fs;
    OK (fsqrtd fdbits fsbits)
  | Pfmaddd fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fmaddd fdbits fs1bits fs2bits fs3bits)
  | Pfmsubd fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fmsubd fdbits fs1bits fs2bits fs3bits)
  | Pfnmaddd fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fnmaddd fdbits fs1bits fs2bits fs3bits)
  | Pfnmsubd fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg fd;
    do fs1bits <- encode_freg fs1;
    do fs2bits <- encode_freg fs2;
    do fs3bits <- encode_freg fs3;
    OK (fnmsubd fdbits fs1bits fs2bits fs3bits)
  | Pfcvtwd rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fcvtwd rdbits fsbits)
  | Pfcvtwud rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg fs;
    OK (fcvtwud rdbits fsbits)
  | Pfcvtdw fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtdw fdbits rsbits)
  | Pfcvtdwu fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtdwu fdbits rsbits)

  | Pfcvtld rd fs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do fsbits <- encode_freg fs;
      OK (fcvtld rdbits fsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtlud rd fs =>
    if Archi.ptr64 then
      do rdbits <- encode_ireg rd;
      do fsbits <- encode_freg fs;
      OK (fcvtlud rdbits fsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtdl fd rs =>
    if Archi.ptr64 then
      do fdbits <- encode_freg fd;
      do rsbits <- encode_ireg0 rs;
      OK (fcvtdl fdbits rsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]
  | Pfcvtdlu fd rs =>
    if Archi.ptr64 then
      do fdbits <- encode_freg fd;
      do rsbits <- encode_ireg0 rs;
      OK (fcvtdlu fdbits rsbits)
    else Error [MSG "Only in rv64: "; MSG (instr_to_string i)]

  | Pfcvtds fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_freg rs;
    OK (fcvtds fdbits rsbits)
  | Pfcvtsd fd rs =>
    do fdbits <- encode_freg fd;
    do rsbits <- encode_freg rs;
    OK (fcvtsd fdbits rsbits)

  | _ => Error [MSG "Not exists or unsupported: "; MSG (instr_to_string i)]
  end.

Definition translate_instr i := do i' <- translate_instr' i; OK [i'].

(* FIXME: for the big endian output for the multi-bytes token in CSLED *)
Definition bits_to_bytes_archi bs := do bs' <- (bits_to_bytes bs); OK (rev bs').

(* Decode;struction *)

(* Broken due to the shamt *)
  (* NEW *)
(* Definition decode_instr_rv32 (i: Instruction) : res instruction := *)
(*   match i with *)
(*   | addi rdbits rsbits imm12 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u12 imm12; *)
(*     OK (Asm.Paddiw rd rs imm) *)
(*   | slti rdbits rsbits imm12 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u12 imm12; *)
(*     OK (Asm.Psltiw rd rs imm) *)
(*   | andi rdbits rsbits imm12 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u12 imm12; *)
(*     OK (Asm.Pandiw rd rs imm) *)
(*   | ori rdbits rsbits imm12 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u12 imm12; *)
(*     OK (Asm.Poriw rd rs imm) *)
(*   | xori rdbits rsbits imm12 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u12 imm12; *)
(*     OK (Asm.Pxoriw rd rs imm) *)
(*   | slli rdbits rsbits imm5 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u5 imm5; *)
(*     OK (Asm.Pslliw rd rs imm) *)
(*   | srli rdbits rsbits imm5 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u5 imm5; *)
(*     OK (Asm.Psrliw rd rs imm) *)
(*   | srai rdbits rsbits imm5 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do rs  <- decode_ireg0_u5 rsbits; *)
(*     do imm <- decode_ofs_u5 imm5; *)
(*     OK (Asm.Psraiw rd rs imm) *)
(*   | lui rdbits imm20 => *)
(*     do rd  <- decode_ireg_u5 rdbits; *)
(*     do imm <- decode_ofs_u20 imm20; *)
(*     OK (Asm.Pluiw rd imm) *)
(*   | add rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Paddw rd rs1 rs2) *)
(*   | sub rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psubw rd rs1 rs2) *)
(*   | mul rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pmulw rd rs1 rs2) *)
(*   | mulh rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pmulhw rd rs1 rs2) *)
(*   | mulhu rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pmulhuw rd rs1 rs2) *)
(*   | div rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pdivw rd rs1 rs2) *)
(*   | divu rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pdivuw rd rs1 rs2) *)
(*   | rem rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Premw rd rs1 rs2) *)
(*   | remu rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Premuw rd rs1 rs2) *)
(*   | slt rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psltw rd rs1 rs2) *)
(*   | sltu rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psltuw rd rs1 rs2) *)
(*   | and rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pandw rd rs1 rs2) *)
(*   | xor rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Pxorw rd rs1 rs2) *)
(*   | sll rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psllw rd rs1 rs2) *)
(*   | srl rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psrlw rd rs1 rs2) *)
(*   | sra rdbits rs1bits rs2bits => *)
(*     do rd  <- decode_ireg_u5 rdbits ; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Asm.Psraw rd rs1 rs2) *)
(*   | beq immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pbeq_ofs rs1 rs2 ofs_Z) *)
(*   | bne immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pbne_ofs rs1 rs2 ofs_Z) *)
(*   | blt immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pblt_ofs rs1 rs2 ofs_Z) *)
(*   | bltu immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pbltu_ofs rs1 rs2 ofs_Z) *)
(*   | bge immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pbge_ofs rs1 rs2 ofs_Z) *)
(*   | bgeu immB1 immB2 rs1bits rs2bits immB3 immB4 => *)
(*     do ofs_Z <- decode_immB immB1 immB2 immB3 immB4; *)
(*     do rs1 <- decode_ireg0_u5 rs1bits; *)
(*     do rs2 <- decode_ireg0_u5 rs2bits; *)
(*     OK (Pbgeu_ofs rs1 rs2 ofs_Z) *)
(*   | lb rdbits rabits ofs_bits => *)
(*     do rd <- decode_ireg_u5 rdbits; *)
(*     do ra <- decode_ireg_u5 rabits; *)
(*     do ofs_int <- decode_ofs_u12 ofs_bits; *)
(*     do ofs <- Z_to_ofs (Int.intval ofs_int); *)
(*     OK (Asm.Plb rd ra ofs) *)
(*   | lbu rdbits rabits ofs_bits => *)
(*     do rd <- decode_ireg_u5 rdbits; *)
(*     do ra <- decode_ireg_u5 rabits; *)
(*     do ofs_int <- decode_ofs_u12 ofs_bits; *)
(*     do ofs <- Z_to_ofs (Int.intval ofs_int); *)
(*     OK (Asm.Plbu rd ra ofs) *)
(*   | lh rdbits rabits ofs_bits => *)
(*     do rd <- decode_ireg_u5 rdbits; *)
(*     do ra <- decode_ireg_u5 rabits; *)
(*     do ofs_int <- decode_ofs_u12 ofs_bits; *)
(*     do ofs <- Z_to_ofs (Int.intval ofs_int); *)
(*     OK (Asm.Plh rd ra ofs) *)
(*   | lhu rdbits rabits ofs_bits => *)
(*     do rd <- decode_ireg_u5 rdbits; *)
(*     do ra <- decode_ireg_u5 rabits; *)
(*     do ofs_int <- decode_ofs_u12 ofs_bits; *)
(*     do ofs <- Z_to_ofs (Int.intval ofs_int); *)
(*     OK (Asm.Plhu rd ra ofs) *)
(*   | lw rdbits rabits ofs_bits => *)
(*     do rd <- decode_ireg_u5 rdbits; *)
(*     do ra <- decode_ireg_u5 rabits; *)
(*     do ofs_int <- decode_ofs_u12 ofs_bits; *)
(*     do ofs <- Z_to_ofs (Int.intval ofs_int); *)
(*     OK (Asm.Plw rd ra ofs) *)
(*   | _ => Error (msg "unsupported") *)
(*   end. *)
