Require Import Coqlib Integers String Ascii.

Module Hex.


Inductive hex_base :=
| H0 | H1 | H2 | H3 | H4 | H5 | H6 | H7 | H8 | H9 | A | B | C | D | E | F.

Definition hex := list hex_base.

Definition char_to_hex_base (a: ascii) : hex_base :=
  if ascii_dec a "0" then 
    H0
  else if ascii_dec a "1" then
    H1
  else if ascii_dec a "2" then
    H2
  else if ascii_dec a "3" then
    H3
  else if ascii_dec a "4" then
    H4
  else if ascii_dec a "5" then
    H5
  else if ascii_dec a "6" then
    H6
  else if ascii_dec a "7" then
    H7
  else if ascii_dec a "8" then
    H8
  else if ascii_dec a "9" then
    H9
  else if ascii_dec a "A" then
    A
  else if ascii_dec a "B" then
    B
  else if ascii_dec a "C" then
    C
  else if ascii_dec a "D" then
    D
  else if ascii_dec a "E" then
    E
  else if ascii_dec a "F" then
    F
  else
    H0.


Fixpoint string_to_hex (s: string): hex :=
  match s with
  | EmptyString => nil
  | String a s' => 
    (char_to_hex_base a) :: (string_to_hex s')
  end.

Definition hex_base_to_char (hb: hex_base) : ascii :=
  match hb with
  | H0 => "0"
  | H1 => "1"
  | H2 => "2"
  | H3 => "3"
  | H4 => "4"
  | H5 => "5"
  | H6 => "6"
  | H7 => "7"
  | H8 => "8"
  | H9 => "9"
  | A => "A"
  | B => "B"
  | C => "C"
  | D => "D"
  | E => "E"
  | F => "F"
  end.


Fixpoint hex_to_string (h: hex) :=
  match h with
  | nil => EmptyString
  | h' :: ht =>
    String (hex_base_to_char h') (hex_to_string ht)
  end.

Notation "H[ str ]" := (string_to_hex str) : hex_scope.

(* Translate hexadecimals to integers *)

Definition hex_base_to_Z (h: hex_base) :=
  match h with
  | H0 => 0
  | H1 => 1
  | H2 => 2
  | H3 => 3
  | H4 => 4
  | H5 => 5
  | H6 => 6
  | H7 => 7
  | H8 => 8
  | H9 => 9
  | A => 10
  | B => 11
  | C => 12
  | D => 13
  | E => 14
  | F => 15
  end.

Fixpoint hex_to_Z (h: hex) : Z :=
  let fix aux acc h :=
      match h with
      | nil => acc
      | h1 :: ht => 
        aux (acc*16 + (hex_base_to_Z h1)) ht
      end
  in aux 0 h.

Definition N_to_hex_base (n:N) (_: (n < 16)%N) : hex_base :=
  if N.eq_dec n 0 then
    H0
  else if N.eq_dec n 1 then
    H1
  else if N.eq_dec n 2 then
    H2
  else if N.eq_dec n 3 then
    H3
  else if N.eq_dec n 4 then
    H4
  else if N.eq_dec n 5 then
    H5
  else if N.eq_dec n 6 then
    H6
  else if N.eq_dec n 7 then
    H7
  else if N.eq_dec n 8 then
    H8
  else if N.eq_dec n 9 then
    H9
  else if N.eq_dec n 10 then
    A
  else if N.eq_dec n 11 then
    B
  else if N.eq_dec n 12 then
    C
  else if N.eq_dec n 13 then
    D
  else if N.eq_dec n 14 then
    E
  else 
    F.

Program Fixpoint N_to_hex_acc (n:nat) (i: N) (acc:list hex_base) : list hex_base :=
  match n with
  | O => acc
  | S n' => 
    let b := (i mod 16)%N in
    let r := (i / 16)%N in
    let h := N_to_hex_base b _ in
    N_to_hex_acc n' r (h::acc)
  end.
Next Obligation.
  apply N.mod_lt. intro H. congruence.
Qed.

Definition N_to_hex (n:nat) (i:N) : hex :=
  N_to_hex_acc n i nil.

Definition Z_to_hex_string (n:nat) (i:Z) : string :=
      if zlt i 0 then
        "-0x" ++ (hex_to_string (N_to_hex n (Z.to_N (0-i))))
      else
        "0x" ++ (hex_to_string (N_to_hex n (Z.to_N i))).
  
  
Notation "HZ[ str ]" := (hex_to_Z (string_to_hex str)) : hex_scope.

Notation "HB[ str ]" := (Byte.repr (hex_to_Z (string_to_hex str))) : hex_scope.

End Hex.


