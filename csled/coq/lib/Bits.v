Require Import Coqlib Integers String Ascii.


Module Bits.

Definition bits := list bool.

Definition char_to_bool (a: ascii) : bool :=
  if ascii_dec a "0" then
    false
  else 
    true.

Fixpoint string_to_bits (s:string): bits :=
  match s with
  | EmptyString => nil
  | String a s' =>
    (char_to_bool a) :: (string_to_bits s')
  end.
    
Notation "b[ str ]" := (string_to_bits str) : bits_scope.

(* Translate bits to integers *)

Definition bool_to_Z (b:bool) :=
  if b then 1 else 0.

Fixpoint bits_to_Z_acc acc bs :=
  match bs with
  | nil => acc
  | b :: bt => 
    bits_to_Z_acc (2*acc + (bool_to_Z b)) bt
  end.
         
Definition bits_to_Z (bs: bits) : Z :=
  bits_to_Z_acc 0 bs.

Notation "bB[ bits ]" := (Byte.repr (bits_to_Z bits)) : bits_scope.

End Bits.
