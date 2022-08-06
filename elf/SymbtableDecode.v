Require Import Coqlib Integers AST Maps.
Require Import Asm Errors.
Require Import RelocProg RelocProgram Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import ListNotations.
Require Import SymbtableEncode.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

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
