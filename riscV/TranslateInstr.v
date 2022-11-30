Require Import Coqlib Maps lib.Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm.
Require Import compcert.encode.Bits Memdata .
Require Import EncDecRet.
Require Import Coq.Logic.Eqdep_dec.
Import Bits.
Import ListNotations.
Require Import BPProperty.
Local Open Scope bits_scope.

Local Open Scope error_monad_scope.

Fixpoint bits_of_int_rec (n: nat) (x: Z) {struct n}: list bool :=
  match n with
  | O => nil
  | S m => ((x mod 2)=?1) :: bits_of_int_rec m (x / 2)
  end.

Definition bits_of_int (n: nat) (x: Z) : list bool :=
  rev (bits_of_int_rec n x).

Fixpoint int_of_bits (l: list bool): Z :=
  match l with
  | nil => 0
  | false :: l' =>  2 * (int_of_bits l')
  | true  :: l' => 2 * (int_of_bits l')+1
  end. 

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
Definition encode_freg (r:freg) : res (bits):=
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

Program Definition encode_freg_u5 (r:freg) : res u5 :=
  do b <- encode_freg r;
  if assertLength b 5 then
    OK (exist _ b _)
  else Error (msg "impossible").

Program Definition encode_ofs_u12 (ofs:Z) :res u12 :=  
  do ofs <- if ( -(two_power_nat 11) <=? ofs) && (ofs <? 0) then
             OK (ofs + (two_power_nat 12))
           else if ( 0 <=? ofs) && (ofs <? (two_power_nat 11)) then
                  OK ofs
                else Error (msg "Offset overflow in encode_ofs_u12");
  let ofs12 := (bits_of_int 12 ofs) in
  if assertLength ofs12 12 then
    OK (exist _ ofs12 _)
  else Error (msg "impossible").

(* Unsigned version:
Definition decode_ofs_u12 (bs:u12) : res int :=
  let bs' := proj1_sig bs in
  OK (Int.repr (int_of_bits bs')). *)

(* the nil case is impossible, can it be eliminated? *)
Definition decode_ofs_u12 (bs:u12) : res int :=
  let bs' := proj1_sig bs in
  match bs' with
  | b0 :: bs1 => 
      if b0 then OK (Int.repr ((int_of_bits bs') - two_power_nat 12)) 
        else OK (Int.repr (int_of_bits bs'))
  | nil => Error(msg "impossible")
  end.

(* proof broken due to the modification of encode_ofs_u12 *)
(* Lemma encode_ofs_u12_consistency:forall ofs l, *)
(*     encode_ofs_u12 (Int.intval ofs) = OK l -> *)
(*     decode_ofs_u12 l = OK ofs. *)
(* Proof. *)
(*   unfold encode_ofs_u12,decode_ofs_u12. *)
(*   intros. do 2 destr_in H. *)

(*   (* Clear -Heqb. *) *)
(*   destruct l. *)
(*   cbn [proj1_sig]. *)
(*   destruct ofs. cbn [Int.intval] in *. *)
(*   assert ((bits_of_int 12 (intval + two_power_nat 12)) = x). *)
(*   inv H. auto. *)
(*   (* the length is 0, impossible *) *)
(*   destruct x. inversion e0. *)

(*   (* length is not 0 *) *)
(*   destruct b eqn:Hb; f_equal. *)
(*   (* sign is 1 , Heqb: intval<0 ; intrange: intval>-1  Contradiction*) *)

(*   Transparent Int.repr. *)
(*   unfold Int.repr. *)
(*   eapply Int.mkint_eq. *)
(*   destruct x. simpl in e0. congruence. *)
(*   repeat (destruct x as [|? x];simpl in e0;try congruence). *)
(* Admitted. *)

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
  if ( -(two_power_nat 19) <=? ofs) && (ofs <? 0) then    
  let ofs20 := (bits_of_int 20 (ofs + (two_power_nat 20))) in
  if assertLength ofs20 20 then
    OK (exist _ ofs20 _)         
  else Error (msg "impossible")
  else
  if ( 0 <=? ofs) && (ofs <? (two_power_nat 19)) then
    let ofs20 := (bits_of_int 20 ofs) in
    if assertLength ofs20 20 then
      OK (exist _ ofs20 _)         
    else Error (msg "impossible")
  else Error (msg "Offset overflow in encode_ofs_u20").

(* Unsigned version:
  Definition decode_ofs_u12 (bs:u12) : res int :=
  let bs' := proj1_sig bs in
  OK (Int.repr (int_of_bits bs')). *)
Definition decode_ofs_u20 (bs:u20) : res int :=
  let bs' := proj1_sig bs in
  match bs' with
  | b0 :: bs1 => 
      if b0 then OK (Int.repr ((int_of_bits bs') - two_power_nat 20)) 
        else OK (Int.repr (int_of_bits bs'))
  | nil => Error(msg "impossible")
  end.

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
  | Paddiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    (* do imm12  <- encode_ofs_u12_signed (Int.signed imm); *)
    OK (addi rdbits rsbits imm12)
  | Psltiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    OK (slti rdbits rsbits imm12)
  | Pandiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    OK (andi rdbits rsbits imm12)
  | Poriw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    OK (ori rdbits rsbits imm12)
  | Pxoriw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm12  <- encode_ofs_u12 (Int.signed imm);
    OK (xori rdbits rsbits imm12)
  | Pslliw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm5  <- encode_ofs_u5 (Int.signed imm);
    OK (slli rdbits rsbits imm5)
  | Psrliw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm5  <- encode_ofs_u5 (Int.signed imm);
    OK (srli rdbits rsbits imm5)
  | Psraiw rd rs imm =>
    do rdbits <- encode_ireg rd;
    do rsbits <- encode_ireg0 rs;
    do imm5  <- encode_ofs_u5 (Int.signed imm);
    OK (srai rdbits rsbits imm5)
  | Pluiw rd imm =>
    do rdbits <- encode_ireg rd;
    do imm20  <- encode_ofs_u20 (Int.signed imm);
    OK (lui rdbits imm20)
  | Paddw rd rs1 rs2 =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (add rdbits rs1bits rs2bits)
  | Psubw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (sub rdbits rs1bits rs2bits)
  | Pmulw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (mul rdbits rs1bits rs2bits)
  | Pmulhw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (mulh rdbits rs1bits rs2bits)
  | Pmulhuw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (mulhu rdbits rs1bits rs2bits)
  | Pdivw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (div rdbits rs1bits rs2bits)
  | Pdivuw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (divu rdbits rs1bits rs2bits)
  | Premw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (rem rdbits rs1bits rs2bits)
  | Premuw rd rs1 rs2 =>
  if Archi.ptr64 then Error (msg "Only in rv32")
    else 
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (remu rdbits rs1bits rs2bits)
  | Psltw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (slt rdbits rs1bits rs2bits)
  | Psltuw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (sltu rdbits rs1bits rs2bits)
  | Pandw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (and rdbits rs1bits rs2bits)
  | Porw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (or rdbits rs1bits rs2bits)
  | Pxorw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (xor rdbits rs1bits rs2bits)
  | Psllw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (sll rdbits rs1bits rs2bits)
  | Psrlw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (srl rdbits rs1bits rs2bits)
  | Psraw rd rs1 rs2 =>
    do rdbits <- encode_ireg rd;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (sra rdbits rs1bits rs2bits)
  | Pbeq_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (beq B1 B2 rs1bits rs2bits B3 B4)
  | Pbne_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bne B1 B2 rs1bits rs2bits B3 B4)
  | Pblt_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (blt B1 B2 rs1bits rs2bits B3 B4)
  | Pbltu_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bltu B1 B2 rs1bits rs2bits B3 B4)
  | Pbge_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bge B1 B2 rs1bits rs2bits B3 B4)
  | Pbgeu_ofs rs1 rs2 ofs =>
    if Archi.ptr64 then Error (msg "Only in rv32")
    else
    do B1 <- encode_B1 ofs;
    do B2 <- encode_B2 ofs;
    do B3 <- encode_B3 ofs;
    do B4 <- encode_B4 ofs;
    do rs1bits <- encode_ireg0 rs1;
    do rs2bits <- encode_ireg0 rs2;
    OK (bgeu B1 B2 rs1bits rs2bits B3 B4)
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
  | Pfmv fd fs =>
    do fdbits <- encode_freg_u5 fd;
    do fsbits <- encode_freg_u5 fs;
    OK (fsgnjd fdbits fsbits fsbits)
  | Pfmvxs rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg_u5 fs;
    OK (fmvxw rdbits fsbits)
  | Pfmvsx fd rs =>
    do fdbits <- encode_freg_u5 fd;
    do rsbits <- encode_ireg rs;
    OK (fmvwx fdbits rsbits)
  | Pfls fd ra ofs =>
    do fdbits <- encode_freg_u5 fd;
    do rabits <- encode_ireg0 ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immbits <- encode_ofs_u12 ofs_Z;
    OK (flw fdbits rabits immbits)
  | Pfss fs ra ofs =>
    do fsbits <- encode_freg_u5 fs;
    do rabits <- encode_ireg ra;
    do ofs_Z <- ofs_to_Z ofs;
    do immS1bits <- encode_S1 ofs_Z;
    do immS2bits <- encode_S2 ofs_Z;
    OK (fsw immS1bits fsbits rabits immS2bits)
  | Pfnegs fd fs =>
    do fdbits <- encode_freg_u5 fd;
    do fsbits <- encode_freg_u5 fs;
    OK (fsgnjns fdbits fsbits fsbits)
  | Pfadds fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fadds fdbits fs1bits fs2bits)
  | Pfsubs fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fsubs fdbits fs1bits fs2bits)
  | Pfmuls fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fmuls fdbits fs1bits fs2bits)
  | Pfdivs fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fdivs fdbits fs1bits fs2bits)
  | Pfmins fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fmins fdbits fs1bits fs2bits)
  | Pfmaxs fd fs1 fs2 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fmaxs fdbits fs1bits fs2bits)
  | Pfeqs rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (feqs rdbits fs1bits fs2bits)
  | Pflts rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (flts rdbits fs1bits fs2bits)
  | Pfles rd fs1 fs2 =>
    do rdbits <- encode_ireg rd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    OK (fles rdbits fs1bits fs2bits)
  | Pfsqrts fd fs =>
    do fdbits <- encode_freg_u5 fd;
    do fsbits <- encode_freg_u5 fs;
    OK (fsqrts fdbits fsbits)
  | Pfmadds fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    do fs3bits <- encode_freg_u5 fs3;
    OK (fmadds fdbits fs1bits fs2bits fs3bits)
  | Pfmsubs fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    do fs3bits <- encode_freg_u5 fs3;
    OK (fmsubs fdbits fs1bits fs2bits fs3bits)
  | Pfnmadds fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    do fs3bits <- encode_freg_u5 fs3;
    OK (fnmadds fdbits fs1bits fs2bits fs3bits)
  | Pfnmsubs fd fs1 fs2 fs3 =>
    do fdbits <- encode_freg_u5 fd;
    do fs1bits <- encode_freg_u5 fs1;
    do fs2bits <- encode_freg_u5 fs2;
    do fs3bits <- encode_freg_u5 fs3;
    OK (fnmsubs fdbits fs1bits fs2bits fs3bits)
  | Pfcvtws rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg_u5 fs;
    OK (fcvtws rdbits fsbits)
  | Pfcvtwus rd fs =>
    do rdbits <- encode_ireg rd;
    do fsbits <- encode_freg_u5 fs;
    OK (fcvtwus rdbits fsbits)
  | Pfcvtsw fd rs =>
    do fdbits <- encode_freg_u5 fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtsw fdbits rsbits)
  | Pfcvtswu fd rs =>
    do fdbits <- encode_freg_u5 fd;
    do rsbits <- encode_ireg0 rs;
    OK (fcvtswu fdbits rsbits)
  | _ => Error [MSG "Not exists or unsupported: "; MSG (instr_to_string i)]
  end.

Definition translate_instr i := do i' <- translate_instr' i; OK [i'].

(* FIXME: for the big endian output for the multi-bytes token in CSLED *)
Definition bits_to_bytes_archi bs := do bs' <- (bits_to_bytes bs); OK (rev bs').

(* Decode;struction *)

  (* NEW *)
Definition decode_instr_rv32 (i: Instruction) : res instruction :=
  match i with
  | addi rdbits rsbits imm12 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u12 imm12;
    OK (Asm.Paddiw rd rs imm)
  | slti rdbits rsbits imm12 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u12 imm12;
    OK (Asm.Psltiw rd rs imm)
  | andi rdbits rsbits imm12 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u12 imm12;
    OK (Asm.Pandiw rd rs imm)
  | ori rdbits rsbits imm12 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u12 imm12;
    OK (Asm.Poriw rd rs imm)
  | xori rdbits rsbits imm12 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u12 imm12;
    OK (Asm.Pxoriw rd rs imm)
  | slli rdbits rsbits imm5 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u5 imm5;
    OK (Asm.Pslliw rd rs imm)
  | srli rdbits rsbits imm5 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u5 imm5;
    OK (Asm.Psrliw rd rs imm)
  | srai rdbits rsbits imm5 =>
    do rd  <- decode_ireg_u5 rdbits;
    do rs  <- decode_ireg0_u5 rsbits;
    do imm <- decode_ofs_u5 imm5;
    OK (Asm.Psraiw rd rs imm)
  | lui rdbits imm20 =>
    do rd  <- decode_ireg_u5 rdbits;
    do imm <- decode_ofs_u20 imm20;
    OK (Asm.Pluiw rd imm)
  | add rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Paddw rd rs1 rs2)
  | sub rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psubw rd rs1 rs2)
  | mul rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pmulw rd rs1 rs2)
  | mulh rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pmulhw rd rs1 rs2)
  | mulhu rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pmulhuw rd rs1 rs2)
  | div rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pdivw rd rs1 rs2)
  | divu rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pdivuw rd rs1 rs2)
  | rem rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Premw rd rs1 rs2)
  | remu rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Premuw rd rs1 rs2)
  | slt rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psltw rd rs1 rs2)
  | sltu rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psltuw rd rs1 rs2)
  | and rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pandw rd rs1 rs2)
  | xor rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Pxorw rd rs1 rs2)
  | sll rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psllw rd rs1 rs2)
  | srl rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psrlw rd rs1 rs2)
  | sra rdbits rs1bits rs2bits =>
    do rd  <- decode_ireg_u5 rdbits ;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Asm.Psraw rd rs1 rs2)
  | beq immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pbeq_ofs rs1 rs2 ofs_Z)
  | bne immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pbne_ofs rs1 rs2 ofs_Z)
  | blt immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pblt_ofs rs1 rs2 ofs_Z)
  | bltu immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pbltu_ofs rs1 rs2 ofs_Z)
  | bge immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pbge_ofs rs1 rs2 ofs_Z)
  | bgeu immB1 immB2 rs1bits rs2bits immB3 immB4 =>
    do ofs_Z <- decode_immB immB1 immB2 immB3 immB4;
    do rs1 <- decode_ireg0_u5 rs1bits;
    do rs2 <- decode_ireg0_u5 rs2bits;
    OK (Pbgeu_ofs rs1 rs2 ofs_Z)
  | lb rdbits rabits ofs_bits =>
    do rd <- decode_ireg_u5 rdbits;
    do ra <- decode_ireg_u5 rabits;
    do ofs_int <- decode_ofs_u12 ofs_bits;
    do ofs <- Z_to_ofs (Int.intval ofs_int);
    OK (Asm.Plb rd ra ofs)
  | lbu rdbits rabits ofs_bits =>
    do rd <- decode_ireg_u5 rdbits;
    do ra <- decode_ireg_u5 rabits;
    do ofs_int <- decode_ofs_u12 ofs_bits;
    do ofs <- Z_to_ofs (Int.intval ofs_int);
    OK (Asm.Plbu rd ra ofs)
  | lh rdbits rabits ofs_bits =>
    do rd <- decode_ireg_u5 rdbits;
    do ra <- decode_ireg_u5 rabits;
    do ofs_int <- decode_ofs_u12 ofs_bits;
    do ofs <- Z_to_ofs (Int.intval ofs_int);
    OK (Asm.Plh rd ra ofs)
  | lhu rdbits rabits ofs_bits =>
    do rd <- decode_ireg_u5 rdbits;
    do ra <- decode_ireg_u5 rabits;
    do ofs_int <- decode_ofs_u12 ofs_bits;
    do ofs <- Z_to_ofs (Int.intval ofs_int);
    OK (Asm.Plhu rd ra ofs)
  | lw rdbits rabits ofs_bits =>
    do rd <- decode_ireg_u5 rdbits;
    do ra <- decode_ireg_u5 rabits;
    do ofs_int <- decode_ofs_u12 ofs_bits;
    do ofs <- Z_to_ofs (Int.intval ofs_int);
    OK (Asm.Plw rd ra ofs)
  | _ => Error (msg "unsupported")
  end.
