Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Axioms Globalenvs.
Require Import Asm RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
(* Import Hex compcert.encode.Bits.Bits. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import RelocBingen.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope nat_scope.

(** *CAV21: Instruction ,CompCertELF: instruction*)

Definition assertLength {A} (l:list A) n: {length l = n} +
                                          {length l <> n}.
Proof.
  decide equality.
Defined.

Definition builtIn (n:nat): Type := {d:list bool| length d = n}.

Lemma builtin_inj: forall {n} (a b:builtIn n),
    proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n a b H.
  induction a, b.
  simpl in H.
  subst x0.
  f_equal.
  apply UIP_dec.
  apply Nat.eq_dec.
Qed.

Definition u2 := builtIn 2.

Definition u3 := builtIn 3.

Definition u4 := builtIn 4.

Definition u8 := builtIn 8.

Definition u16 := builtIn 16.

Definition u32 := builtIn 32.

Definition nat_to_bits8_opt n : bits :=
  [( n/128 mod 2 =? 1);
  ( n/64 mod 2 =? 1);
  ( n/32 mod 2 =? 1);
  ( n/16 mod 2 =? 1);
  ( n/8 mod 2 =? 1);
  ( n/4 mod 2 =? 1);
  ( n/2 mod 2 =? 1);
  ( n mod 2 =? 1)].

Fixpoint bytes_to_bits_opt (lb:list byte) : bits :=
  match lb with
  | [] => []
  | b::lb' =>(nat_to_bits8_opt (Z.to_nat (Byte.unsigned b))) ++
                                                           (bytes_to_bits_opt lb')
  end.
Program Definition zero32 : u32 :=
  bytes_to_bits_opt (bytes_of_int 4 0).

Program Definition encode_ireg_u3 (r:ireg) : res u3 :=
  do b <- encode_ireg r;
  if assertLength b 3 then
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_ireg (bs: u3) : res ireg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(RAX)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(RCX)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(RDX)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(RBX)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(RSP)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(RBP)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(RSI)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(RDI)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma ireg_encode_consistency :
  forall r encoded,
  encode_ireg_u3 r = OK(encoded) ->
  decode_ireg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_ireg_u3 in H.
  destruct r; simpl in H;
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma ireg_decode_consistency :
  forall r encoded,
  decode_ireg encoded = OK(r) ->
  encode_ireg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_ireg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_ireg_u3; simpl;        (**r calculate encode_ireg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_freg_u3 (r:freg) : res u3 :=
  do b <- encode_freg r;
  if assertLength b 3 then
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_freg (bs: u3) : res freg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(XMM0)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(XMM1)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(XMM2)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(XMM3)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(XMM4)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(XMM5)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(XMM6)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(XMM7)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma freg_encode_consistency :
  forall r encoded,
  encode_freg_u3 r = OK(encoded) ->
  decode_freg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_freg_u3 in H.
  destruct r; simpl in H;
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma freg_decode_consistency :
  forall r encoded,
  decode_freg encoded = OK(r) ->
  encode_freg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_freg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_freg_u3; simpl;        (**r calculate encode_freg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_scale_u2 (ss: Z) :res u2 :=
  do s <- encode_scale ss;
  if assertLength s 2 then
    OK (exist _ s _)
  else Error (msg "impossible").

Definition decode_scale (bs: u2) : res Z :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(1%Z)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(2%Z)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(4%Z)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(8%Z)      (**r b["011"] *)
  else Error(msg "reg not found")
.

Lemma scale_encode_consistency :
  forall ss encoded,
  encode_scale_u2 ss = OK(encoded) ->
  decode_scale encoded = OK(ss).
Proof.
  intros.
  destruct encoded.
  unfold encode_scale_u2 in H; monadInv H.

  destruct (assertLength x0 2); try discriminate.  (**r prove x = x0 *)
  inversion EQ0; subst.

  unfold encode_scale in EQ.
  destruct ss eqn:Ess; try discriminate.
  repeat (destruct p; try discriminate);           (**r generate subgoals for each scale 1/2/4/8 *)
  inversion EQ as [Heq]; subst; simpl;             (**r replace x with exact value *)
  unfold decode_scale; auto.                       (**r get result of function decode_scale *)
Qed.

Lemma scale_decode_consistency :
  forall r encoded,
  decode_scale encoded = OK(r) ->
  encode_scale_u2 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1] *)
  destruct b0, b1 eqn:Eb;
  unfold decode_scale in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_scale_u2; simpl;        (**r calculate encode_scale_u2 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

(** Wordsize BEGIN *)
(** TODO: these module should not be exported *)

Module Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_32.

Module int32 := Make(Wordsize_32).

Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_16.

Module int16 := Make(Wordsize_16).

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_8.

Module int8 := Make(Wordsize_8).

Definition in_int_range_b (intval:Z) (modulus:Z) :=
  Z.leb (-1) intval || Z.leb intval modulus. 

Definition in_int_range (intval:Z) (modulus:Z) :=
  Z.le (-1) intval /\ Z.le intval modulus. 

(** Wordsize END *)

Program Definition encode_ofs_u8 (ofs:int) :res u8 :=
  let intval := Int.unsigned ofs in
  if in_int_range_b intval int8.modulus then
    let ofs8 := bytes_to_bits_opt (bytes_of_int 1 intval) in
    if assertLength ofs8 8 then
      OK (exist _ ofs8 _)
    else Error (msg "impossible")
  else Error (msg "Not in range").

Definition decode_ofs_u8 (bs:u8) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK (Int.repr z).

Lemma encode_decode_ofs_u8 : forall ofs bs,
  encode_ofs_u8 ofs = OK(bs) ->
  decode_ofs_u8 bs = OK(ofs).
Admitted.

Lemma decode_encode_ofs_u8 : forall ofs bs,
  decode_ofs_u8 bs = OK(ofs) ->
  encode_ofs_u8 ofs = OK(bs).
Admitted.

Program Definition encode_ofs_u16 (ofs:int) :res u16 :=
  let intval := Int.unsigned ofs in
  if in_int_range_b intval int16.modulus then
    let ofs16 := bytes_to_bits_opt (bytes_of_int 1 intval) in
    if assertLength ofs16 16 then
      OK (exist _ ofs16 _)
    else Error (msg "impossible")
  else Error (msg "Not in range").

Definition decode_ofs_u16 (bs:u16) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK(Int.repr z).

Lemma encode_decode_ofs_u16 : forall ofs bs,
  encode_ofs_u16 ofs = OK(bs) ->
  decode_ofs_u16 bs = OK(ofs).
Admitted.

Lemma decode_encode_ofs_u16 : forall ofs bs,
  decode_ofs_u16 bs = OK(ofs) ->
  encode_ofs_u16 ofs = OK(bs).
Admitted.

Program Definition encode_ofs_u32 (ofs:int) :res u32 :=
  let intval := Int.unsigned ofs in
  if in_int_range_b intval int32.modulus then
    let ofs32 := bytes_to_bits_opt (bytes_of_int 1 intval) in
    if assertLength ofs32 32 then
      OK (exist _ ofs32 _)
    else Error (msg "impossible")
  else Error (msg "Not in range").

Program Definition Z_encode_ofs_u32 (ofs:Z) :res u32 :=
  if in_int_range_b ofs int32.modulus then
    let ofs32 := bytes_to_bits_opt (bytes_of_int 1 ofs) in
    if assertLength ofs32 32 then
      OK (exist _ ofs32 _)
    else Error (msg "impossible")
  else Error (msg "Not in range").

Definition decode_ofs_u32 (bs:u32) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK (Int.repr z).

Definition Z_decode_ofs_u32 (bs:u32) : res Z :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK (z).

Lemma encode_decode_ofs_u32 : forall ofs bs,
  encode_ofs_u32 ofs = OK(bs) ->
  decode_ofs_u32 bs = OK(ofs).
Admitted.

Lemma decode_encode_ofs_u32 : forall ofs bs,
  decode_ofs_u32 bs = OK(ofs) ->
  encode_ofs_u32 ofs = OK(bs).
Admitted.

Lemma Z_encode_decode_ofs_u32 : forall ofs bs,
  Z_encode_ofs_u32 ofs = OK(bs) ->
  Z_decode_ofs_u32 bs = OK(ofs).
Admitted.

Lemma Z_decode_encode_ofs_u32 : forall ofs bs,
  Z_decode_ofs_u32 bs = OK(ofs) ->
  Z_encode_ofs_u32 ofs = OK(bs).
Admitted.

Program Definition encode_testcond_u4 (c:testcond) : u4 :=
  match c with
  | Cond_e   => b["0100"]   (**r 4 *)
  | Cond_ne  => b["0101"]   (**r 5 *)
  | Cond_b   => b["0010"]   (**r 2 *)
  | Cond_be  => b["0110"]   (**r 6 *)
  | Cond_ae  => b["0011"]   (**r 3 *)
  | Cond_a   => b["0111"]   (**r 7 *)
  | Cond_l   => b["1100"]   (**r C *)
  | Cond_le  => b["1110"]   (**r E *)
  | Cond_ge  => b["1101"]   (**r D *)
  | Cond_g   => b["1111"]   (**r F *)
  | Cond_p   => b["1010"]   (**r A *)
  | Cond_np  => b["1011"]   (**r B *)
  end.

Definition decode_testcond_u4 (bs:u4) : res testcond :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 4 then OK(Cond_e)            (**r 4 b["0100"] *)
  else if Z.eqb n 5  then OK(Cond_ne)     (**r 5 b["0101"] *)
  else if Z.eqb n 2  then OK(Cond_b)      (**r 2 b["0010"] *)
  else if Z.eqb n 6  then OK(Cond_be)     (**r 6 b["0110"] *)
  else if Z.eqb n 3  then OK(Cond_ae)     (**r 3 b["0011"] *)
  else if Z.eqb n 7  then OK(Cond_a)      (**r 7 b["0111"] *)
  else if Z.eqb n 12 then OK(Cond_l)      (**r C b["1100"] *)
  else if Z.eqb n 14 then OK(Cond_le)     (**r E b["1110"] *)
  else if Z.eqb n 13 then OK(Cond_ge)     (**r D b["1101"] *)
  else if Z.eqb n 15 then OK(Cond_g)      (**r F b["1111"] *)
  else if Z.eqb n 10 then OK(Cond_p)      (**r A b["1010"] *)
  else if Z.eqb n 11 then OK(Cond_np)     (**r B b["1011"] *)
  else Error(msg "reg not found")
.

Lemma testcond_encode_consistency : forall c bs,
  encode_testcond_u4 c = bs ->
  decode_testcond_u4 bs = OK(c).
Proof.
  (**r enumerate all possibility of c *)
  destruct c;
  simpl; unfold char_to_bool; simpl;
  intros; subst;
  unfold decode_testcond_u4; simpl;
  auto.
Qed.

Lemma testcond_decode_consistency : forall c bs,
  decode_testcond_u4 bs = OK(c) ->
  encode_testcond_u4 c = bs.
Proof.
  intros.
  destruct bs as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b as [| b3 b]; try discriminate; inversion Hlen. (**r the 4th one *)
  destruct b; try discriminate.                             (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2, b3 eqn:Eb;
  unfold decode_testcond_u4 in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                         (**r subst r *)
  unfold encode_testcond_u4; simpl;           (**r calculate encode_testcond_u4 *)
  cbv delta in *;
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                            (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                        (**r to solve e = eq_refl *)
Qed.

(* Addressing mode in CAV21 automatically generated definition *)
Inductive AddrE: Type :=
| AddrE12(uvar3_0:u3)
| AddrE11(uvar32_0:u32)
| AddrE10(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)
| AddrE9(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrE8(uvar3_0:u3)
| AddrE7(uvar32_0:u32)
| AddrE6(uvar3_0:u3)(uvar32_1:u32)
| AddrE5(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrE4(uvar3_0:u3)(uvar32_1:u32).

(* Instruction in CAV21 automatically generated definition *)
Inductive Instruction: Type :=
| Psubl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pbsqrtsd(uvar3_0:u3)(uvar3_1:u3)
| Psbbl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prep_movsl
| Pmovsq_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsq_mr(AddrE:AddrE)(uvar3_0:u3)
| Pminsd(uvar3_0:u3)(uvar3_1:u3)
| Pmaxsd(uvar3_0:u3)(uvar3_1:u3)
| Pbswap32(uvar3_0:u3)
| Pbsrl(uvar3_0:u3)(uvar3_1:u3)
| Pbsfl(uvar3_0:u3)(uvar3_1:u3)
| Paddl_mi(AddrE:AddrE)(uvar32_1:u32)
| Paddl_rr(uvar3_0:u3)(uvar3_1:u3)
| Padcl_rr(uvar3_0:u3)(uvar3_1:u3)
| Padcl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pjcc_rel(uvar4_0:u4)(uvar32_1:u32)
| Pret_iw(uvar16_0:u16)
| Pret
| Pcall_r(uvar3_0:u3)
| Pcall_ofs(uvar32_0:u32)
| Pnop
| Pjmp_m(AddrE:AddrE)
| Pjmp_r(uvar3_0:u3)
| Pjmp_l_rel(uvar32_0:u32)
| Pandps_fm(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_fm(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_f(uvar3_0:u3)(uvar3_1:u3)
| Pcomisd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuld_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubd_ff(uvar3_0:u3)(uvar3_1:u3)
| Paddd_ff(uvar3_0:u3)(uvar3_1:u3)
| Psetcc(uvar4_0:u4)(uvar3_1:u3)
| Pcmov(uvar4_0:u4)(uvar3_1:u3)(uvar3_2:u3)
| Ptestl_rr(uvar3_0:u3)(uvar3_1:u3)
| Ptestl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prorl_ri(uvar3_0:u3)(uvar8_1:u8)
| Prolw_ri(uvar3_0:u3)(uvar8_1:u8)
| Pshld_ri(uvar3_0:u3)(uvar3_1:u3)(uvar8_2:u8)
| Psarl_rcl(uvar3_0:u3)
| Psarl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pshrl_rcl(uvar3_0:u3)
| Pshrl_ri(uvar3_0:u3)(uvar8_1:u8)
| Psall_rcl(uvar3_0:u3)
| Psall_ri(uvar3_0:u3)(uvar8_1:u8)
| Pnotl(uvar3_0:u3)
| Pxorl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pxorl_ri(uvar3_0:u3)(uvar32_1:u32)
| Porl_rr(uvar3_0:u3)(uvar3_1:u3)
| Porl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pidivl_r(uvar3_0:u3)
| Pdivl_r(uvar3_0:u3)
| Pcltd
| Pmull_r(uvar3_0:u3)
| Pimull_ri(uvar3_0:u3)(uvar3_1:u3)(uvar32_2:u32)
| Pimull_rr(uvar3_0:u3)(uvar3_1:u3)
| Psubl_rr(uvar3_0:u3)(uvar3_1:u3)
| Paddl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pnegl(uvar3_0:u3)
| Pleal(AddrE:AddrE)(uvar3_0:u3)
| Pcvttss2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2sd_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2ss_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvttsd2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtss2sd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsd2ss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsw_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovzw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovzw_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovsb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsb_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovzb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovzb_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_mr(AddrE:AddrE)(uvar3_0:u3)
| Pflds_m(AddrE:AddrE)
| Pfstps_m(AddrE:AddrE)
| Pfstpl_m(AddrE:AddrE)
| Pfldl_m(AddrE:AddrE)
| Pmovss_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovss_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsd_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pmovl_rr(uvar3_0:u3)(uvar3_1:u3).


Definition Instr_reloc_offset (i:Instruction): res Z := Error (msg "unfinished").

Section WITH_RELOC_OFS_MAP.

Variable rtbl_ofs_map: reloc_ofs_map_type.

(* Translate ccelf addressing mode to cav21 addr mode *)
Definition translate_Addrmode_AddrE (sofs: Z) (res_iofs: res Z) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- res_iofs;
        do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          match obase,oindex with
          | None,None =>
            OK (AddrE11 zero32)
          | Some base,None =>
            do r <- encode_ireg_u3 base;
              OK (AddrE6 r zero32)
          | None,Some (idx,ss) =>
            do index <- encode_ireg_u3 idx;
            do scale <- encode_scale_u2 ss;
            if ireg_eq idx RSP then
              (* OK (AddrE7 zero32) *)
              Error (msg "index can not be RSP")
            else
              OK (AddrE9 scale index zero32)
          | Some base,Some (idx,ss) =>
            do scale <- encode_scale_u2 ss;
            do index <- encode_ireg_u3 idx;
            do breg <- encode_ireg_u3 base;
            if ireg_eq idx RSP then
              Error (msg "index can not be RSP")
                    (* OK (AddrE4 breg zero32)            *)
            else
              OK (AddrE5 scale index breg zero32)
          end
        else Error (msg "addend is not equal to ofs")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      do iofs <- res_iofs;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        do ofs32 <- Z_encode_ofs_u32 ofs;
        match obase,oindex with
        | None,None =>
          OK (AddrE11 ofs32)
        | Some base,None =>
          do r <- encode_ireg_u3 base;
          OK (AddrE6 r ofs32)
        | None,Some (idx,ss) =>
          do r <- encode_ireg_u3 idx;
          do scale <- encode_scale_u2 ss;
          if ireg_eq idx RSP then
            (* OK (AddrE7 ofs32) *)
            Error (msg "index can not be RSP")
          else
            OK (AddrE9 scale r ofs32)
        | Some base,Some (idx,ss) =>
          do scale <- encode_scale_u2 ss;
          do index <- encode_ireg_u3 idx;
          do breg <- encode_ireg_u3 base;
          if ireg_eq idx RSP then
            Error (msg "index can not be RSP")
                  (* OK (AddrE4 breg_sig ofs32) *)
          else
            OK (AddrE5 scale index breg ofs32)
        end
      | _ => Error (msg "impossible")
      end
    end
  end.




(* Translate CAV21 addr mode to ccelf addr mode *)
Definition translate_AddrE_Addrmode (sofs: Z) (res_iofs : res Z) (addr:AddrE) : res addrmode :=
  (* need to relocate? *)
  do iofs <- res_iofs;
  match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
  | None =>
    match addr with
    | AddrE11 disp =>
      OK (Addrmode None None (inl (bits_to_Z (proj1_sig disp))))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg idx;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else
        OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | AddrE6 base disp =>
      do b <- decode_ireg base;
      OK (Addrmode (Some b) None (inl (bits_to_Z (proj1_sig disp))) )
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg idx;
      do b <- decode_ireg base;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | _ => Error (msg "unsupported or impossible")
    end
  | Some _ =>
    do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
    match addr with
    | AddrE11 _ =>
      OK (Addrmode None None (inr (xH,Ptrofs.repr addend)))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg idx;
      OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | AddrE6 base disp =>
      do b <- decode_ireg base;
      OK (Addrmode (Some b) None (inr (xH,Ptrofs.repr addend)))
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg idx;
      do b <- decode_ireg base;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | _ => Error (msg "unsupported or impossible")
    end
  end.

(* consistency proof *)
Lemma translate_consistency1 : forall ofs iofs addr addrE,
    translate_Addrmode_AddrE ofs iofs addr = OK addrE ->
    translate_AddrE_Addrmode ofs iofs addrE = OK addr.
  intros. destruct addr.
  unfold translate_Addrmode_AddrE in H.
  unfold translate_AddrE_Addrmode.
  (* destruct base;destruct (ZTree.get);try destruct p;destruct const;try congruence. *)
  (* - monadInv H. *)
  (*   rewrite EQ. *)
  (*   cbn [bind].     *)
  (*   destruct (ZTree.get (x + ofs)%Z rtbl_ofs_map);try congruence. *)
  (*   monadInv EQ0. *)
  (*   destruct (ireg_eq i1 RSP);try congruence. *)
  (*   monadInv EQ5. *)
Admitted.


(* ccelf instruction to cav21 instruction, unfinished!!! *)
Definition translate_instr (ofs: Z) (i:instruction) : res Instruction :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE ofs (instr_reloc_offset i) in
  match i with
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg_u3 rd;
    do r1bits <- encode_ireg_u3 r1;
    OK (Pmovl_rr rdbits r1bits)
  | Asm.Pmovl_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovl_rm a rdbits)
  | Asm.Pmovl_ri rd imm =>
    do rdbits <- encode_ireg_u3 rd;
    do imm32 <- encode_ofs_u32 imm;
    OK (Pmovl_ri rdbits imm32)
  | Asm.Pmovl_mr addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovl_mr a rbits)
  | Asm.Pmovsd_ff rd r1 =>
    do rdbits <- encode_freg_u3 rd;
    do r1bits <- encode_freg_u3 r1;
    OK (Pmovsd_ff rdbits r1bits)
  | Asm.Pmovsd_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsd_fm a rbits)
  | Asm.Pmovsd_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsd_mf a rbits)
  | Asm.Pmovss_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovss_fm a rbits)
  | Asm.Pmovss_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovss_mf a rbits)
  | Asm.Pfldl_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfldl_m a)
  | Asm.Pfstpl_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfstpl_m a)
  | Asm.Pflds_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pflds_m a)
  | Asm.Pfstps_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfstps_m a)
  | Asm.Pmovb_mr addr r =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovb_mr a rbits)
  | Asm.Pmovw_mr addr r =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovw_mr a rbits)
  | Asm.Pmovzb_rr rd r =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovzb_rr rdbits rbits)
  | Asm.Pmovzb_rm r addr =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovzb_rm a rbits)
  (*from there*)
  | Asm.Pmovzw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovzw_rm a rbits)
  | Asm.Pmovzw_rr rd rs =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 rs;
     OK (Pmovzw_rr rdbits rbits)
  | Asm.Pmovsb_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsb_rm a rbits)
  | Asm.Pmovsb_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsb_rr rdbits rbits)
  | Asm.Pmovw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovw_rm a rbits)
  | Asm.Pmovb_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovb_rm a rdbits)
  | Asm.Pmovsw_rm rd addr =>
     do rdbits <- encode_ireg_u3 rd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pmovsw_rm a rdbits)
  | Asm.Pmovsw_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsw_rr rdbits rbits)
  | Asm.Pnegl r =>
     do rbits <- encode_ireg_u3 r;
     OK (Pnegl rbits)
  | Asm.Pleal r addr =>
     do rbits <- encode_ireg_u3 r;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pleal a rbits)
  | Asm.Pcvttss2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttss2si_rf rdbits rbits)
  | Asm.Pcvtsi2sd_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2sd_fr rdbits rbits)
  | Asm.Pcvtsi2ss_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2ss_fr rdbits rbits)
  | Asm.Pcvttsd2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttsd2si_rf rdbits rbits)
  | Asm.Pcvtss2sd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtss2sd_ff rdbits rbits)
  | Asm.Pcvtsd2ss_ff rd r1=>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtsd2ss_ff rdbits rbits)
  | Asm.Paddl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Paddl_ri rdbits imm32)
  | Asm.Psubl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Psubl_rr rdbits rbits)
  | Asm.Pimull_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pimull_rr rdbits rbits)
  | Asm.Pimull_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Pimull_ri rdbits rdbits imm32)
  | Asm.Pmull_r r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pmull_r rbits)
  | Asm.Pcltd => OK (Pcltd)
  | Asm.Pdivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pdivl_r rbits)
  | Asm.Pidivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pidivl_r rbits)
  | Asm.Pandl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pandl_rr rdbits rbits)
  | Asm.Pandl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Pandl_ri rdbits imm32)
  | Asm.Porl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Porl_ri rdbits imm32)
  | Asm.Porl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Porl_rr rdbits rbits)
  | Asm.Pxorl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pxorl_rr rdbits rbits)
  | Asm.Pxorl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Pxorl_ri rdbits imm32)
  | Asm.Pnotl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pnotl rdbits)
  | Asm.Psall_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Psall_ri rdbits imm8)
  | Asm.Psall_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psall_rcl rdbits)
  | Asm.Pshrl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Pshrl_ri rdbits imm8)
  | Asm.Psarl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Psarl_ri rdbits imm8)
  | Asm.Psarl_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psarl_rcl rdbits)
  | Asm.Pshld_ri rd r1 imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     do imm8 <- encode_ofs_u8 imm;
     OK (Pshld_ri rdbits rbits imm8)
  | Asm.Prolw_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Prolw_ri rdbits imm8)
  | Asm.Prorl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Prorl_ri rdbits imm8)
  | Asm.Pcmpl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Pcmpl_rr rdbits rbits)
  | Asm.Pcmpl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 imm;
     OK (Pcmpl_ri rdbits imm32)
  | Asm.Ptestl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 imm;
     OK (Ptestl_ri rdbits imm32)
  | Asm.Ptestl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Ptestl_rr rdbits rbits)
  | Asm.Pcmov c rd r1 =>(*define a new function*)
     let cond := encode_testcond_u4 c in
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcmov cond rdbits rbits)
  | Asm.Psetcc c rd =>
     let cond := encode_testcond_u4 c in 
     do rdbits <- encode_ireg_u3 rd;
     OK (Psetcc cond rdbits)
  | Asm.Paddd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Paddd_ff rdbits rbits)
  | Asm.Psubd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Psubd_ff rdbits rbits)
  | Asm.Pmuld_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pmuld_ff rdbits rbits)
  | Asm.Pcomisd_ff r1 r2 =>
     do rdbits <- encode_freg_u3 r1;
     do rbits <- encode_freg_u3 r2;
     OK (Pcomisd_ff rdbits rbits)
  | Asm.Pxorps_f rd =>
     do rdbits <- encode_freg_u3 rd;
     OK (Pxorps_f rdbits rdbits)
  | Asm.Pxorps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pxorps_fm a rdbits)
  | Asm.Pandps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pandps_fm a rdbits)
  | Asm.Pjmp_l_rel ofs =>(*admitttttttttttttttttttttted*)
     do imm <- Z_encode_ofs_u32 ofs;
     OK (Pjmp_l_rel imm)
  | Asm.Pjmp_r r sg =>(*admitttttttttttttttttttttted*)
     do rdbits <- encode_ireg_u3 r;
     (*how to use sg*)
     OK (Pjmp_r rdbits)
  | Asm.Pjmp_m addr =>
     do a <- translate_Addrmode_AddrE addr;
     OK (Pjmp_m a)
  | Asm.Pnop =>
     OK (Pnop)
  | Asm.Pcall_r r sg => (*how to use sg*)
     do rdbits <- encode_ireg_u3 r;
     OK (Pcall_r rdbits)
  | Asm.Pret => OK(Pret)
  | Asm.Pret_iw imm => (*define encode_ofs_u16*)
     do imm16 <- encode_ofs_u16 imm;
     OK (Pret_iw imm16)
  | Asm.Pjcc_rel c ofs =>
     let cond := encode_testcond_u4 c in
     do imm <- Z_encode_ofs_u32 ofs;
     OK (Pjcc_rel cond imm)
  | Asm.Padcl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 imm;
     OK (Padcl_ri rdbits imm8)
  | Asm.Padcl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Padcl_rr rdbits rbits)
  | Asm.Paddl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Paddl_rr rdbits rbits)
  | Asm.Paddl_mi addr imm =>
     do a <- translate_Addrmode_AddrE addr;
     do imm32 <- encode_ofs_u32 imm;
     OK (Paddl_mi a imm32)
  | Asm.Pbsfl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsfl rdbits rbits)
  | Asm.Pbsrl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsrl rdbits rbits)
  | Asm.Pbswap32 rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pbswap32 rdbits)
  | Asm.Pmaxsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;
     OK (Pmaxsd rdbits rbits)
  | Asm.Pminsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;
     OK (Pminsd rdbits rbits)
  | Asm.Pmovsq_mr addr rs =>
     do a <- translate_Addrmode_AddrE addr;
     do rbits <- encode_freg_u3 rs;
     OK (Pmovsq_mr a rbits)
  | Asm.Pmovsq_rm rd addr =>
     do rdbits <- encode_freg_u3 rd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pmovsq_mr a rdbits)
  | Asm.Prep_movsl => OK(Prep_movsl)
  | Asm.Psbbl_rr  rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Psbbl_rr rdbits rbits)
  | Asm.Psqrtsd rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pbsqrtsd rdbits rbits)
  | Asm.Psubl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 imm;
     OK (Psubl_ri rdbits imm32)
  | _ => Error (msg "Not exists")
  end.

Definition translate_Instr (ofs: Z) (i:Instruction) : res instruction :=
  let translate_AddrE_Addrmode := translate_AddrE_Addrmode ofs (Instr_reloc_offset i) in
  match i with
  | Pmovl_rr rdbits r1bits =>
    do r1 <- decode_ireg r1bits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pmov_rr rd r1)
  | Pmovl_rm a rdbits =>
    do addr <- translate_AddrE_Addrmode a;
    do rd   <- decode_ireg rdbits;
    OK (Asm.Pmovl_rm rd addr)
  | Pmovl_ri rdbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Pmovl_ri rd imm)
  | Pmovl_mr a rbits =>
    do addr <- translate_AddrE_Addrmode a;
    do r    <- decode_ireg rbits;
    OK (Asm.Pmovl_mr addr r)
  | Pmovsd_ff rdbits r1bits =>
    do r1 <- decode_freg r1bits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pmovsd_ff rd r1)
  | Pmovsd_fm a rbits =>
    do addr <- translate_AddrE_Addrmode a;
    do r    <- decode_freg rbits;
    OK (Asm.Pmovsd_fm r addr)
  | Pmovsd_mf a rbits =>
    do r    <- decode_freg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsd_mf addr r)
  | Pmovss_fm a rbits =>
    do addr <- translate_AddrE_Addrmode a;
    do r    <- decode_freg rbits;
    OK (Asm.Pmovss_fm r addr)
  | Pmovss_mf a rbits =>
    do r    <- decode_freg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovss_mf addr r)
  | Pfldl_m a =>
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pfldl_m addr)
  | Pfstpl_m a =>
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pfstpl_m addr)
  | Pflds_m a =>
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pflds_m addr)
  | Pfstps_m a =>
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pfstps_m addr)
  | Pmovb_mr a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovb_mr addr r)
  | Pmovw_mr a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovw_mr addr r)
  | Pmovzb_rr rdbits rbits =>
    do r  <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pmovzb_rr rd r)
  | Pmovzb_rm a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovzb_rm r addr)
  | Pmovzw_rm a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovzw_rm r addr)
  | Pmovzw_rr rdbits rbits =>
    do rs <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pmovzw_rr rd rs)
  | Pmovsb_rm a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsb_rm r addr)
  | Pmovsb_rr rdbits rbits =>
    do rs <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pmovsb_rr rd rs)
  | Pmovw_rm a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovw_rm r addr)
  | Pmovb_rm a rdbits =>
    do rd   <- decode_ireg rdbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovb_rm rd addr)
  | Pmovsw_rm a rdbits =>
    do rd   <- decode_ireg rdbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsw_rm rd addr)
  | Pmovsw_rr rdbits rbits =>
    do rs <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pmovsw_rr rd rs)
  | Pnegl rbits =>
    do r    <- decode_ireg rbits;
    OK (Asm.Pnegl r)
  | Pleal a rbits =>
    do r    <- decode_ireg rbits;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pleal r addr)
  | Pcvttss2si_rf rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pcvttss2si_rf rd r1)
  | Pcvtsi2sd_fr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pcvtsi2sd_fr rd r1)
  | Pcvtsi2ss_fr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pcvtsi2ss_fr rd r1)
  | Pcvttsd2si_rf rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pcvttsd2si_rf rd r1)
  | Pcvtss2sd_ff rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pcvtss2sd_ff rd r1)
  | Pcvtsd2ss_ff rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pcvtsd2ss_ff rd r1)
  | Paddl_ri rdbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd <- decode_ireg rdbits;
    OK (Asm.Paddl_ri rd imm)
  | Psubl_rr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Psubl_rr rd r1)
  | Pimull_rr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pimull_rr rd r1)
  | Pimull_ri rdbits rbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd  <- decode_ireg rdbits;
    (* Why repeat *)
    OK (Asm.Pimull_ri rd imm)
  | Pmull_r rbits =>
    do r1 <- decode_ireg rbits;
    OK (Asm.Pmull_r r1)
  | Pcltd => OK (Asm.Pcltd)
  | Pdivl_r rbits =>
    do r1 <- decode_ireg rbits;
    OK (Asm.Pdivl r1)
  | Pidivl_r rbits =>
    do r1 <- decode_ireg rbits;
    OK (Asm.Pidivl r1)
  | Pandl_rr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pandl_rr rd r1)
  | Pandl_ri rdbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pandl_ri rd imm)
  | Porl_ri rdbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Porl_ri rd imm)
  | Porl_rr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Porl_rr rd r1)
  | Pxorl_rr rdbits rbits =>
    do rd <- decode_ireg rdbits;
    do r1 <- decode_ireg rbits;
    OK (Asm.Pxorl_rr rd r1)
  | Pxorl_ri rdbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Pxorl_ri rd imm)
  | Pnotl rdbits =>
    do rd <- decode_ireg rdbits;
    OK (Asm.Pnotl rd)
  | Psall_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Psall_ri rd imm)
  | Psall_rcl rdbits =>
    do rd <- decode_ireg rdbits;
    OK (Asm.Psall_rcl rd)
  | Pshrl_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Pshrl_ri rd imm)
  | Psarl_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Psarl_ri rd imm)
  | Psarl_rcl rdbits =>
    do rd <- decode_ireg rdbits;
    OK (Asm.Psarl_rcl rd)
  | Pshld_ri rdbits rbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do r1  <- decode_ireg rbits;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Pshld_ri rd r1 imm)
  | Prolw_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Prolw_ri rd imm)
  | Prorl_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Prorl_ri rd imm)
  | Pcmpl_rr rdbits rbits =>
    do r2 <- decode_ireg rbits;
    do r1 <- decode_ireg rdbits;
    OK (Asm.Pcmpl_rr r1 r2)
  | Pcmpl_ri rbits imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do rd  <- decode_ireg rbits;
    OK (Asm.Pcmpl_ri rd imm)
  | Ptestl_ri rdbits imm32 =>
    do rd  <- decode_ireg rdbits;
    do imm <- decode_ofs_u32 imm32;
    OK (Asm.Ptestl_ri rd imm)
  | Ptestl_rr rdbits rbits =>
    do r2 <- decode_ireg rbits;
    do r1 <- decode_ireg rdbits;
    OK (Asm.Ptestl_rr r1 r2)
  | Pcmov cond rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    do c  <- decode_testcond_u4 cond;
    OK (Asm.Pcmov c rd r1)
  | Psetcc cond rdbits =>
    do rd <- decode_ireg rdbits;
    do c  <- decode_testcond_u4 cond;
    OK (Asm.Psetcc c rd)
  | Paddd_ff rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Paddd_ff rd r1)
  | Psubd_ff rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Psubd_ff rd r1)
  | Pmuld_ff rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pmuld_ff rd r1)
  | Pcomisd_ff rdbits rbits =>
    do r2 <- decode_freg rbits;
    do r1 <- decode_freg rdbits;
    OK (Asm.Pcomisd_ff r1 r2)
  | Pxorps_f rdbits rbits =>
    (** why repeat *)
    do rd <- decode_freg rdbits;
    OK (Asm.Pxorps_f rd)
  | Pxorps_fm a rdbits =>
    do addr <- translate_AddrE_Addrmode a;
    do frd  <- decode_freg rdbits;
    OK (Asm.Pxorps_fm frd addr)
  | Pandps_fm a rdbits =>
    do addr <- translate_AddrE_Addrmode a;
    do frd  <- decode_freg rdbits;
    OK (Asm.Pandps_fm frd addr)
  | Pjmp_l_rel imm =>
    do ofs <- Z_decode_ofs_u32 imm;
    OK (Asm.Pjmp_l_rel ofs)
  | Pjmp_r rdbits =>
    do r <- decode_ireg rdbits;
    (*how to use sg*)
    OK (Asm.Pjmp_r r (mksignature [] Tvoid (mkcallconv None false false)))
  | Pjmp_m a =>
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pjmp_m addr)
  | Pnop => OK (Asm.Pnop)
  | Pcall_r rdbits => 
    (*how to use sg*)
    do r <- decode_ireg rdbits;
    OK (Asm.Pcall_r r (mksignature [] Tvoid (mkcallconv None false false)))
  | Pret => OK(Asm.Pret)
  | Pret_iw imm16 => 
    do imm <- decode_ofs_u16 imm16;
    OK (Asm.Pret_iw imm)
    (* Pjcc_rel type of ofs *)
  | Pjcc_rel cond imm =>
    do ofs <- Z_decode_ofs_u32 imm;
    do c   <- decode_testcond_u4 cond;
    OK (Asm.Pjcc_rel c ofs)
  | Padcl_ri rdbits imm8 =>
    do imm <- decode_ofs_u8 imm8;
    do rd  <- decode_ireg rdbits;
    OK (Asm.Padcl_ri rd imm)
  | Padcl_rr rdbits rbits =>
    do rd <- decode_ireg rdbits;
    do r2 <- decode_ireg rbits;
    OK (Asm.Padcl_rr rd r2)
  | Paddl_rr rdbits rbits =>
    do r2 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Paddl_rr rd r2)
  | Paddl_mi a imm32 =>
    do imm <- decode_ofs_u32 imm32;
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Paddl_mi addr imm)
  | Pbsfl rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pbsfl rd r1)
  | Pbsrl rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Pbsrl rd r1)
  | Pbswap32 rdbits =>
    do rd <- decode_ireg rdbits;
    OK (Asm.Pbswap32 rd)
  | Pmaxsd rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pmaxsd rd r1)
  | Pminsd rdbits rbits =>
    do r2 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Pminsd rd r2)
  | Pmovsq_mr addr rbits =>
    do a  <- translate_AddrE_Addrmode addr;
    do rs <- decode_freg rbits;
    OK (Asm.Pmovsq_mr a rs)
  | Pmovsq_rm a rdbits =>
    do addr <- translate_AddrE_Addrmode a;
    do rd   <- decode_freg rdbits;
    OK (Asm.Pmovsq_mr addr rd)
  | Prep_movsl => OK(Asm.Prep_movsl)
  | Psbbl_rr rdbits rbits =>
    do r1 <- decode_ireg rbits;
    do rd <- decode_ireg rdbits;
    OK (Asm.Psbbl_rr rd r1)
  | Pbsqrtsd rdbits rbits =>
    do r1 <- decode_freg rbits;
    do rd <- decode_freg rdbits;
    OK (Asm.Psqrtsd rd r1)
  | Psubl_ri rdbits imm32 =>
    do rd  <- decode_ireg rdbits;
    do imm <- decode_ofs_u32 imm32;
    OK (Asm.Psubl_ri rd imm)
  | _ => Error (msg "Unfinished")
  end.

Lemma instr_ofs_consistency : forall i I ofs,
    translate_instr ofs i = OK I ->
    instr_reloc_offset i = Instr_reloc_offset I.
Admitted.

Lemma Instr_ofs_consistency : forall i I ofs,
    translate_Instr ofs I = OK i ->
    Instr_reloc_offset I = instr_reloc_offset i.
Admitted.


Lemma translate_instr_consistency1 : forall ofs i I,
    translate_instr ofs i = OK I ->
    translate_Instr ofs I = OK i.
Proof.
  intros.
  destruct i; try discriminate;   (**r remove Err cases *)
  simpl in H; monadInv H;         (**r unfold `do` in H *)
  simpl; unfold bind;             (**r unfold translate_Instr in goal *)

  (**r try to solve reg to reg instructions, i.e. Pmovl_rr *)
  try (apply ireg_encode_consistency in EQ; rewrite EQ);
  try (apply ireg_encode_consistency in EQ1; rewrite EQ1);
  try (apply freg_encode_consistency in EQ; rewrite EQ);
  try (apply freg_encode_consistency in EQ1; rewrite EQ1);

  (**r try to solve reg to imm instructions *)
  try (apply encode_decode_ofs_u32 in EQ; unfold decode_ofs_u32; inversion EQ);
  try (apply encode_decode_ofs_u32 in EQ0; unfold decode_ofs_u32; inversion EQ0);
  try (apply encode_decode_ofs_u32 in EQ1; unfold decode_ofs_u32; inversion EQ1);
  try (apply encode_decode_ofs_u16 in EQ; unfold decode_ofs_u16; inversion EQ);
  try (apply encode_decode_ofs_u16 in EQ0; unfold decode_ofs_u16; inversion EQ0);
  try (apply encode_decode_ofs_u16 in EQ1; unfold decode_ofs_u16; inversion EQ1);
  try (apply encode_decode_ofs_u8 in EQ; unfold decode_ofs_u8; inversion EQ);
  try (apply encode_decode_ofs_u8 in EQ0; unfold decode_ofs_u8; inversion EQ0);
  try (apply encode_decode_ofs_u8 in EQ1; unfold decode_ofs_u8; inversion EQ1);

  try auto.

  - (* Asm.Pmovl_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovl_mr *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovl_fm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovl_mf *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovss_fm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovss_mf *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pfldl_m *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pfstpl_m *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pflds_m *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pfstps_m *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovb_mr *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovw_mr *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovzb_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovsb_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovzw_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovsw_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pleal *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - rewrite testcond_encode_consistency with (c := c); auto.
  - rewrite testcond_encode_consistency with (c := c); auto.
  - (* Asm.Pxorps_fm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pandps_fm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pjmp_r *) admit. (** TODO: signature needed *)
  - (* Asm.Pjmp_m *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pcall_r *) admit. (** TODO: signature needed *)
  - (* Asm.Paddl_mi *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovb_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovsq_mr *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovsq_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - (* Asm.Pmovw_rm *) admit. (** TODO: Instr_reloc_offset is admitted, this cannot be proved *)
  - apply Z_encode_decode_ofs_u32 in EQ. unfold Z_decode_ofs_u32. inversion EQ. subst. auto.
  - rewrite testcond_encode_consistency with (c := c); auto; apply Z_encode_decode_ofs_u32 in EQ. unfold Z_decode_ofs_u32. inversion EQ. auto.
Admitted.

Lemma translate_Instr_consistency1 : forall ofs i I,
    translate_Instr ofs I = OK i ->
    translate_instr ofs i = OK I.
Proof.
  intros.
  destruct I; try discriminate;   (**r remove Err cases *)
  simpl in H; monadInv H;         (**r unfold `do` in H *)
  simpl; unfold bind;             (**r unfold translate_Instr in goal *)

  (**r try to solve reg to reg instructions, i.e. Pmovl_rr *)
  try (apply ireg_decode_consistency in EQ; rewrite EQ);
  try (apply ireg_decode_consistency in EQ1; rewrite EQ1);
  try (apply freg_decode_consistency in EQ; rewrite EQ);
  try (apply freg_decode_consistency in EQ1; rewrite EQ1); try auto.

  - (* Psubl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Pbsqrtsd *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Pjcc_rel *) rewrite Z_decode_encode_ofs_u32 with (bs := uvar32_1); auto.
    apply testcond_decode_consistency with (c := x) in EQ. rewrite EQ.
    auto.
  - (* Pret_iw *) rewrite decode_encode_ofs_u16 with (bs := uvar16_0); auto.
  - (* Pjmp_l_rel *) rewrite Z_decode_encode_ofs_u32 with (bs := uvar32_0); auto.
  - (* Pxorps_f *) admit. (* args are strange *)
  - (* Psetcc *) apply testcond_decode_consistency with (c := x0) in EQ1. rewrite EQ1.
    auto.
  - (* Pcmov *) apply testcond_decode_consistency with (c := x1) in EQ0. rewrite EQ0.
    auto.
  - (* Ptestl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Pcmpl_ri *)  rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Prorl_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Prolw_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Pshld_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_2); auto.
  - (* Psarl_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Pshrl_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Psall_ri *) rewrite decode_encode_ofs_u8 with (bs := uvar8_1); auto.
  - (* Pxorl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Porl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Pandl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Pimull_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_2); auto. admit. (* args are repeated *)
  - (* Paddl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
  - (* Pmovl_ri *) rewrite decode_encode_ofs_u32 with (bs := uvar32_1); auto.
Admitted.

