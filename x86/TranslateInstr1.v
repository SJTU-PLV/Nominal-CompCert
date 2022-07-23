Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Axioms Globalenvs.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
(* Import Hex compcert.encode.Bits.Bits. *)
Require Import Coq.Logic.Eqdep_dec.
(* Require Import RelocBingen. *)
Require Import EncDecRet BPProperty.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* cannot be used in monadInv *)
Ltac destr_pair :=
  match goal with
  | [H: prod ?a ?b |- _ ] =>
    destruct H;try destr_pair
  end.

Ltac destr_prod x :=
  match type of x with
  | prod ?a ?b =>
    let a:= fresh "ProdL" in
    let b:= fresh "ProdR" in
    destruct x as (a & b);try destr_prod a
  end.


(* my monadinv *)
Ltac monadInv1 H :=
  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (destr_prod x);
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (destr_prod x1);
      try (destr_prod x2);
      try (monadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X; [try (monadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInv1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  monadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.



(** *CAV21: Instruction ,CompCertELF: instruction*)

(** * Encoding of instructions and functions *)

Definition encode_ireg (r: ireg) : res bits :=
  match r with
  | RAX => OK (b["000"])
  | RCX => OK (b["001"])
  | RDX => OK (b["010"])
  | RBX => OK (b["011"])
  | RSP => OK (b["100"])
  | RBP => OK (b["101"])
  | RSI => OK (b["110"])
  | RDI => OK (b["111"])
  | _ => Error (msg "Encoding of register not supported")
  end.

(*encode 64bit reg ,return *)
Definition encode_ireg64 (r:ireg) :(bits*bits):=
  match r with
  | RAX =>  (b["0"],b[ "000"])
  | RBX =>  (b["0"],b[ "011"])
  | RCX =>  (b["0"],b[ "001"])
  | RDX =>  (b["0"],b[ "010"])
  | RSI =>  (b["0"],b[ "110"])
  | RDI =>  (b["0"],b[ "111"])
  | RBP =>  (b["0"],b[ "101"])
  | RSP =>  (b["0"],b[ "100"])
  | R8 => (b["1"],b["000"])
  | R9 => (b["1"],b["001"])
  | R10 =>  (b["1"],b["010"])
  | R11 =>  (b["1"],b["011"])
  | R12 =>  (b["1"],b["100"])
  | R13 =>  (b["1"],b["101"])
  | R14 => (b["1"],b["110"])
  | R15 => (b["1"],b["111"])
end.
   

Definition encode_freg (r: freg) : res bits :=
  match r with
  | XMM0 => OK (b["000"])
  | XMM1 => OK (b["001"])
  | XMM2 => OK (b["010"])
  | XMM3 => OK (b["011"])
  | XMM4 => OK (b["100"])
  | XMM5 => OK (b["101"])
  | XMM6 => OK (b["110"])
  | XMM7 => OK (b["111"])
  | _ => Error (msg "Encoding of freg not supported")
  end.

Definition encode_freg64 (r:freg) :(bits*bits):=
  match r with
  | XMM0  =>  (b["0"],b["000"])
  | XMM1  =>  (b["0"],b["001"])
  | XMM2  =>  (b["0"],b["010"])
  | XMM3  =>  (b["0"],b["011"])
  | XMM4  =>  (b["0"],b["100"])
  | XMM5  =>  (b["0"],b["101"])
  | XMM6  =>  (b["0"],b["110"])
  | XMM7  =>  (b["0"],b["111"])
  | XMM8 => (b["1"],b["000"])
  | XMM9 => (b["1"],b["001"])
  | XMM10  =>  (b["1"],b["010"])
  | XMM11  =>  (b["1"],b["011"])
  | XMM12  =>  (b["1"],b["100"])
  | XMM13  =>  (b["1"],b["101"])
  | XMM14  => (b["1"],b["110"])
  | XMM15  => (b["1"],b["111"])
end.


Definition encode_scale (s: Z) : res bits :=
  match s with
  | 1 => OK b["00"]
  | 2 => OK b["01"]
  | 4 => OK b["10"]
  | 8 => OK b["11"]
  | _ => Error (msg "Translation of scale failed")
  end.


Program Definition zero32 : u32 :=
  bytes_to_bits_opt (bytes_of_int 4 0).

Program Definition zero1: u1 :=
  b["0"].

Program Definition one1: u1 :=
  b["1"].

Program Definition zero2: u2 :=
  b["00"].

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

Definition decode_ireg_u4 (extend: bool) (bs:u3) : ireg :=
  if extend then
    match (proj1_sig bs) with
    | [false;false;false] => R8
    | [false;false;true] => R9
    | [false;true;false] => R10
    | [false;true;true] => R11
    | [true;false;false] => R12
    | [true;false;true] => R13
    | [true;true;false] => R14
    | [true;true;true] => R15
    | _ => RAX                   (* impossible *)
    end
  else
    match (proj1_sig bs) with
    | [false;false;false]=> RAX
    | [false;false;true]=> RCX
    | [false;true;false]=> RDX
    | [false;true;true] => RBX
    | [true;false;false]=> RSP
    | [true;false;true] => RBP
    | [true;true;false] => RSI
    | [true;true;true] => RDI
    | _ => RAX                   (* impossible *)
    end.

    
Program Definition encode_ireg_u4 (r:ireg) : res (u1*u3):=
  let (R,b) := encode_ireg64 r in
  if assertLength R 1 then
    if assertLength b 3 then
      OK (R,b)
    else Error(msg"impossible")
  else Error(msg"impossible").



Definition decode_freg_u4 (extend: bool) (bs:u3) : freg :=
  if extend then
    match (proj1_sig bs) with
    | [false;false;false]=> XMM8
    | [false;false;true] => XMM9
    | [false;true;false] => XMM10
    | [false;true;true]  => XMM11
    | [true;false;false] => XMM12
    | [true;false;true]  => XMM13
    | [true;true;false]  => XMM14
    | [true;true;true]   => XMM15
    | _ => XMM0                  (* impossible *)
    end
  else
    match (proj1_sig bs) with
    | [false;false;false] => XMM0
    | [false;false;true]  => XMM1 
    | [false;true;false]  => XMM2
    | [false;true;true]   => XMM3
    | [true;false;false]  => XMM4
    | [true;false;true]   => XMM5
    | [true;true;false]   => XMM6
    | [true;true;true]    => XMM7
    | _ => XMM0
    end.

Program Definition encode_freg_u3 (r:freg) : res u3 :=
  do b <- encode_freg r;
  if assertLength b 3 then
    OK (exist _ b _)
  else Error (msg "impossible").


Program Definition encode_freg_u4 (r:freg) : res (u1*u3):=
  let (R,b) := encode_freg64 r in
  if assertLength R 1 then
    if assertLength b 3 then
      OK (R,b)
    else Error(msg"impossible")
  else Error(msg"impossible").

(** *Consistency theorem for register encoding and decoding *)

Definition decode_u1 (a:u1) : bool :=
  match (proj1_sig a ) with
  | [b] => b
  | _ => true
  end.

Coercion decode_u1 : u1 >-> bool.

Remark decode_ireg_u4_inject1: forall reg1 reg2 e1 e2,
    decode_ireg_u4 e1 reg1 = decode_ireg_u4 e2 reg2 ->
    e1 = e2.
Proof.
  destruct reg1;destruct reg2. unfold decode_ireg_u4.
  destruct e1;destruct e2;simpl;auto;
  do 4 (destruct x;simpl in e;try congruence);
  do 4 (destruct x0;simpl in e0;try congruence);
  destruct b;destruct b0;destruct b1;simpl;auto;try congruence;
  destruct b2;destruct b3;destruct b4;simpl;auto;try congruence.
Qed.

Remark decode_ireg_u4_inject2: forall reg1 reg2 e1 e2,
    decode_ireg_u4 e1 reg1 = decode_ireg_u4 e2 reg2 ->
    reg1 = reg2.
Proof.
  destruct e1;destruct e2;destruct reg1;destruct reg2;simpl;auto;try congruence;
    try (do 4 (destruct x;simpl in e;try congruence);
  do 4 (destruct x0;simpl in e0;try congruence);
  destruct b;destruct b0;destruct b1;
    destruct b2;destruct b3;destruct b4;
    intros;simpl;auto;try congruence;f_equal;apply proof_irr).
Qed.
  
Lemma encode_ireg_u4_consistency: forall reg extend bs,
    encode_ireg_u4 reg = OK (extend,bs) ->
    decode_ireg_u4 extend bs = reg.
Proof.
  unfold encode_ireg_u4. unfold encode_ireg64.
  intro reg. destruct reg;simpl;intros;inv H;simpl;auto.
Qed.

Lemma encode_ireg_u3_consistency: forall reg bs,
    encode_ireg_u3 reg = OK bs ->
    decode_ireg_u4 false bs = reg.
Proof.
  unfold encode_ireg_u3. unfold encode_ireg.
  intro reg. destruct reg;simpl;intros;inv H;simpl;auto.
Qed.
  
Lemma encode_freg_u4_consistency: forall reg extend bs,
    encode_freg_u4 reg = OK (extend,bs) ->
    decode_freg_u4 extend bs = reg.
Proof.
  unfold encode_freg_u4. unfold encode_freg64.
  intro reg. destruct reg;simpl;intros;inv H;simpl;auto.
Qed.

Lemma encode_freg_u3_consistency: forall reg bs,
    encode_freg_u3 reg = OK bs ->
    decode_freg_u4 false bs = reg.
Proof.
  unfold encode_ireg_u3. unfold encode_ireg.
  intro reg. destruct reg;simpl;intros;inv H;simpl;auto.
Qed.
  


(* FIXME *)
Program Definition encode_ofs_u64 (ofs:Z) : res u64 :=
  let ofs64 := bytes_to_bits_opt (bytes_of_int 8 ofs) in
  if assertLength ofs64 64 then
    OK (exist _ ofs64 _)
  else Error (msg "impossible").



Program Definition encode_scale_u2 (ss: Z) :res u2 :=
  do s <- encode_scale ss;
  if assertLength s 2 then
    OK (exist _ s _)
  else Error (msg "impossible").

Definition decode_scale (bs: u2) : Z :=
  let bs' := proj1_sig bs in
  match bs' with
  | [false;false] => 1
  | [false;true] => 2
  | [true;false] => 4
  | [true;true] => 8
  | _ => 1
  end.

Lemma encode_scale_consistency :
  forall ss encoded,
  encode_scale_u2 ss = OK(encoded) ->
  decode_scale encoded = ss.
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

Program Definition encode_ofs_u8 (ofs:Z) :res u8 :=
  let ofs8 := bytes_to_bits_opt (bytes_of_int 1 ofs) in
  if assertLength ofs8 8 then
    OK (exist _ ofs8 _)
  else Error (msg "impossible").

Definition decode_ofs_u8 (bs:u8) : int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  Int.repr z.

Program Definition encode_ofs_u16 (ofs:Z) :res u16 :=
  let ofs16 := bytes_to_bits_opt (bytes_of_int 2 ofs) in
  if assertLength ofs16 16 then
    OK (exist _ ofs16 _)
  else Error (msg "impossible in encode_ofs_u16").

Definition decode_ofs_u16 (bs:u16) : int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  Int.repr z.

Program Definition encode_ofs_u32 (ofs:Z) :res u32 :=
  let ofs32 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs32 32 then
    OK (exist _ ofs32 _)
  else Error (msg "impossible").

Definition decode_ofs_u32 (bs:u32) : int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  Int.repr z.

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

(*change it to total function*)
Definition decode_testcond_u4 (bs:u4) : res testcond :=
  let bs' := proj1_sig bs in
  match bs' with
  | [false;true;false;false] => OK Cond_e
  | [false;true;false;true] => OK Cond_ne
  | [false;false;true;false] => OK Cond_b
  | [false;true;true;false] => OK Cond_be
  | [false;false;true;true] => OK Cond_ae
  | [false;true;true;true] => OK Cond_a
  | [true;true;false;false] => OK Cond_l
  | [true;true;true;false] => OK Cond_le
  | [true;true;false;true] => OK Cond_ge
  | [true;true;true;true] => OK Cond_g
  | [true;false;true;false] => OK Cond_p
  | [true;false;true;true] => OK Cond_np
  | _ => Error (msg "decode testcond error")
  end.

(** *Consistency Lemma for offset,testcond *)
Lemma encode_testcond_consistency : forall c,
  decode_testcond_u4 (encode_testcond_u4 c) = OK(c).
Proof.
  (**r enumerate all possibility of c *)
  destruct c;
  simpl; unfold char_to_bool; simpl;
  intros; subst;
  unfold decode_testcond_u4; simpl;
  auto.
Qed.

Lemma encode_ofs_u16_consistency:forall ofs l,
    encode_ofs_u16 (Int.intval ofs) = OK l ->
    decode_ofs_u16 l = ofs.
Proof.
Admitted.


Lemma encode_ofs_u8_consistency:forall ofs l,
    encode_ofs_u8 (Int.intval ofs) = OK l ->
    decode_ofs_u8 l = ofs.
Proof.
Admitted.

Lemma encode_ofs_u32_consistency_aux:forall ofs l,
    0 <= ofs < Int.modulus ->
    encode_ofs_u32 ofs = OK l ->
    Int.intval (decode_ofs_u32 l) = ofs.
Admitted.


Lemma encode_ofs_u32_consistency:forall ofs l,
    encode_ofs_u32 (Int.intval ofs) = OK l ->
    decode_ofs_u32 l = ofs.
Proof.
  unfold encode_ofs_u32.
  intros ofs l H.
  set (val:= (bytes_to_bits_opt (bytes_of_int 4 (Int.intval ofs)))) in *.
  destr_in H. inv H. unfold decode_ofs_u32.
  simpl. destruct ofs. Transparent Int.repr.
  unfold Int.repr. cbn [Int.intval] in val.
  eapply Int.mkint_eq.
  clear e.
  unfold val.
Admitted.


Hint Resolve encode_ireg_u4_consistency encode_freg_u4_consistency encode_ofs_u32_consistency encode_ofs_u8_consistency encode_ofs_u16_consistency encode_testcond_consistency encode_scale_consistency encode_ofs_u32_consistency_aux: encdec.


  
Section WITH_RELOC_OFS_MAP.

Variable rtbl_ofs_map: reloc_ofs_map_type.


Definition get_reloc_addend (ofs:Z) : res Z :=
  match ZTree.get ofs rtbl_ofs_map with
  | None => Error [MSG "Cannot find the relocation entry at the offset "; POS (Z.to_pos ofs)]
  | Some e => OK (reloc_addend e)
  end.

Definition get_instr_reloc_addend (ofs:Z) (i:instruction) : res Z :=
  do iofs <- instr_reloc_offset i;
  get_reloc_addend (ofs + iofs).


Definition get_instr_reloc_addend' (ofs:Z): res Z :=
  get_reloc_addend ofs.


Definition translate_Addrmode_AddrE_aux32 (obase: option ireg) (oindex: option (ireg*Z)) (ofs32:u32) : res AddrE :=
  match obase,oindex with
  | None,None =>
    if Archi.ptr64 then
      do rsp <- encode_ireg_u3 RSP;
    (* do not use rip-relative addressing *)
      OK (AddrE9 zero2 rsp ofs32)
    else
      OK (AddrE11 ofs32)
  | Some base,None =>
    do r <- encode_ireg_u3 base;
    do rsp <- encode_ireg_u3 RSP;
    OK (AddrE5 zero2 rsp r ofs32)
  | None,Some (idx,ss) =>
    if ireg_eq idx RSP then
      (* OK (AddrE7 zero32) *)
      Error (msg "index can not be RSP")    
    else
      do index <- encode_ireg_u3 idx;
      do scale <- encode_scale_u2 ss;    
      OK (AddrE9 scale index ofs32)
  | Some base,Some (idx,ss) =>
    if ireg_eq idx RSP then
      Error (msg "index can not be RSP")
            (* OK (AddrE4 breg zero32)            *)
    else
      do scale <- encode_scale_u2 ss;
      do index <- encode_ireg_u3 idx;
      do breg <- encode_ireg_u3 base;    
      OK (AddrE5 scale index breg ofs32)
  end.


(* Translate ccelf addressing mode to cav21 addr mode *)
(* sofs: instruction ofs, res_iofs: relocated location in the instruction*)
(* TODO: 64bit mode, the addend is placed in the relocation entry *)
Definition translate_Addrmode_AddrE (sofs: Z) (res_iofs: res Z) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- res_iofs;
        do addend <- get_instr_reloc_addend' (iofs + sofs);
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          (*32bit mode the addend placed in instruction *)
          do imm32 <- encode_ofs_u32 addend;
          translate_Addrmode_AddrE_aux32 obase oindex imm32
        else Error (msg "addend is not equal to ofs")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      do iofs <- res_iofs;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        if (0 <=? ofs) && (ofs <? Int.modulus) then
          do ofs32 <- encode_ofs_u32 ofs;
          translate_Addrmode_AddrE_aux32 obase oindex ofs32
        else Error (msg "offset overflow in translate addrmode 32")
      | _ => Error (msg "impossible relocation entry in addrmode")
      end
    end
  end.


(* u1:X u1:B *)
Definition translate_Addrmode_AddrE_aux64 (obase: option ireg) (oindex: option (ireg*Z)) (ofs32:u32) : res (AddrE*u1*u1) :=
  match obase,oindex with
  | None,None =>
    if Archi.ptr64 then
      do rsp <- encode_ireg_u3 RSP;
      (* do not use rip-relative addressing *)
      OK ((AddrE9 zero2 rsp ofs32),zero1,zero1)
    else
      Error (msg "Encode 64bit addrmode in 32bit mode ")
  | Some base,None =>
    do B_r <- encode_ireg_u4 base;
    let (B,r) := B_r in
    do rsp <- encode_ireg_u3 RSP;
    OK ((AddrE5 zero2 rsp r ofs32),zero1,B)
    (* if ireg_eq base RSP then *)
    (*   OK ((AddrE4 r ofs32),zero1,B) *)
    (* else *)
    (*   OK ((AddrE6 r ofs32),zero1,B) *)
  | None,Some (idx,ss) =>
    if ireg_eq idx RSP then
      (* OK (AddrE7 zero32) *)
      Error (msg "index can not be RSP")    
    else
      do X_index <- encode_ireg_u4 idx;
      let (X,index) := X_index in
      do scale <- encode_scale_u2 ss;
      OK ((AddrE9 scale index ofs32),X,zero1)
  | Some base,Some (idx,ss) =>
    if ireg_eq idx RSP then
      Error (msg "index can not be RSP")
            (* OK (AddrE4 breg zero32)*)
    else
      do scale <- encode_scale_u2 ss;
      do X_index <- encode_ireg_u4 idx;
      do B_breg <- encode_ireg_u4 base;
      let (X,index) := X_index in
      let (B,breg) := B_breg in
      OK ((AddrE5 scale index breg ofs32),X,B)
  end.


(* 64bit addrmode translation, u1: X, u1:B *)
Definition translate_Addrmode_AddrE64 (sofs: Z) (res_iofs: res Z) (addr:addrmode): res (AddrE*u1*u1) :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- res_iofs;
        do addend <- get_instr_reloc_addend' (iofs + sofs);
        (* addend is the offset of id and access point *)
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          do imm32 <- encode_ofs_u32 addend;
          translate_Addrmode_AddrE_aux64 obase oindex imm32
        else Error (msg "64bit: addend is not equal to ofs")
      | _ => Error(msg "64bit: id must be 1")
      end
    | inl ofs =>
      do iofs <- res_iofs;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        if (0 <=? ofs) && (ofs <? Int.modulus) then
          do ofs32 <- encode_ofs_u32 ofs;
          translate_Addrmode_AddrE_aux64 obase oindex ofs32
        else Error (msg "offset overflow in translate addrmode 64")
      | _ => Error (msg "64bit: impossible relocation entry in addrmode")
      end
    end
  end.

(* TODO: decode addrE to addrmode in 64bit mode *)
Definition translate_AddrE_Addrmode (sofs: Z) (res_iofs: res Z) (X B: bool) (addr:AddrE) : res addrmode :=
  (* addrmode must pass reloc offset test *)
  do iofs <- res_iofs;
  match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
  | Some e =>
    match addr with
    | AddrE0 _ => Error (msg "AddrE0 impossible in addrmode decoding") 
    | AddrE5 s i b imm =>
      let base := decode_ireg_u4 B b in
      let index := decode_ireg_u4 X i in
      let scale := decode_scale s in
      let ofs := Ptrofs.of_int (decode_ofs_u32 imm) in
      if ireg_eq index RSP then
        OK (Addrmode (Some base) None (inr (xH,ofs)))
      else
        OK (Addrmode (Some base) (Some (index,scale)) (inr (xH,ofs)))
    | AddrE9 s i imm =>
      let scale := decode_scale s in
      let ofs := Ptrofs.of_int (decode_ofs_u32 imm)in
      let index := decode_ireg_u4 X i in
      if ireg_eq index RSP then
        if Archi.ptr64 then
          OK (Addrmode None None (inr (xH,ofs)))
        else Error (msg "impossible: translate_AddrE_Addrmode")
      else
        OK (Addrmode None (Some (index,scale)) (inr (xH,ofs)))
    | AddrE11 imm =>
      let ofs := Ptrofs.of_int (decode_ofs_u32 imm)in
      OK (Addrmode None None (inr (xH,ofs)))
    end
  (* mostly copy above *)
  | None =>
    match addr with
    | AddrE0 _ => Error (msg "AddrE0 impossible in addrmode decoding") 
    | AddrE5 s i b imm =>
      let base := decode_ireg_u4 B b in
      let index := decode_ireg_u4 X i in
      let scale := decode_scale s in
      let ofs := Int.intval (decode_ofs_u32 imm) in
      if ireg_eq index RSP then
        OK (Addrmode (Some base) None (inl ofs))
      else
        OK (Addrmode (Some base) (Some (index,scale)) (inl ofs))       
    | AddrE9 s i imm =>
      let scale := decode_scale s in
      let ofs := Int.intval (decode_ofs_u32 imm) in
      let index := decode_ireg_u4 X i in
      if ireg_eq index RSP then
        if Archi.ptr64 then
          OK (Addrmode None None (inl ofs))
        else Error (msg "impossible: translate_AddrE_Addrmode")
      else
        OK (Addrmode None (Some (index,scale)) (inl ofs))
    | AddrE11 imm =>
      let ofs := Int.intval (decode_ofs_u32 imm) in
      OK (Addrmode None None (inl ofs))
    end
  end.

(** *Consistency theorem for AddrE and Addrmode  *)
Definition not_AddrE0 a:bool:=
  match a with
  | AddrE0 _ => false
  | _ => true
  end.

Lemma transl_addr_consistency32: forall addr a sofs res_iofs,
    translate_Addrmode_AddrE sofs res_iofs addr = OK a ->
    not_AddrE0 a = true /\ translate_AddrE_Addrmode sofs res_iofs false false a = OK addr.
Proof.
  unfold translate_Addrmode_AddrE.
  destruct addr.
  destruct base;destruct ofs;intros ad sofs res_iofs H.
  - destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0. simpl in EQ2. destruct p. simpl in EQ2.
      destr_in EQ2. monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo. admit.
    + destruct p0. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      simpl in EQ3. destruct p.  destr_in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  -  destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux32 in EQ2.
      monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo.
      admit.
    + destruct p. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      unfold translate_Addrmode_AddrE_aux32 in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  - destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0. simpl in EQ2. destruct p.
      destr_in EQ2. monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo. admit.
    + destruct p0. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      simpl in EQ3. destruct p.  destr_in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  -  destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux32 in EQ2.
      destr_in EQ2.
      * monadInv EQ2.
        split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo. rewrite Heqb0.
        admit.
      * inv EQ2. split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo.
        do 3 f_equal. auto with encdec.
        apply andb_true_iff  in Heqb. destruct Heqb.
        assert (0 <= z < Int.modulus).
        split. 
        apply Z.leb_le;eauto. apply Z.ltb_lt;eauto.  
        auto with encdec.
    + destruct p. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      unfold translate_Addrmode_AddrE_aux32 in EQ3. destr_in EQ3.
      * monadInv EQ3.
        split. simpl;auto.
        unfold get_instr_reloc_addend' in EQ1.
        unfold get_reloc_addend in EQ1. destr_in EQ1.
        unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
        rewrite Heqb0. admit.
      * inv EQ3. split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        unfold get_instr_reloc_addend' in EQ1.
        unfold get_reloc_addend in EQ1. destr_in EQ1.
        do 4 f_equal.
        apply Z.eqb_eq in Heqb. subst.
        destruct i0. simpl in *.
        unfold Ptrofs.of_int. unfold Int.unsigned.
        erewrite (encode_ofs_u32_consistency_aux intval).
        Transparent Ptrofs.repr. unfold Ptrofs.repr.
        eapply Ptrofs.mkint_eq. admit.
        unfold Int.modulus. unfold Int.wordsize.
        unfold Ptrofs.modulus in *. unfold Ptrofs.wordsize in *.
        unfold Wordsize_Ptrofs.wordsize in *. rewrite Heqb0 in *.
        unfold Wordsize_32.wordsize. lia.
        auto with encdec.
Admitted.

(* mostly same as 32bit mode *)
Lemma transl_addr_consistency64: forall addr a sofs res_iofs x b,
    translate_Addrmode_AddrE64 sofs res_iofs addr = OK (a, x, b) ->
    not_AddrE0 a = true /\ translate_AddrE_Addrmode sofs res_iofs x b a = OK addr.

  unfold translate_Addrmode_AddrE64.
  destruct addr.
  destruct base;destruct ofs;intros ad sofs res_iofs x b H.
  - destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0. simpl in EQ2. destruct p.
      destr_in EQ2. monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo. admit.
    + destruct p0. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      simpl in EQ3. destruct p.  destr_in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  -  destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux64 in EQ2.
      monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo.
      admit.
    + destruct p. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      unfold translate_Addrmode_AddrE_aux64 in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  - destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0. simpl in EQ2. destruct p.
      destr_in EQ2. monadInv EQ2.
      split. simpl;auto.
      unfold translate_AddrE_Addrmode. cbn [bind].
      rewrite Heqo. admit.
    + destruct p0. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      simpl in EQ3. destruct p.  destr_in EQ3. monadInv EQ3.
      split. simpl;auto.
      unfold get_instr_reloc_addend' in EQ1.
      unfold get_reloc_addend in EQ1. destr_in EQ1.
      unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
      admit.
  -  destr_in H.
    + monadInv H. destr_in EQ0. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux64 in EQ2.
      destr_in EQ2.
      * monadInv EQ2.
        split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo. rewrite Heqb1.
        admit.
    + destruct p. destr_in H.
      monadInv H. destr_in EQ2. monadInv EQ2.
      unfold translate_Addrmode_AddrE_aux64 in EQ3. destr_in EQ3.
      * monadInv EQ3.
        split. simpl;auto.
        unfold get_instr_reloc_addend' in EQ1.
        unfold get_reloc_addend in EQ1. destr_in EQ1.
        unfold translate_AddrE_Addrmode.  cbn [bind]. rewrite Heqo.
        rewrite Heqb1. admit.
Admitted.


(** *REX: Extended register and addrmode encoding *)

Definition encode_rex_prefix_r (r: ireg) : res (list Instruction * u3) :=
  if check_extend_reg r then
    do rbits <- encode_ireg_u3 r;
    OK ([], rbits)
  else
    if Archi.ptr64 then
      do Brbits <- encode_ireg_u4 r;
      let (B, rbits) := Brbits in
      OK ([REX_WRXB zero1 zero1 zero1 B], rbits)
    else
      Error (msg "encode extend register in 32bit mode! ").

(* unused *)
Definition encode_rex_prefix_f (fr: freg) : res (list Instruction * u3) :=
  if check_extend_freg fr then
    do rbits <- encode_freg_u3 fr;
    OK ([], rbits)
  else
    if Archi.ptr64 then
      do Brbits <- encode_freg_u4 fr;
      let (B, rbits) := Brbits in
      OK ([REX_WRXB zero1 zero1 zero1 B], rbits)
    else
      Error (msg "encode extend register in 32bit mode! ").


Definition encode_rex_prefix_addr (instr_ofs: Z) (res_iofs: res Z) (addr: addrmode) : res (list Instruction * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE instr_ofs res_iofs in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 instr_ofs res_iofs in
  if check_extend_addrmode addr then
    do a <- translate_Addrmode_AddrE addr;
    OK ([], a)
  else
    if Archi.ptr64 then
      do addr_X_B <- translate_Addrmode_AddrE64 addr;
      let (a_X, B) := addr_X_B in
      let (a,X) := a_X in
      OK ([REX_WRXB zero1 zero1 X B], a)
    else
      Error (msg "encode extend addrmode in 32bit mode! ").


(** 32bit mode, r: R b: B, return option rex, encoded r, encoded b*)
Definition encode_rex_prefix_rr  (r b: ireg) : res (list Instruction * u3 * u3) :=
  if check_extend_reg r then
    if check_extend_reg b then
      do rbits <- encode_ireg_u3 r;
      do bbits <- encode_ireg_u3 b;
      OK ([], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_ireg_u4 b;
        let (B, bbits) := B_bbits in
        do rbits <- encode_ireg_u3 r;
        OK ([REX_WRXB zero1 zero1 zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ")
  else
    do R_rbits <- encode_ireg_u4 r;
    let (R, rbits) := R_rbits in
    if check_extend_reg b then
      do bbits <- encode_ireg_u3 b;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_ireg_u4 b;
        let (B, bbits) := B_bbits in
        OK ([REX_WRXB zero1 R zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ").

Definition encode_rex_prefix_ra (instr_ofs: Z) (res_iofs: res Z) (r: ireg) (addr: addrmode) : res (list Instruction * u3 * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE instr_ofs res_iofs in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 instr_ofs res_iofs in
  if check_extend_reg r then
    if check_extend_addrmode addr then
      do rbits <- encode_ireg_u3 r;
      do a <- translate_Addrmode_AddrE addr;
      OK ([], rbits, a)
    else
      if Archi.ptr64 then
        do rbits <- encode_ireg_u3 r;
        do addr_X_B <- translate_Addrmode_AddrE64 addr;
        let (a_X, B) := addr_X_B in
        let (a,X) := a_X in
        OK ([REX_WRXB zero1 zero1 X B], rbits, a)
      else
        Error (msg "encode extend register in 32bit mode! ")
  else
    if check_extend_addrmode addr then
      do Rrbits <- encode_ireg_u4 r;
      let (R, rbits) := Rrbits in
      do a <- translate_Addrmode_AddrE addr;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, a)
    else
      if Archi.ptr64 then
        do Rrbits <- encode_ireg_u4 r;
        let (R, rbits) := Rrbits in      
        do addr_X_B <- translate_Addrmode_AddrE64 addr;
        let (a_X, B) := addr_X_B in
        let (a,X) := a_X in
        OK ([REX_WRXB zero1 R X B], rbits, a)
      else
        Error (msg "encode extend addrmode in 32bit mode! ").

Definition encode_rex_prefix_ff  (r b: freg) : res (list Instruction * u3 * u3) :=
  if check_extend_freg r then
    if check_extend_freg b then
      do rbits <- encode_freg_u3 r;
      do bbits <- encode_freg_u3 b;
      OK ([], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_freg_u4 b;
        let (B, bbits) := B_bbits in
        do rbits <- encode_freg_u3 r;
        OK ([REX_WRXB zero1 zero1 zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ")
  else
    do R_rbits <- encode_freg_u4 r;
    let (R, rbits) := R_rbits in
    if check_extend_freg b then
      do bbits <- encode_freg_u3 b;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_freg_u4 b;
        let (B, bbits) := B_bbits in
        OK ([REX_WRXB zero1 R zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ").


Definition encode_rex_prefix_rf  (r: ireg) (b: freg) : res (list Instruction * u3 * u3) :=
  if check_extend_reg r then
    if check_extend_freg b then
      do rbits <- encode_ireg_u3 r;
      do bbits <- encode_freg_u3 b;
      OK ([], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_freg_u4 b;
        let (B, bbits) := B_bbits in
        do rbits <- encode_ireg_u3 r;
        OK ([REX_WRXB zero1 zero1 zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ")
  else
    do R_rbits <- encode_ireg_u4 r;
    let (R, rbits) := R_rbits in
    if check_extend_freg b then
      do bbits <- encode_freg_u3 b;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_freg_u4 b;
        let (B, bbits) := B_bbits in
        OK ([REX_WRXB zero1 R zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ").

Definition encode_rex_prefix_fr  (r: freg) (b: ireg): res (list Instruction * u3 * u3) :=
  if check_extend_freg r then
    if check_extend_reg b then
      do rbits <- encode_freg_u3 r;
      do bbits <- encode_ireg_u3 b;
      OK ([], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_ireg_u4 b;
        let (B, bbits) := B_bbits in
        do rbits <- encode_freg_u3 r;
        OK ([REX_WRXB zero1 zero1 zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ")
  else
    do R_rbits <- encode_freg_u4 r;
    let (R, rbits) := R_rbits in
    if check_extend_reg b then
      do bbits <- encode_ireg_u3 b;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, bbits)
    else
      if Archi.ptr64 then
        do B_bbits <- encode_ireg_u4 b;
        let (B, bbits) := B_bbits in
        OK ([REX_WRXB zero1 R zero1 B], rbits, bbits)
      else
        Error (msg "encode extend two register in 32bit mode! ").


Definition encode_rex_prefix_fa (instr_ofs: Z) (res_iofs: res Z) (r: freg) (addr: addrmode) : res (list Instruction * u3 * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE instr_ofs res_iofs in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 instr_ofs res_iofs in
  if check_extend_freg r then
    if check_extend_addrmode addr then
      do rbits <- encode_freg_u3 r;
      do a <- translate_Addrmode_AddrE addr;
      OK ([], rbits, a)
    else
      if Archi.ptr64 then
        do rbits <- encode_freg_u3 r;
        do addr_X_B <- translate_Addrmode_AddrE64 addr;
        let (a_X, B) := addr_X_B in
        let (a,X) := a_X in
        OK ([REX_WRXB zero1 zero1 X B], rbits, a)
      else
        Error (msg "encode extend register in 32bit mode! ")
  else
    if check_extend_addrmode addr then
      do Rrbits <- encode_freg_u4 r;
      let (R, rbits) := Rrbits in
      do a <- translate_Addrmode_AddrE addr;
      OK ([REX_WRXB zero1 R zero1 zero1], rbits, a)
    else
      if Archi.ptr64 then
        do Rrbits <- encode_freg_u4 r;
        let (R, rbits) := Rrbits in      
        do addr_X_B <- translate_Addrmode_AddrE64 addr;
        let (a_X, B) := addr_X_B in
        let (a,X) := a_X in
        OK ([REX_WRXB zero1 R X B], rbits, a)
      else
        Error (msg "encode extend addrmode in 32bit mode! ").






(** return (option rex prefix, instruction *)
(** REX_WRXB: B R W X  *)
Definition translate_instr (instr_ofs: Z) (i:instruction) : res (list Instruction) :=
  let res_iofs := instr_reloc_offset i in
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE instr_ofs res_iofs in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 instr_ofs res_iofs in
  let encode_rex_prefix_ra := encode_rex_prefix_ra instr_ofs res_iofs in
  let encode_rex_prefix_fa := encode_rex_prefix_fa instr_ofs res_iofs in
  let encode_rex_prefix_addr := encode_rex_prefix_addr instr_ofs res_iofs in
  match i with
  | Pmov_rr rd r1 =>
    if Archi.ptr64 then
      do Rrdbits <- encode_ireg_u4 rd;
      do Brsbits <- encode_ireg_u4 r1;
      let (B, rsbits) := Brsbits in
      let (R, rdbits) := Rrdbits in
      OK ([REX_WRXB one1 R zero1 B; Pmovl_rm (AddrE0 rsbits) rdbits])
    else
      do rex_rr <- encode_rex_prefix_rr rd r1;
      let (oREX_rdbits, r1bits) := rex_rr in
      let (orex, rdbits) := oREX_rdbits in
      OK (orex ++ [Pmovl_rm (AddrE0 r1bits) rdbits])
  | Asm.Pmovl_rm rd addr =>
    do rex_ra <- encode_rex_prefix_ra rd addr;
    let (oREX_rdbits, a) := rex_ra in
    let (orex, rdbits) := oREX_rdbits in
    OK (orex ++ [Pmovl_rm a rdbits])
  | Asm.Pmovl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Pmovl_ri rdbits imm32])
  | Asm.Pmovl_mr addr r =>
    do rex_ra <- encode_rex_prefix_ra r addr;
    let (oREX_rbits, a) := rex_ra in
    let (orex, rbits) := oREX_rbits in
    OK (orex ++ [Pmovl_mr a rbits])
  | Asm.Pmovsd_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, rsbits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pmovss_d_fm (AddrE0 rsbits) rdbits])
  | Asm.Pmovsd_fm rd addr =>
    do rex_ra <- encode_rex_prefix_fa rd addr;
    let (oREX_rdbits, a) := rex_ra in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pmovss_d_fm a rdbits])
  | Asm.Pmovsd_mf addr rs =>
    do rex_ra <- encode_rex_prefix_fa rs addr;
    let (oREX_rsbits, a) := rex_ra in
    let (orex, rsbits) := oREX_rsbits in
    OK ([REPNZ] ++ orex ++ [Pmovss_d_mf a rsbits])
  | Asm.Pmovss_fm rd addr =>
    do rex_ra <- encode_rex_prefix_fa rd addr;
    let (oREX_rdbits, a) := rex_ra in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Pmovss_d_fm a rdbits])
  | Asm.Pmovss_mf addr rs =>
    do rex_ra <- encode_rex_prefix_fa rs addr;
    let (oREX_rsbits, a) := rex_ra in
    let (orex, rsbits) := oREX_rsbits in
    OK ([REP] ++ orex ++ [Pmovss_d_mf a rsbits])
  | Asm.Pfldl_m addr =>
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    OK (orex ++ [Pfldl_m a])
  | Asm.Pfstpl_m addr =>
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    OK (orex ++ [Pfstpl_m a])
  | Asm.Pflds_m addr =>
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    OK (orex ++ [Pflds_m a])
  | Asm.Pfstps_m addr =>
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    OK (orex ++ [Pfstps_m a])
  | Asm.Pmovb_mr addr rs =>
    if Archi.ptr64 then
      do Rrsbits <- encode_ireg_u4 rs;
      let (R, rsbits):= Rrsbits in
      do addr_X_B <- translate_Addrmode_AddrE64 addr;
      let (a_X, B) := addr_X_B in
      let (a,X) := a_X in
      (* 64bit mode rex prefix for byte register encoding *)
      OK ([REX_WRXB zero1 R X B;Pmovb_mr a rsbits])
    else
      do rex_ra <- encode_rex_prefix_ra rs addr;
      let (orex_rbits, a) := rex_ra in
      let (orex, rbits) := orex_rbits in
      OK (orex ++ [Pmovb_mr a rbits])
  | Asm.Pmovw_mr addr r =>
    do rex_ra <- encode_rex_prefix_ra r addr;
    let (orex_rbits, a) := rex_ra in
    let (orex, rbits) := orex_rbits in
    OK ([Override] ++ orex ++ [Pmovl_mr a rbits])
  | Asm.Pmovzb_rr rd r1 =>
    if Archi.ptr64 then
      do Rrdbits <- encode_ireg_u4 rd;
      do Brsbits <- encode_ireg_u4 r1;
      let (B, r1bits) := Brsbits in
      let (R, rdbits) := Rrdbits in
      OK ([REX_WRXB zero1 R zero1 B; Pmovzb_rm (AddrE0 r1bits) rdbits])
    else
      do rex_rr <- encode_rex_prefix_rr rd r1;
      let (orex_rdbits, r1bits) := rex_rr in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pmovzb_rm (AddrE0 r1bits) rdbits])
  | Asm.Pmovzb_rm rd addr =>
    (* 1byte memory to 32bit register *)
    (* if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       let (R, rdbits):= Rrdbits in *)
(*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *)
(*       let (a_X, B) := addr_X_B in *)
(*       let (a,X) := a_X in *)
(*       OK ([REX_WRXB zero1 R X B; Pmovzb_rm a rdbits]) *)
(*     else *)
      do rex_ra <- encode_rex_prefix_ra rd addr;
      let (orex_rdbits, a) := rex_ra in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pmovzb_rm a rdbits])
  | Asm.Pmovzw_rm rd addr =>
    do rex_ra <- encode_rex_prefix_ra rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pmovzw_GvEv a rdbits])
  | Asm.Pmovzw_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
     OK (orex ++ [Pmovzw_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pmovsb_rm rd addr =>
    (* if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       let (R, rdbits):= Rrdbits in *)
(*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *)
(*       let (a_X, B) := addr_X_B in *)
(*       let (a,X) := a_X in *)
(*       OK ([REX_WRXB zero1 R X B; Pmovsb_GvEv a rdbits]) *)
(*     else *)
      do rex_ra <- encode_rex_prefix_ra rd addr;
      let (orex_rdbits, a) := rex_ra in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pmovsb_GvEv a rdbits])
  | Asm.Pmovsb_rr rd rs =>
    if Archi.ptr64 then
      do Rrdbits <- encode_ireg_u4 rd;
      do Brsbits <- encode_ireg_u4 rs;
      let (B, r1bits) := Brsbits in
      let (R, rdbits) := Rrdbits in
      OK ([REX_WRXB zero1 R zero1 B; Pmovsb_GvEv (AddrE0 r1bits) rdbits])
    else
      do rex_rr <- encode_rex_prefix_rr rd rs;
      let (orex_rdbits, r1bits) := rex_rr in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pmovsb_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pmovw_rm rd addr =>
    do rex_ra <- encode_rex_prefix_ra rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK ([Override] ++ orex ++ [Pmovl_rm a rdbits])
  | Asm.Pmovb_rm rd addr =>
    if Archi.ptr64 then
      do Rrdbits <- encode_ireg_u4 rd;
      let (R, rdbits):= Rrdbits in
      do addr_X_B <- translate_Addrmode_AddrE64 addr;
      let (a_X, B) := addr_X_B in
      let (a,X) := a_X in
      OK ([REX_WRXB zero1 R X B; Pmovb_rm a rdbits])
    else
      do rex_ra <- encode_rex_prefix_ra rd addr;
      let (orex_rdbits, a) := rex_ra in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pmovb_rm a rdbits])
  | Asm.Pmovsw_rm rd addr =>
    do rex_ra <- encode_rex_prefix_ra rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pmovsw_GvEv a rdbits])
  | Asm.Pmovsw_rr rd rs =>
    do rex_rr <- encode_rex_prefix_rr rd rs;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pmovsw_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pnegl rd =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    OK (orex ++ [Pnegl rdbits])
  | Asm.Pleal rd addr =>
    do rex_ra <- encode_rex_prefix_ra rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pleal a rdbits])

  | Asm.Pcvttss2si_rf rd r1 =>
    do rex_rr <- encode_rex_prefix_rf rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Pcvttss_d_2si_rf rdbits r1bits])
  | Asm.Pcvttss2sl_rf rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_freg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REP; REX_WRXB one1 R zero1 B; Pcvttss_d_2si_rf rdbits rsbits])
  | Asm.Pcvtsi2sd_fr rd r1 =>
    do rex_rr <- encode_rex_prefix_fr rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pcvtsi2ss_d_fr rdbits r1bits])
  | Asm.Pcvtsl2sd_fr rd rs =>
    (* rd require u3, but u4 here *)
    do Rrdbits <- encode_freg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REPNZ; REX_WRXB one1 R zero1 B; Pcvtsi2ss_d_fr rdbits rsbits])
  | Asm.Pcvtsi2ss_fr rd r1 =>
    do rex_rr <- encode_rex_prefix_fr rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Pcvtsi2ss_d_fr rdbits r1bits])
  | Asm.Pcvtsl2ss_fr rd rs =>
    (* rd require u3, but u4 here *)
    do Rrdbits <- encode_freg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REP; REX_WRXB one1 R zero1 B; Pcvtsi2ss_d_fr rdbits rsbits])
  | Asm.Pcvttsd2si_rf rd r1 =>
    do rex_rr <- encode_rex_prefix_rf rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pcvttss_d_2si_rf rdbits r1bits])
  | Asm.Pcvttsd2sl_rf rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_freg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REPNZ; REX_WRXB one1 R zero1 B; Pcvttss_d_2si_rf rdbits rsbits])
  | Asm.Pcvtss2sd_ff rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
     OK ([REP] ++ orex ++ [Pcvtsd2ss_d_ff rdbits r1bits])
  | Asm.Pcvtsd2ss_ff rd r1=>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pcvtsd2ss_d_ff rdbits r1bits])
  | Asm.Paddl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Paddl_ri rdbits imm32])
  | Asm.Psubl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Psubl_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pimull_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pimull_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pimull_r r =>
    do rex_r <- encode_rex_prefix_r r;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pimull_r rbits])
  | Asm.Pimull_ri rd imm =>
    do rex_rr <- encode_rex_prefix_rr rd rd;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Pimull_ri rdbits r1bits imm32])
  | Asm.Pmull_r r =>
    do rex_r <- encode_rex_prefix_r r;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pmull_r rbits])
  | Asm.Pcltd => OK [Pcltd]
  | Asm.Pcqto => OK [REX_WRXB one1 zero1 zero1 zero1; Pcltd]
  | Asm.Pdivl r1 =>
    do rex_r <- encode_rex_prefix_r r1;
    let (orex, rbits) := rex_r in
     OK (orex ++ [Pdivl_r rbits])
  | Asm.Pidivl r1 =>
    do rex_r <- encode_rex_prefix_r r1;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pidivl_r rbits])
  | Asm.Pandl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr r1 rd;
    let (orex_r1bits, rdbits) := rex_rr in
    let (orex, r1bits) := orex_r1bits in
    OK (orex ++ [Pandl_EvGv (AddrE0 rdbits) r1bits])
  | Asm.Pandl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Pandl_ri rdbits imm32])
  | Asm.Porl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (orex ++ [Porl_ri rdbits imm32])
  | Asm.Porl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr r1 rd;
    let (orex_r1bits, rdbits) := rex_rr in
    let (orex, r1bits) := orex_r1bits in
    OK (orex ++ [Porl_EvGv (AddrE0 rdbits) r1bits])
  | Asm.Pxorl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr r1 rd;
    let (orex_r1bits, rdbits) := rex_rr in
    let (orex, r1bits) := orex_r1bits in
    OK (orex ++ [Pxorl_EvGv (AddrE0 rdbits) r1bits])
  | Asm.Pxorl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Pxorl_ri rdbits imm32])
  | Asm.Pnotl rd =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    OK (orex ++ [Pnotl rdbits])
  | Asm.Psall_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    OK (orex ++ [Psall_ri rdbits imm8])
  | Asm.Psall_rcl rd =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    OK (orex ++ [Psall_rcl rdbits])
  | Asm.Pshrl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    OK (orex ++ [Pshrl_ri rdbits imm8])
  | Asm.Psarl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    OK (orex ++ [Psarl_ri rdbits imm8])
  | Asm.Psarl_rcl rd =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    OK (orex ++ [Psarl_rcl rdbits])
  | Asm.Pshld_ri rd r1 imm =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    (* rd is rm, rd is reg_op *)
     OK (orex ++ [Pshld_ri r1bits rdbits imm8])
  | Asm.Prolw_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    OK ([Override] ++ orex ++ [Prolw_ri rdbits imm8])
  | Asm.Prorl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    OK (orex ++ [Prorl_ri rdbits imm8])
  | Asm.Pcmpl_rr r1 r2 =>
    (* swap rd and r1 for some bug found in qsort.c *)
    do rex_rr <- encode_rex_prefix_rr r2 r1;
    let (orex_r2bits, r1bits) := rex_rr in
    let (orex, r2bits) := orex_r2bits in
    (* bug here: fixed *)
    OK (orex ++ [Pcmpl_EvGv (AddrE0 r1bits) r2bits])
  | Asm.Pcmpl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Pcmpl_ri rdbits imm32])
  | Asm.Ptestl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Ptestl_ri rdbits imm32])
  | Asm.Ptestl_rr r1 r2 =>
    do rex_rr <- encode_rex_prefix_rr r2 r1;
    let (orex_r2bits, r1bits) := rex_rr in
    let (orex, r2bits) := orex_r2bits in
    OK (orex ++ [Ptestl_EvGv (AddrE0 r1bits) r2bits])
  | Asm.Pcmov c rd r1 =>
    let cond := encode_testcond_u4 c in
    if Archi.ptr64 then
      do Rrdbits <- encode_ireg_u4 rd;
      do Brsbits <- encode_ireg_u4 r1;
      let (B, rsbits) := Brsbits in
      let (R, rdbits) := Rrdbits in
      OK [REX_WRXB one1 R zero1 B; Pcmov cond rdbits rsbits]
    else
      do rex_rr <- encode_rex_prefix_rr rd r1;
      let (orex_rdbits, r1bits) := rex_rr in
      let (orex, rdbits) := orex_rdbits in
      OK (orex ++ [Pcmov cond rdbits r1bits])
  | Asm.Psetcc c rd =>
    if Archi.ptr64 then
      do Brdbits <- encode_ireg_u4 rd;
      let (B, rdbits) := Brdbits in
      let cond := encode_testcond_u4 c in
      OK ([REX_WRXB zero1 zero1 zero1 B; Psetcc cond rdbits])
    else
      do rex_r <- encode_rex_prefix_r rd;
      let (orex, rdbits) := rex_r in
      let cond := encode_testcond_u4 c in
      OK (orex ++ [Psetcc cond rdbits])
  | Asm.Paddd_ff rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Padds_d_ff rdbits r1bits])
  | Asm.Padds_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Padds_d_ff rdbits r1bits])
  | Asm.Psubd_ff rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Psubs_d_ff rdbits r1bits])
  | Asm.Psubs_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Psubs_d_ff rdbits r1bits])

  | Asm.Pmuld_ff rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pmuls_d_ff rdbits r1bits])
  | Asm.Pmuls_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Pmuls_d_ff rdbits r1bits])

  | Asm.Pcomisd_ff r1 r2 =>
    do rex_rr <- encode_rex_prefix_ff r1 r2;
    let (oREX_r1bits, r2bits) := rex_rr in
    let (orex, r1bits) := oREX_r1bits in
    OK ([Override] ++ orex ++ [Pcomiss_d_ff r1bits r2bits])
  | Asm.Pcomiss_ff r1 r2 =>
    do rex_rr <- encode_rex_prefix_ff r1 r2;
    let (oREX_r1bits, r2bits) := rex_rr in
    let (orex, r1bits) := oREX_r1bits in
    (* test in r1_r2/comoss.s: r1 -> reg, r2 -> rm*)
    OK (orex ++ [Pcomiss_d_ff r1bits r2bits])

  | Asm.Pxorps_f r =>
    do rex_rr <- encode_rex_prefix_ff r r;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK (orex ++ [Pxorps_d_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pxorps_fm frd addr =>
    do rex_ra <- encode_rex_prefix_fa frd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pxorps_d_GvEv a rdbits])
  | Asm.Pxorpd_f r =>
    do rex_rr <- encode_rex_prefix_ff r r;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([Override] ++ orex ++ [Pxorps_d_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pxorpd_fm frd addr =>
    do rex_ra <- encode_rex_prefix_fa frd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK ([Override] ++ orex ++ [Pxorps_d_GvEv a rdbits])
  | Asm.Pandps_fm frd addr =>
    do rex_ra <- encode_rex_prefix_fa frd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pandps_d_fm a rdbits])
  | Asm.Pandpd_fm frd addr =>
    do rex_ra <- encode_rex_prefix_fa frd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK ([Override] ++ orex ++ [Pandps_d_fm a rdbits])

  | Asm.Pjmp_l_rel ofs =>
    (* no relocation *)
    do iofs <- res_iofs;
    match ZTree.get (iofs+instr_ofs) rtbl_ofs_map with
    | None =>
      if (0 <=? ofs) && (ofs <? Int.modulus) then
        do imm <- encode_ofs_u32 ofs;
        OK [Pjmp_l_rel imm]
      else
        Error (msg "overflow of offset in Pjmp_l_rel")
    | _ => Error[MSG"Relocation entry in Pjmp_l_rel not expected"; MSG(Z_to_hex_string 4 ofs)]
    end
  | Asm.Pjmp_s id _ =>
    if Pos.eqb id xH then
      do iofs <- res_iofs;
      do addend <- get_instr_reloc_addend' (iofs + instr_ofs);
      do imm32 <- encode_ofs_u32 addend;
      OK [Pjmp_l_rel imm32]
    else Error (msg "Id not equal to xH in Pjmp_s")
  | Asm.Pjmp_r r sg =>
    do rex_r <- encode_rex_prefix_r r;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pjmp_Ev (AddrE0 rbits)])
  | Asm.Pjmp_m addr =>
    (* same in the 64bit and 32bit mode *)
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    OK (orex ++ [Pjmp_Ev a])
  | Asm.Pnop | Asm.Plabel _ | Asm.Pmovls_rr _ =>
     OK [Pnop]
  | Asm.Pcall_r r sg =>
    do rex_r <- encode_rex_prefix_r r;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pcall_r rbits])
  | Asm.Pcall_s id sg =>
    match id with
    | xH =>
      do iofs <- res_iofs;
      do addend <- get_instr_reloc_addend' (iofs + instr_ofs);
      do imm32 <- encode_ofs_u32 addend;
      OK [Pcall_ofs imm32]
    | _ =>
      Error [MSG "id must be 1: Pcall_s"]
    end
  | Asm.Pret => OK [Pret]
  | Asm.Pret_iw imm => (*define encode_ofs_u16*)
     do imm16 <- encode_ofs_u16 (Int.intval imm);
     OK [Pret_iw imm16]
  | Asm.Pjcc_rel c ofs =>
    let cond := encode_testcond_u4 c in
    if (0 <=? ofs) && (ofs <? Int.modulus) then
      do imm <- encode_ofs_u32 ofs;
      OK [Pjcc_rel cond imm]
    else Error (msg "offset overflow in Pjcc_rel")
  | Asm.Padcl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (orex ++ [Padcl_ri rdbits imm8])
  | Asm.Padcl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr r1 rd;
    let (orex_r1bits, rdbits) := rex_rr in
    let (orex, r1bits) := orex_r1bits in
    (* check document, add reg with CF to rm *)
    OK (orex ++ [Padcl_rr r1bits rdbits])
  | Asm.Paddl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr r1 rd;
    let (orex_r1bits, rdbits) := rex_rr in
    let (orex, r1bits) := orex_r1bits in
    OK (orex ++ [Paddl_EvGv (AddrE0 rdbits) r1bits])
  | Asm.Paddl_mi addr imm =>
    do orex_a <- encode_rex_prefix_addr addr;
    let (orex, a) := orex_a in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Paddl_mi a imm32])
  | Asm.Pbsfl rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pbsfl rdbits r1bits])
  | Asm.Pbsrl rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pbsrl rdbits r1bits])
  | Asm.Pbswap32 rd =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R,rdbits) := Rrdbits in
    (* use R to extend register instead of B *)
    OK ([REX_WRXB zero1 R zero1 zero1; Pbswap32 rdbits])
    (* do rex_r <- encode_rex_prefix_r rd; *)
    (* let (orex, rdbits) := rex_r in *)
    (* OK (orex ++ [Pbswap32 rdbits]) *)
  | Asm.Pbswap64 rd =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R,rdbits) := Rrdbits in
    OK ([REX_WRXB one1 R zero1 zero1; Pbswap32 rdbits])
  | Asm.Pmaxsd rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pmaxsd rdbits r1bits])
  | Asm.Pminsd rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pminsd rdbits r1bits])

  | Asm.Pmovsq_mr addr rs =>
    do rex_ra <- encode_rex_prefix_fa rs addr;
    let (orex_rbits, a) := rex_ra in
    let (orex, rbits) := orex_rbits in
    OK ([Override] ++ orex ++ [Pmovsq_mr a rbits])
  | Asm.Pmovsq_rm rd addr =>
    do rex_ra <- encode_rex_prefix_fa rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK ([REP] ++ orex ++ [Pmovsq_rm a rdbits])
  | Asm.Prep_movsl => OK ([REP; Prep_movsl])
  | Asm.Psbbl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Psbbl_rr r1bits rdbits])

  | Asm.Psqrtsd rd r1 =>
    do rex_rr <- encode_rex_prefix_ff rd r1;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pbsqrtsd rdbits r1bits])
  | Asm.Psubl_ri rd imm =>
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (orex ++ [Psubl_ri rdbits imm32])
  | Asm.Pmov_mr_a addr rs =>
    if Archi.ptr64 then
      do addr_X_B <- translate_Addrmode_AddrE64 addr;
      let (a_X, B) := addr_X_B in
      let (a,X) := a_X in
      do Rrsbits <- encode_ireg_u4 rs;
      let (R,rsbits) := Rrsbits in
      OK ([REX_WRXB one1 R X B; Pmovl_mr a rsbits])
    else
      do a <- translate_Addrmode_AddrE addr;
      do rbits <- encode_ireg_u3 rs;
    OK [Pmovl_mr a rbits]
  | Asm.Pmov_rm_a rd addr =>
    if Archi.ptr64 then
      do addr_X_B <- translate_Addrmode_AddrE64 addr;
      let (a_X, B) := addr_X_B in
      let (a,X) := a_X in
      do Rrdbits <- encode_ireg_u4 rd;
      let (R,rdbits) := Rrdbits in
      OK ([REX_WRXB one1 R X B; Pmovl_rm a rdbits])
    else
      do a <- translate_Addrmode_AddrE addr;
      do rbits <- encode_ireg_u3 rd;
      OK ([Pmovl_rm a rbits])

  | Asm.Pmovsd_mf_a addr rs =>
    do rex_ra <- encode_rex_prefix_fa rs addr;
    let (orex_rbits, a) := rex_ra in
    let (orex, rbits) := orex_rbits in
    OK ([REPNZ] ++ orex ++ [Pmovss_d_mf a rbits])
  | Asm.Pmovsd_fm_a rd addr =>
    do rex_ra <- encode_rex_prefix_fa rd addr;
    let (orex_rdbits, a) := rex_ra in
    let (orex, rdbits) := orex_rdbits in
    OK ([REP] ++ orex ++ [Pmovss_d_fm a rdbits])
  | Asm.Pxorl_r r =>
    do rex_rr <- encode_rex_prefix_rr r r;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK (orex ++ [Pxorl_EvGv (AddrE0 rdbits) r1bits])

  | Asm.Pdivd_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REPNZ] ++ orex ++ [Pdivss_d_ff rdbits r1bits])
  | Asm.Pdivs_ff rd rs =>
    do rex_rr <- encode_rex_prefix_ff rd rs;
    let (oREX_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := oREX_rdbits in
    OK ([REP] ++ orex ++ [Pdivss_d_ff rdbits r1bits])

  | Asm.Pshrl_rcl r =>
    do rex_r <- encode_rex_prefix_r r;
    let (orex, rbits) := rex_r in
    OK (orex ++ [Pshrl_rcl rbits])
  | Asm.Pmovzl_rr rd r1 =>
    do rex_rr <- encode_rex_prefix_rr rd r1;
    let (orex_rdbits, r1bits) := rex_rr in
    let (orex, rdbits) := orex_rdbits in
    OK (orex ++ [Pmovl_rm (AddrE0 r1bits) rdbits])

  (* 64bit *)
  (* transfer to mov  memory *)
(*     | Asm.Pmovq_ri rd imm => *)
(*     do Rrdbits <- encode_ireg_u4 rd; *)
(*     let (R,rdbits) := Rrdbits in *)
(*     do imm64 <- encode_ofs_u64 (Int64.intval imm); *)
(*     OK (Pmovq_ri R rdbits imm64) *)
  | Asm.Pmovsl_rr rd r1 =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 r1;
    let (B, r1bits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REX_WRXB one1 R zero1 B; Pmovsxd_GvEv (AddrE0 r1bits) rdbits])
  | Asm.Pmovq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    (* cannot use '(addr,X,B) because X also a product type *)
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    (* alphabetical: B R X *)
    OK ([REX_WRXB one1 R X B; Pmovl_rm a rdbits])
  | Asm.Pmovq_mr addr rs =>
    do Rrsbits <- encode_ireg_u4 rs;
    let (R, rsbits):= Rrsbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pmovl_mr a rsbits])
  | Asm.Pleaq rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pleal a rdbits])
  | Asm.Pnegq r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits):= Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pnegl rbits])
  | Asm.Paddq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Paddl_GvEv a rdbits])
  | Asm.Psubq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Psubl_GvEv a rdbits])
  | Asm.Psubq_rr rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Psubl_GvEv (AddrE0 rsbits) rdbits])
  | Asm.Pimulq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pimull_GvEv a rdbits])
  | Asm.Pimulq_r r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pimull_r rbits])
  | Asm.Pimulq_rr rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Pimull_GvEv (AddrE0 rsbits) rdbits])
  | Asm.Pmulq_r r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pmull_r rbits])
  | Asm.Pidivq r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pidivl_r rbits])
  | Asm.Pdivq r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pdivl_r rbits])
  | Asm.Pandq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pandl_GvEv a rdbits])
  | Asm.Pandq_rr rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Pandl_GvEv (AddrE0 rsbits) rdbits])
  | Asm.Porq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Porl_GvEv a rdbits])
  | Asm.Porq_rr rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Porl_GvEv (AddrE0 rsbits) rdbits])
  | Asm.Pxorq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pxorl_GvEv a rdbits])
  | Asm.Pxorq_rr rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Pxorl_GvEv (AddrE0 rsbits) rdbits])
  | Asm.Pxorq_r r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 B zero1 B; Pxorl_GvEv (AddrE0 rbits) rbits])
  | Asm.Pnotq r =>
  (* test in asm *)
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pnotl rbits])
  | Asm.Psalq_ri r imm =>
  (* find some confusion in Asm.v semantic, must check whether imm is 8 bit *)
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Psall_ri rbits imm8])
  | Asm.Psalq_rcl r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Psall_rcl rbits])
  | Asm.Psarq_ri r imm =>
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Psarl_ri rbits imm8])
  | Asm.Psarq_rcl r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Psarl_rcl rbits])
  | Asm.Pshrq_ri r imm =>
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pshrl_ri rbits imm8])
  | Asm.Pshrq_rcl r =>
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pshrl_rcl rbits])
  | Asm.Prorq_ri r imm =>
    do imm8 <- encode_ofs_u8 (Int.intval imm);
    do Brbits <- encode_ireg_u4 r;
    let (B, rbits) := Brbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Prorl_ri rbits imm8])
  | Asm.Pcmpq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Pcmpl_GvEv a rdbits])
  | Asm.Pcmpq_rr r1 r2 =>
    do Br1bits <- encode_ireg_u4 r1;
    do Rr2bits <- encode_ireg_u4 r2;
    let (B, r1bits) := Br1bits in
    let (R, r2bits) := Rr2bits in
    (* B for rs, R for rd *)
    OK ([REX_WRXB one1 R zero1 B; Pcmpl_EvGv (AddrE0 r1bits) r2bits])
  | Asm.Ptestq_rm rd addr =>
    do Rrdbits <- encode_ireg_u4 rd;
    let (R, rdbits):= Rrdbits in
    do addr_X_B <- translate_Addrmode_AddrE64 addr;
    let (a_X, B) := addr_X_B in
    let (a,X) := a_X in
    OK ([REX_WRXB one1 R X B; Ptestl_EvGv a rdbits])
  | Asm.Ptestq_rr r1 r2 =>
    do Rr2bits <- encode_ireg_u4 r2;
    do Br1bits <- encode_ireg_u4 r1;
    let (B, r1bits) := Br1bits in
    let (R, r2bits) := Rr2bits in
    (* test in r1_r2/testq.s: r2 -> reg_op -> R, r1 -> rm -> B *)
    OK ([REX_WRXB one1 R zero1 B; Ptestl_EvGv (AddrE0 r1bits) r2bits])
  (* add Pbsrq Pbsfq for builtin pass*)
  | Asm.Pbsfq rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REX_WRXB one1 R zero1 B; Pbsfl rdbits rsbits])
  | Asm.Pbsrq rd rs =>
    do Rrdbits <- encode_ireg_u4 rd;
    do Brsbits <- encode_ireg_u4 rs;
    let (B, rsbits) := Brsbits in
    let (R, rdbits) := Rrdbits in
    OK ([REX_WRXB one1 R zero1 B; Pbsrl rdbits rsbits])
  | _ => Error [MSG "Not exists or unsupported: "; MSG (instr_to_string i)]
  end.

(* (** return (option rex prefix, instruction *) *)
(* (** REX_WRXB: B R W X  *) *)
(* Definition translate_instr (instr_ofs: Z) (i:instruction) : res (list Instruction) := *)
(*   let res_iofs := instr_reloc_offset i in *)
(*   let translate_Addrmode_AddrE := translate_Addrmode_AddrE instr_ofs res_iofs in *)
(*   let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 instr_ofs res_iofs in *)
(*   let encode_rex_prefix_ra := encode_rex_prefix_ra instr_ofs res_iofs in *)
(*   let encode_rex_prefix_fa := encode_rex_prefix_fa instr_ofs res_iofs in *)
(*   let encode_rex_prefix_addr := encode_rex_prefix_addr instr_ofs res_iofs in *)
(*   match i with *)
(*   | Pmov_rr rd r1 => *)
(*     if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       do Brsbits <- encode_ireg_u4 r1; *)
(*       let (B, rsbits) := Brsbits in *)
(*       let (R, rdbits) := Rrdbits in *)
(*       OK ([REX_WRXB one1 R zero1 B; Pmovl_rm (AddrE0 rsbits) rdbits]) *)
(*     else *)
(*       do rex_rr <- encode_rex_prefix_rr rd r1; *)
(*       let (oREX_rdbits, r1bits) := rex_rr in *)
(*       let (orex, rdbits) := oREX_rdbits in *)
(*       OK (orex ++ [Pmovl_rm (AddrE0 r1bits) rdbits]) *)
(*   | Asm.Pmovl_rm rd addr => *)
(*     do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*     let (oREX_rdbits, a) := rex_ra in *)
(*     let (orex, rdbits) := oREX_rdbits in *)
(*     OK (orex ++ [Pmovl_rm a rdbits]) *)
(*   | Asm.Pmovl_ri rd imm => *)
(*     do rex_r <- encode_rex_prefix_r rd; *)
(*     let (orex, rdbits) := rex_r in *)
(*     do imm32 <- encode_ofs_u32 (Int.intval imm); *)
(*     OK (orex ++ [Pmovl_ri rdbits imm32]) *)
(*   | Asm.Pmovl_mr addr r => *)
(*     do rex_ra <- encode_rex_prefix_ra r addr; *)
(*     let (oREX_rbits, a) := rex_ra in *)
(*     let (orex, rbits) := oREX_rbits in *)
(*     OK (orex ++ [Pmovl_mr a rbits]) *)
(*   | Asm.Pmovsd_ff rd rs => *)
(*     do rex_rr <- encode_rex_prefix_ff rd rs; *)
(*     let (oREX_rdbits, rsbits) := rex_rr in *)
(*     let (orex, rdbits) := oREX_rdbits in *)
(*     OK ([REPNZ] ++ orex ++ [Pmovss_d_fm (AddrE0 rsbits) rdbits]) *)
(*   | Asm.Pmovsd_fm rd addr => *)
(*     do rex_ra <- encode_rex_prefix_fa rd addr; *)
(*     let (oREX_rdbits, a) := rex_ra in *)
(*     let (orex, rdbits) := oREX_rdbits in *)
(*     OK ([REPNZ] ++ orex ++ [Pmovss_d_fm a rdbits]) *)
(*   | Asm.Pmovsd_mf addr rs => *)
(*     do rex_ra <- encode_rex_prefix_fa rs addr; *)
(*     let (oREX_rsbits, a) := rex_ra in *)
(*     let (orex, rsbits) := oREX_rsbits in *)
(*     OK ([REPNZ] ++ orex ++ [Pmovss_d_mf a rsbits]) *)
(*   | Asm.Pmovss_fm rd addr => *)
(*     do rex_ra <- encode_rex_prefix_fa rd addr; *)
(*     let (oREX_rdbits, a) := rex_ra in *)
(*     let (orex, rdbits) := oREX_rdbits in *)
(*     OK ([REP] ++ orex ++ [Pmovss_d_fm a rdbits]) *)
(*   | Asm.Pmovss_mf addr rs => *)
(*     do rex_ra <- encode_rex_prefix_fa rs addr; *)
(*     let (oREX_rsbits, a) := rex_ra in *)
(*     let (orex, rsbits) := oREX_rsbits in *)
(*     OK ([REP] ++ orex ++ [Pmovss_d_mf a rsbits]) *)
(*   | Asm.Pmovw_rm rd addr => *)
(*     do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*     let (orex_rdbits, a) := rex_ra in *)
(*     let (orex, rdbits) := orex_rdbits in *)
(*     OK ([Override] ++ orex ++ [Pmovl_rm a rdbits]) *)
(*   | Asm.Pfldl_m addr => *)
(*     do orex_a <- encode_rex_prefix_addr addr; *)
(*     let (orex, a) := orex_a in *)
(*     OK (orex ++ [Pfldl_m a]) *)
(*   | Asm.Pfstpl_m addr => *)
(*     do orex_a <- encode_rex_prefix_addr addr; *)
(*     let (orex, a) := orex_a in *)
(*     OK (orex ++ [Pfstpl_m a]) *)
(*   | Asm.Pflds_m addr => *)
(*     do orex_a <- encode_rex_prefix_addr addr; *)
(*     let (orex, a) := orex_a in *)
(*     OK (orex ++ [Pflds_m a]) *)
(*   | Asm.Pfstps_m addr => *)
(*     do orex_a <- encode_rex_prefix_addr addr; *)
(*     let (orex, a) := orex_a in *)
(*     OK (orex ++ [Pfstps_m a]) *)
(*   | Asm.Pmovb_mr addr rs => *)
(*     if Archi.ptr64 then *)
(*       do Rrsbits <- encode_ireg_u4 rs; *)
(*       let (R, rsbits):= Rrsbits in *)
(*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *)
(*       let (a_X, B) := addr_X_B in *)
(*       let (a,X) := a_X in *)
(*       (* 64bit mode rex prefix for byte register encoding *) *)
(*       OK ([REX_WRXB zero1 R X B;Pmovb_mr a rsbits]) *)
(*     else *)
(*       do rex_ra <- encode_rex_prefix_ra rs addr; *)
(*       let (orex_rbits, a) := rex_ra in *)
(*       let (orex, rbits) := orex_rbits in *)
(*       OK (orex ++ [Pmovb_mr a rbits]) *)
(*   | Asm.Pmovw_mr addr r => *)
(*     do rex_ra <- encode_rex_prefix_ra r addr; *)
(*     let (orex_rbits, a) := rex_ra in *)
(*     let (orex, rbits) := orex_rbits in *)
(*     OK ([Override] ++ orex ++ [Pmovl_mr a rbits]) *)
(*   | Asm.Pmovzb_rr rd r1 => *)
(*     if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       do Brsbits <- encode_ireg_u4 r1; *)
(*       let (B, r1bits) := Brsbits in *)
(*       let (R, rdbits) := Rrdbits in *)
(*       OK ([REX_WRXB zero1 R zero1 B; Pmovzb_rm (AddrE0 r1bits) rdbits]) *)
(*     else *)
(*       do rex_rr <- encode_rex_prefix_rr rd r1; *)
(*       let (orex_rdbits, r1bits) := rex_rr in *)
(*       let (orex, rdbits) := orex_rdbits in *)
(*       OK (orex ++ [Pmovzb_rm (AddrE0 r1bits) rdbits]) *)
(*   | Asm.Pmovzb_rm rd addr => *)
(*     (* 1byte memory to 32bit register *) *)
(*     (* if Archi.ptr64 then *) *)
(* (*       do Rrdbits <- encode_ireg_u4 rd; *) *)
(* (*       let (R, rdbits):= Rrdbits in *) *)
(* (*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *) *)
(* (*       let (a_X, B) := addr_X_B in *) *)
(* (*       let (a,X) := a_X in *) *)
(* (*       OK ([REX_WRXB zero1 R X B; Pmovzb_rm a rdbits]) *) *)
(* (*     else *) *)
(*       do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*       let (orex_rdbits, a) := rex_ra in *)
(*       let (orex, rdbits) := orex_rdbits in *)
(*       OK (orex ++ [Pmovzb_rm a rdbits]) *)
(*   | Asm.Pmovzw_rm rd addr => *)
(*     do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*     let (orex_rdbits, a) := rex_ra in *)
(*     let (orex, rdbits) := orex_rdbits in *)
(*     OK (orex ++ [Pmovzw_GvEv a rdbits]) *)
(*   | Asm.Pmovzw_rr rd r1 => *)
(*     do rex_rr <- encode_rex_prefix_rr rd r1; *)
(*     let (orex_rdbits, r1bits) := rex_rr in *)
(*     let (orex, rdbits) := orex_rdbits in *)
(*      OK (orex ++ [Pmovzw_GvEv (AddrE0 r1bits) rdbits]) *)
(*   | Asm.Pmovsb_rm rd addr => *)
(*     (* if Archi.ptr64 then *) *)
(* (*       do Rrdbits <- encode_ireg_u4 rd; *) *)
(* (*       let (R, rdbits):= Rrdbits in *) *)
(* (*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *) *)
(* (*       let (a_X, B) := addr_X_B in *) *)
(* (*       let (a,X) := a_X in *) *)
(* (*       OK ([REX_WRXB zero1 R X B; Pmovsb_GvEv a rdbits]) *) *)
(* (*     else *) *)
(*       do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*       let (orex_rdbits, a) := rex_ra in *)
(*       let (orex, rdbits) := orex_rdbits in *)
(*       OK (orex ++ [Pmovsb_GvEv a rdbits]) *)
(*   | Asm.Pmovsb_rr rd rs => *)
(*     if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       do Brsbits <- encode_ireg_u4 rs; *)
(*       let (B, r1bits) := Brsbits in *)
(*       let (R, rdbits) := Rrdbits in *)
(*       OK ([REX_WRXB zero1 R zero1 B; Pmovsb_GvEv (AddrE0 r1bits) rdbits]) *)
(*     else *)
(*       do rex_rr <- encode_rex_prefix_rr rd rs; *)
(*       let (orex_rdbits, r1bits) := rex_rr in *)
(*       let (orex, rdbits) := orex_rdbits in *)
(*       OK (orex ++ [Pmovsb_GvEv (AddrE0 r1bits) rdbits]) *)
(*   | Asm.Pmovb_rm rd addr => *)
(*     if Archi.ptr64 then *)
(*       do Rrdbits <- encode_ireg_u4 rd; *)
(*       let (R, rdbits):= Rrdbits in *)
(*       do addr_X_B <- translate_Addrmode_AddrE64 addr; *)
(*       let (a_X, B) := addr_X_B in *)
(*       let (a,X) := a_X in *)
(*       OK ([REX_WRXB zero1 R X B; Pmovb_rm a rdbits]) *)
(*     else *)
(*       do rex_ra <- encode_rex_prefix_ra rd addr; *)
(*       let (orex_rdbits, a) := rex_ra in *)
(*       let (orex, rdbits) := orex_rdbits in *)
(*       OK (orex ++ [Pmovb_rm a rdbits]) *)

(*   | _ => Error (msg "unsupported") *)
(*   end. *)


       
Section CSLED_RELOC.

Variable Instr_reloc_offset: list Instruction -> res Z.



(* unfinished: we should add conditional checking for W bit, which can ensure the deocde_consistency *)
Definition decode_instr_rex (instr_ofs: Z) (res_iofs: res Z) (W R X B: bool) (i: Instruction) : res instruction :=
  let translate_AddrE_Addrmode := translate_AddrE_Addrmode instr_ofs res_iofs X B in
  match i with
  | Pmovl_rm (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pmov_rr rd rs)
  | Pmovl_rm a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then
      OK (Asm.Pmovq_rm rd addr)
    else
      OK (Asm.Pmovl_rm rd addr)
  | Pmovl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    OK (Asm.Pmovl_ri rd imm)
  | Pmovl_mr a rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then
      OK (Asm.Pmovq_mr addr rs)
    else
      OK (Asm.Pmovl_mr addr rs)
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
  (* special: Pmovb_mr *)
  | Pmovb_mr a rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovb_mr addr rs)
  (* special: Pmovzb_rr*)
  | Pmovzb_rm (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pmovzb_rr rd rs)
  | Pmovzb_rm a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovzb_rm rd addr)
  | Pmovzw_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pmovzw_rr rd rs)
  | Pmovzw_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovzw_rm rd addr)
  (* special: Pmovsb_rm*)
  | Pmovsb_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pmovsb_rr rd rs)
  | Pmovsb_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsb_rm rd addr)
  (* special: Pmovb_rm *)
  | Pmovb_rm a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovb_rm rd addr)
  | Pmovsw_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pmovsw_rr rd rs)
  | Pmovsw_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsw_rm rd addr)
  | Pnegl rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pnegq rd)
    else OK (Asm.Pnegl rd)
  | Pleal a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Pleaq rd addr)
    else OK (Asm.Pleal rd addr)
  | Paddl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Paddl_ri rd imm)
  | Psubl_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Psubq_rr rd rs)
    else OK (Asm.Psubl_rr rd rs)
  | Psubl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Psubq_rm rd addr)
    else Error (msg "unsupported")
  | Pimull_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pimulq_rr rd rs)
    else OK (Asm.Pimull_rr rd rs)
  | Pimull_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Pimulq_rm rd addr)
    else Error (msg "unsupported")
  | Pimull_r rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pimulq_r rd)
    else OK (Asm.Pimull_r rd)
  | Pimull_ri rdbits _ imm32 =>
    (* do not check rdbits = rsbits *)
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pimull_ri rd imm)
  | Pmull_r rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pmulq_r rd)
    else OK (Asm.Pmull_r rd)
  | Pcltd => 
    if W then OK Asm.Pcqto
    else OK Asm.Pcltd
  | Pdivl_r rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pdivq rd)
    else OK (Asm.Pdivl rd)
  | Pidivl_r rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pidivq rd)
    else OK (Asm.Pidivl rd)
  | Pandl_EvGv (AddrE0 rdbits) rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pandl_rr rd rs)
  | Pandl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pandl_ri rd imm)
  | Porl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Porl_ri rd imm)
  | Porl_EvGv (AddrE0 rdbits) rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Porl_rr rd rs)
  | Pxorl_EvGv (AddrE0 rdbits) rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorl_rr rd rs)
  | Pxorl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorl_ri rd imm)
  | Pnotl rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Pnotq rd)
    else OK (Asm.Pnotl rd)
  | Psall_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then OK (Asm.Psalq_ri rd imm)
    else OK (Asm.Psall_ri rd imm)
  | Psall_rcl rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Psalq_rcl rd)
    else OK (Asm.Psall_rcl rd)
  | Pshrl_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then OK (Asm.Pshrq_ri rd imm)
    else OK (Asm.Pshrl_ri rd imm)
  | Psarl_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then OK (Asm.Psarq_ri rd imm)
    else OK (Asm.Psarl_ri rd imm)
  | Psarl_rcl rbits =>
    let rd := decode_ireg_u4 B rbits in
    if W then OK (Asm.Psarq_rcl rd)
    else OK (Asm.Psarl_rcl rd)
  (* special: Asm.Pshld_ri rd r1 imm*)
  | Pshld_ri rsbits rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pshld_ri rd rs imm)
  | Prorl_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then OK (Asm.Prorq_ri rd imm)
    else OK (Asm.Prorl_ri rd imm)
  | Pcmpl_EvGv (AddrE0 r1bits) r2bits =>
    let r2 := decode_ireg_u4 R r2bits in
    let r1 := decode_ireg_u4 B r1bits in
    if W then OK (Asm.Pcmpq_rr r1 r2)
    else OK (Asm.Pcmpl_rr r1 r2)
  | Pcmpl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pcmpl_ri rd imm)
  | Ptestl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Ptestl_ri rd imm)
  | Ptestl_EvGv (AddrE0 r1bits) r2bits =>
    let r2 := decode_ireg_u4 R r2bits in
    let r1 := decode_ireg_u4 B r1bits in
    if W then OK (Asm.Ptestq_rr r1 r2)
    else OK (Asm.Ptestl_rr r1 r2)
  (* special : Pcmov *)
  | Pcmov cond rdbits rsbits =>
    do c <- decode_testcond_u4 cond;
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    OK (Asm.Pcmov c rd rs)
  (* special : Psetcc *)
  | Psetcc cond rdbits =>
    let rd := decode_ireg_u4 B rdbits in
    do c <- decode_testcond_u4 cond;
    OK (Asm.Psetcc c rd)
  | Pcomiss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pcomiss_ff rd rs)       
  (* rd = rs *)
  | Pxorps_d_GvEv (AddrE0 rsbits) rdbits =>
    (* not check rsbits = rdbits *)
    let rd := decode_freg_u4 R rdbits in
    (* let rs := decode_ireg_u4 B rsbits in *)
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorps_f rd)
  | Pxorps_d_GvEv a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorps_fm rd addr)
  | Pandps_d_fm a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pandps_fm rd addr)
  (* so special : Pjmp_l_rel *)
  | Pjmp_l_rel imm32 =>
    do iofs <- res_iofs;
    match ZTree.get (iofs + instr_ofs) rtbl_ofs_map with
    | Some _ =>
      OK (Asm.Pjmp_s xH signature_main)
    | None =>
      let imm := decode_ofs_u32 imm32 in
      OK (Asm.Pjmp_l_rel (Int.intval imm))
    end
  (* not well defined *)
  | Pjmp_Ev (AddrE0 rsbits)=>
    let rs := decode_ireg_u4 B rsbits in
    if W then Error (msg "impossible")
    else OK (Asm.Pjmp_r rs signature_main)
  | Pjmp_Ev a =>
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "impossible")
    else OK (Asm.Pjmp_m addr)
  | Pnop => OK Asm.Pnop
  | Pcall_r rbits =>
    let r := decode_ireg_u4 B rbits in
    OK (Asm.Pcall_r r signature_main)
  | Pcall_ofs imm32 =>
    do iofs <- res_iofs;
    match ZTree.get (iofs + instr_ofs) rtbl_ofs_map with
    | Some _ =>
      OK (Asm.Pcall_s xH signature_main)
    | None =>
      Error (msg "impossible")
    end
  | Pret => OK Asm.Pret
  | Pret_iw imm16 =>
    let imm := decode_ofs_u16 imm16 in
    OK (Asm.Pret_iw imm)
  | Pjcc_rel cond imm32 =>
    do c <- decode_testcond_u4 cond;
    let imm := decode_ofs_u32 imm32 in
    OK (Asm.Pjcc_rel c (Int.intval imm))
  | Padcl_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Padcl_ri rd imm)
  | Padcl_rr rsbits rdbits =>
    let rs := decode_ireg_u4 R rsbits in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Padcl_rr rd rs)
  | Paddl_EvGv (AddrE0 rdbits) rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Paddl_rr rd rs)
  | Paddl_mi a imm32 =>
    let imm := decode_ofs_u32 imm32 in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Paddl_mi addr imm)
  | Pbsfl rdbits rsbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pbsfq rd rs)
    else OK (Asm.Pbsfl rd rs)
  | Pbsrl rdbits rsbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pbsrq rd rs)
    else OK (Asm.Pbsrl rd rs)
  | Pbswap32 rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    if W then OK (Asm.Pbswap64 rd)
    else OK (Asm.Pbswap32 rd)
  | Psbbl_rr rsbits rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Psbbl_rr rd rs)
  | Psubl_ri rdbits imm32 =>
    let imm := decode_ofs_u32 imm32 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Psubl_ri rd imm)
  | Pshrl_rcl rdbits =>
    let rd := decode_ireg_u4 B rdbits in
    if W then OK (Asm.Pshrq_rcl rd)
    else OK (Asm.Pshrl_rcl rd)
              | Paddl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Paddq_rm rd addr)
    else Error (msg "unsupported")
              (* 64bit *)
               
  | Pmovsxd_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pmovsl_rr rd rs)
    else Error (msg "unsupported")               
  | Pandl_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pandq_rr rd rs)
    else Error (msg "unsupported")
  | Pandl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Pandq_rm rd addr)
    else Error (msg "unsupported")
  | Porl_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Porq_rr rd rs)
    else Error (msg "unsupported")
  | Porl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Porq_rm rd addr)
    else Error (msg "unsupported")
  | Pxorl_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then OK (Asm.Pxorq_rr rd rs)
    else Error (msg "unsupported")
  | Pxorl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Pxorq_rm rd addr)
    else Error (msg "unsupported")
  | Pcmpl_GvEv a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Pcmpq_rm rd addr)
    else Error (msg "unsupported")
  | Ptestl_EvGv a rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then OK (Asm.Ptestq_rm rs addr)
    else Error (msg "unsupported")
  | _ => Error (msg "unsupported")
  end.

Definition decode_instr_override (instr_ofs: Z) (res_iofs: res Z)  (W R X B: bool) (i: Instruction) : res instruction :=
  let translate_AddrE_Addrmode := translate_AddrE_Addrmode instr_ofs res_iofs X B in
  match i with
  | Pmovl_rm a rdbits =>
    let rd := decode_ireg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovw_rm rd addr)
  | Pmovl_mr a rsbits =>
    let rs := decode_ireg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovw_mr addr rs)
  | Prolw_ri rdbits imm8 =>
    let imm := decode_ofs_u8 imm8 in
    let rd := decode_ireg_u4 B rdbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Prolw_ri rd imm)
  | Pcomiss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pcomisd_ff rd rs)
  (* rd = rs *)
  | Pxorps_d_GvEv (AddrE0 rsbits) rdbits =>
    let rd := decode_freg_u4 R rdbits in
    (* let rs := decode_ireg_u4 B rsbits in *)
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorpd_f rd)
  | Pxorps_d_GvEv a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pxorpd_fm rd addr)
  | Pandps_d_fm a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pandpd_fm rd addr)
  | Pmovsq_mr a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pmovsq_mr addr rd)
  | _ => Error (msg "unsupported")
  end.

Definition decode_instr_repnz (instr_ofs: Z) (res_iofs: res Z) (W R X B: bool) (i: Instruction) : res instruction :=
  let translate_AddrE_Addrmode := translate_AddrE_Addrmode instr_ofs res_iofs X B in
  match i with
  | Pmovss_d_fm (AddrE0 rsbits) rdbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pmovsd_ff rd rs)
  | Pmovss_d_fm a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsd_fm rd addr)
  | Pmovss_d_mf a rsbits =>
    let rs := decode_freg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovsd_mf addr rs)
  | Pcvttss_d_2si_rf rdbits rsbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then
      OK (Asm.Pcvttsd2sl_rf rd rs)
    else
      OK (Asm.Pcvttsd2si_rf rd rs)
  | Pcvtsi2ss_d_fr rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then
      OK (Asm.Pcvtsl2sd_fr rd rs)
    else
      OK (Asm.Pcvtsi2sd_fr rd rs)
  | Pcvtsd2ss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pcvtsd2ss_ff rd rs)
  | Padds_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Paddd_ff rd rs)
  | Psubs_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Psubd_ff rd rs)
  | Pmuls_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pmuld_ff rd rs)
  | Pmaxsd rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pmaxsd rd rs)
  | Pminsd rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pminsd rd rs)
  | Pbsqrtsd rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Psqrtsd rd rs)
  | Pdivss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pdivd_ff rd rs)
  | _ => Error (msg "unsupported")
  end.

Definition decode_instr_rep (instr_ofs: Z) (res_iofs: res Z)  (W R X B: bool) (i: Instruction) : res instruction :=
  let translate_AddrE_Addrmode := translate_AddrE_Addrmode instr_ofs res_iofs X B in
  match i with
  | Pmovss_d_fm a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovss_fm rd addr)
  | Pmovss_d_mf a rsbits =>
    let rs := decode_freg_u4 R rsbits in
    do addr <- translate_AddrE_Addrmode a;
    OK (Asm.Pmovss_mf addr rs)
  | Pcvttss_d_2si_rf rdbits rsbits =>
    let rd := decode_ireg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then
      OK (Asm.Pcvttss2sl_rf rd rs)
    else
      OK (Asm.Pcvttss2si_rf rd rs)
  | Pcvtsi2ss_d_fr rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_ireg_u4 B rsbits in
    if W then
      OK (Asm.Pcvtsl2ss_fr rd rs)
    else
      OK (Asm.Pcvtsi2ss_fr rd rs)
  | Pcvtsd2ss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pcvtss2sd_ff rd rs)
  | Padds_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Padds_ff rd rs)
  | Psubs_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Psubs_ff rd rs)
  | Pmuls_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    OK (Asm.Pmuls_ff rd rs)
  | Pmovsq_rm a rdbits =>
    let rd := decode_freg_u4 R rdbits in
    do addr <- translate_AddrE_Addrmode a;
    if W then Error (msg "unsupported")
    else OK (Asm.Pmovsq_rm rd addr)
  | Prep_movsl => OK Asm.Prep_movsl
  | Pdivss_d_ff rdbits rsbits =>
    let rd := decode_freg_u4 R rdbits in
    let rs := decode_freg_u4 B rsbits in
    if W then Error (msg "unsupported")
    else OK (Asm.Pdivs_ff rd rs)
  | _ => Error (msg "unsupported")
  end.


Definition decode_instr (instr_ofs: Z) (li:list Instruction) :=
  let res_iofs := Instr_reloc_offset li in
  let decode_instr_rex := decode_instr_rex instr_ofs res_iofs in
  let decode_instr_override := decode_instr_override instr_ofs res_iofs in
  let decode_instr_rep := decode_instr_rep instr_ofs res_iofs in
  let decode_instr_repnz := decode_instr_repnz instr_ofs res_iofs in
  match li with
  | Override :: REX_WRXB w r x b :: i :: _ =>
    decode_instr_override w r x b i
  | REP :: REX_WRXB w r x b :: i :: _ =>
    decode_instr_rep w r x b i
  | REPNZ :: REX_WRXB w r x b :: i :: _ =>
    decode_instr_repnz w r x b i
  | REX_WRXB w r x b :: i :: _ =>
    decode_instr_rex w r x b i
  | Override :: i :: _ =>
    decode_instr_override false false false false i
  | REP :: i :: _ =>
    decode_instr_rep false false false false i
  | REPNZ :: i :: _ =>
    decode_instr_repnz false false false false i
  | i :: _ =>
    decode_instr_rex false false false false i
  | _ => Error (msg "impossible")
  end.

  



Lemma encode_rex_prefix_rr_result: forall r b l rs bs,
    encode_rex_prefix_rr r b = OK (l, rs, bs) ->
    (l = [] /\ decode_ireg_u4 false rs = r /\ decode_ireg_u4 false bs = b) \/
    (exists rexr rexb, l = [REX_WRXB zero1 rexr zero1 rexb] /\ decode_ireg_u4 rexr rs = r /\ decode_ireg_u4 rexb bs = b).
Proof.
  unfold encode_rex_prefix_rr.
  intros r b l rs bs.
  destr;destr.
  admit.
  destr. intro H.
  monadInv H.  right.
  exists zero1,ProdL. assert (decode_ireg_u4 false rs = r) by admit.
  admit.
Admitted.

Lemma encode_rex_prefix_r_result: forall b l bs,
    encode_rex_prefix_r b = OK (l, bs) ->
    (l = [] /\  decode_ireg_u4 false bs = b) \/
    (exists rexb, l = [REX_WRXB zero1 zero1 zero1 rexb] /\ decode_ireg_u4 rexb bs = b).
Admitted.


Lemma encode_rex_prefix_ff_result: forall r b l rs bs,
    encode_rex_prefix_ff r b = OK (l, rs, bs) ->
    (l = [] /\ decode_freg_u4 false rs = r /\ decode_freg_u4 false bs = b) \/
    (exists rexr rexb, l = [REX_WRXB zero1 rexr zero1 rexb] /\ decode_freg_u4 rexr rs = r /\ decode_freg_u4 rexb bs = b).
Admitted.

Lemma encode_rex_prefix_fr_result: forall r b l rs bs,
    encode_rex_prefix_fr r b = OK (l, rs, bs) ->
    (l = [] /\ decode_freg_u4 false rs = r /\ decode_ireg_u4 false bs = b) \/
    (exists rexr rexb, l = [REX_WRXB zero1 rexr zero1 rexb] /\ decode_freg_u4 rexr rs = r /\ decode_ireg_u4 rexb bs = b).
Admitted.

Lemma encode_rex_prefix_rf_result: forall r b l rs bs,
    encode_rex_prefix_rf r b = OK (l, rs, bs) ->
    (l = [] /\ decode_ireg_u4 false rs = r /\ decode_freg_u4 false bs = b) \/
    (exists rexr rexb, l = [REX_WRXB zero1 rexr zero1 rexb] /\ decode_ireg_u4 rexr rs = r /\ decode_freg_u4 rexb bs = b).
Admitted.



Lemma encode_rex_prefix_ra_result: forall instr_ofs res_iofs r addr l rs a,
    encode_rex_prefix_ra instr_ofs res_iofs r addr = OK (l,rs,a) ->
    (not_AddrE0 a = true) /\
    ((l = [] /\  decode_ireg_u4 false rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs false false a = OK addr) \/
    (exists rexr rexx rexb , l = [REX_WRXB zero1 rexr rexx rexb] /\  decode_ireg_u4 rexr rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs rexx rexb a = OK addr)).
Proof.
  unfold encode_rex_prefix_ra.
  intros instr_ofs res_iofs r addr l rs a H.
  repeat destr_in H.
  - monadInv H11.
    apply transl_addr_consistency32 in EQ1.
    destruct EQ1. split;auto. left.
    split;split;auto with encdec.
    admit.
  - monadInv H11.
    apply transl_addr_consistency64 in EQ1.
    destruct EQ1. split;auto. right.
    exists zero1,ProdR0,ProdR. split;split;auto with encdec.
    admit.
  - monadInv H11.
    apply transl_addr_consistency32 in EQ1.
    destruct EQ1. split;auto. right.
    exists ProdL,zero1,zero1.
    split;split;auto with encdec.
  - monadInv H11.
    apply transl_addr_consistency64 in EQ1.
    destruct EQ1. split;auto. right.
    exists ProdL,ProdR1,ProdR0.
    split;split;auto with encdec.    
Admitted.

Lemma encode_rex_prefix_fa_result: forall instr_ofs res_iofs r addr l rs a,
    encode_rex_prefix_fa instr_ofs res_iofs r addr = OK (l,rs,a) ->
    (not_AddrE0 a = true) /\
    ((l = [] /\  decode_freg_u4 false rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs false false a = OK addr) \/
    (exists rexr rexx rexb , l = [REX_WRXB zero1 rexr rexx rexb] /\  decode_freg_u4 rexr rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs rexx rexb a = OK addr)).
Admitted.

Lemma encode_rex_prefix_addr_result: forall instr_ofs res_iofs addr l a,
    encode_rex_prefix_addr instr_ofs res_iofs addr = OK (l,a) ->
    (not_AddrE0 a = true) /\
    ((l = [] /\  translate_AddrE_Addrmode instr_ofs res_iofs false false a = OK addr) \/
    (exists rexx rexb , l = [REX_WRXB zero1 zero1 rexx rexb] /\ translate_AddrE_Addrmode instr_ofs res_iofs rexx rexb a = OK addr)).
Admitted.


Hint Unfold decode_instr_rex decode_instr_rep decode_instr_repnz decode_instr decode_instr_override: decunfold.


(* false if the encoded instruction unable to decode to itself *)
Definition well_defined_instr i :=
  match i with
  | Pmovsd_mf_a _ _
  | Pmovsd_fm_a _ _
  | Pxorq_r _
  | Pmov_mr_a _ _ | Pmov_rm_a _ _
  | Asm.Pcall_r _ _
  | Asm.Plabel _ | Asm.Pmovls_rr _
  | Asm.Pjmp_r _ _
  | Asm.Pjmp_s _ _
  | Asm.Pmovzl_rr _ _
  | Asm.Pcall_s _ _
  | Asm.Pxorl_r _ => false
  | _ => true
  end.

Ltac solve_rr :=
    exploit encode_rex_prefix_rr_result;eauto;
    intros [(? & ? & ?) | (? & ? & ? & ? & ?)];subst;simpl;auto.

Ltac solve_ff :=
    exploit encode_rex_prefix_ff_result;eauto;
    intros [(? & ? & ?) | (? & ? & ? & ? & ?)];subst;simpl;auto.

Ltac solve_rf :=
  exploit encode_rex_prefix_rf_result;eauto;
  intros [(? & ? & ?) | (? & ? & ? & ? & ?)];subst;simpl;auto.


Ltac solve_fr :=
    exploit encode_rex_prefix_fr_result;eauto;
    intros [(? & ? & ?) | (? & ? & ? & ? & ?)];subst;simpl;auto.

Ltac solve_only_r :=
    exploit encode_rex_prefix_r_result;eauto;
    intros [(? & ?) | (? & ? & ?)];subst;simpl;auto.

Ltac solve_ri32 :=
  exploit encode_rex_prefix_r_result;eauto;
  exploit encode_ofs_u32_consistency;eauto;
  intros ?;intros [(? & ?) | (? & ? & ?)];subst;simpl;auto.

Ltac solve_ri8 :=
  exploit encode_rex_prefix_r_result;eauto;
  exploit encode_ofs_u8_consistency;eauto;
  intros ?;intros [(? & ?) | (? & ? & ?)];subst;simpl;auto.

Ltac solve_ri16 :=
  exploit encode_rex_prefix_r_result;eauto;
  exploit encode_ofs_u16_consistency;eauto;
  intros ?;intros [(? & ?) | (? & ? & ?)];subst;simpl;auto.


Ltac solve_ra RELOC:=
  exploit encode_rex_prefix_ra_result;eauto;
  intros (NOTADDRE0 & [(? & ? & A) | (? & ? & ? & ? & ? & A)]);
  subst;cbn [app] in *;autounfold with decunfold;
  rewrite RELOC;rewrite A;
  cbn [bind];auto;
  try destr;simpl in NOTADDRE0;try congruence.

Ltac solve_fa RELOC:=
  exploit encode_rex_prefix_fa_result;eauto;
  intros (NOTADDRE0 & [(? & ? & A) | (? & ? & ? & ? & ? & A)]);
  subst;cbn [app] in *;autounfold with decunfold;
  rewrite RELOC;rewrite A;
  cbn [bind];auto;
  try destr;simpl in NOTADDRE0;try congruence.

(* rex_prefix unused case *)
Ltac solve_normal:=
  (* so adhoc: prevent so much time-consuming in other case *)
  cbn [app] in *;autounfold with decunfold;
  simpl;                      (* eliminate decode_u1 *)
  try (do 2 f_equal);auto with encdec.


Ltac solve_ra64_normal RELOC :=  
  exploit encode_ireg_u4_consistency;eauto;intros;subst;
  exploit transl_addr_consistency64;eauto;intros (NOTADDRE0 & A);
  cbn [app] in *;autounfold with decunfold;
  rewrite RELOC;rewrite A;
  cbn [bind];auto;
  try destr;simpl in NOTADDRE0;try congruence.

Ltac solve_only_addr RELOC:=
  exploit encode_rex_prefix_addr_result; eauto;
  intros (NOTADDRE0 & [(? & A) | (? & ? & ? & A)]);
  subst;cbn [app] in *;autounfold with decunfold;
  rewrite RELOC;rewrite A;
  cbn [bind];auto;
  try destr;simpl in NOTADDRE0;try congruence.

Ltac destr_ptr64_in_H H :=
  match type of H with
  | context [Archi.ptr64] =>
    destruct Archi.ptr64
  end.

Ltac solve_decode_instr H RELOC :=
  monadInv H;auto;
  match goal with
  | H1: encode_rex_prefix_addr _ _ _ = OK _ |- _ =>
    solve_only_addr RELOC
  | H1: encode_ireg_u4 _ = OK _,
        H2: translate_Addrmode_AddrE64 _ _ _ = OK _ |- _ =>
    solve_ra64_normal RELOC
  | H1: encode_freg_u4 ?r1 = OK ?res1,
        H2: encode_freg_u4 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_ireg_u4 ?r1 = OK ?res1,
        H2: encode_freg_u4 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_ireg_u4 ?r1 = OK ?res1,
        H2: encode_ireg_u4 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_ireg_u4 ?r1 = OK ?res1,
        H2: encode_ofs_u32 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_ireg_u4 ?r1 = OK ?res1,
        H2: encode_ofs_u16 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_ireg_u4 ?r1 = OK ?res1,
        H2: encode_ofs_u8 ?r2 = OK ?res2
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | H1: encode_rex_prefix_fa _ _ _ _ = OK _ |- _ =>
    solve_fa RELOC
  | H1: encode_rex_prefix_ra _ _ _ _ = OK _ |- _ =>
    solve_ra RELOC
  | H1: encode_rex_prefix_r _ = OK _,
        H2:encode_ofs_u16 _ = OK _ |- _ =>
    solve_ri16
  | H1: encode_rex_prefix_r _ = OK _,
        H2:encode_ofs_u8 _ = OK _ |- _ =>
    solve_ri8
  | H1: encode_rex_prefix_r _ = OK _,
        H2:encode_ofs_u32 _ = OK _ |- _ =>
    solve_ri32
  | H1: encode_rex_prefix_r _ = OK _ |- _ =>
    solve_only_r
  | H1: encode_rex_prefix_rf _ _ = OK _ |- _ =>
    solve_rf
  | H1: encode_rex_prefix_fr _ _ = OK _ |- _ =>
    solve_fr
  | H1: encode_rex_prefix_ff _ _ = OK _ |- _ =>
    solve_ff
  | H1: encode_rex_prefix_rr _ _ = OK _ |- _ =>
    solve_rr
  (* only encode ireg, place to the end *)
  | H1: encode_ireg_u4 ?r1 = OK ?res1
    |- context [REX_WRXB ?a ?b ?c ?d :: ?l] =>
    solve_normal
  | _ => fail
  end.
  
Hypothesis encode_reloc_offset_conform: forall i iofs li l,
  translate_instr iofs i = OK li ->
  Instr_reloc_offset (li++l) = instr_reloc_offset i.

Theorem translate_instr_consistency: forall instr_ofs i li l,
    well_defined_instr i = true ->
    translate_instr instr_ofs i = OK li ->
    decode_instr instr_ofs (li++l) = OK i.
Proof.
  intros instr_ofs i li l WD H.
  exploit (encode_reloc_offset_conform i instr_ofs li l);eauto.
  intros RELOC.
  unfold translate_instr in H;
    destruct i;simpl in WD;try congruence;clear WD;
      try destr_ptr64_in_H H;
      try solve_decode_instr H RELOC;
      try (do 2 f_equal;auto with encdec).

  (* Pimull_ri *)
  exploit encode_rex_prefix_rr_result;eauto.
  intros [(?, (?, ?))| (?, (?, (?, (?, ?))))]; subst.
  exploit decode_ireg_u4_inject1;eauto;intros.
  rewrite <- H13 in *.
  exploit decode_ireg_u4_inject2;eauto;intros;subst.
  exploit decode_ireg_u4_inject1. apply H11. intro.
  rewrite H14 in *. auto.
  inv H. exploit decode_ireg_u4_inject1. apply H11.
  intros. rewrite H. auto.
  

  (* testcond *)
  1-10 : try (rewrite encode_testcond_consistency;simpl;
  do 2 f_equal;auto with encdec).

  monadInv H. simpl. do 2 f_equal;auto with encdec.
  
  (* Paddmi *)
  generalize Heqb.
  unfold zero1. simpl. unfold char_to_bool.
  simpl. unfold decode_u1. simpl. congruence.

  monadInv H. destr_in EQ0. destr_in EQ0.
  monadInv EQ0. cbn [app] in *. autounfold with decunfold.
  simpl in RELOC.
  rewrite RELOC. cbn [bind]. inv EQ.
  rewrite Heqo. do 2 f_equal.
  apply andb_true_iff  in Heqb. destruct Heqb.
  assert (0 <= ofs < Int.modulus).
  split. 
  apply Z.leb_le;eauto. apply Z.ltb_lt;eauto.  
  apply encode_ofs_u32_consistency_aux;eauto.
  (* intros. *)
  (* rewrite H12. unfold Int.repr. simpl. *)
  (* rewrite Int.Z_mod_modulus_eq. *)
  (* rewrite Z.mod_eq. erewrite Z.div_small;eauto. *)
  (* rewrite Z.mul_0_r. rewrite Z.sub_0_r. auto. *)
  (* generalize  Int.modulus_pos. lia. *)

  destr_in H.
  monadInv H. cbn [app] in *. autounfold with decunfold.
  rewrite encode_testcond_consistency. cbn [bind].
  do 2 f_equal.
  apply andb_true_iff  in Heqb. destruct Heqb.
  assert (0 <= ofs < Int.modulus).
  split. 
  apply Z.leb_le;eauto. apply Z.ltb_lt;eauto.  
  apply encode_ofs_u32_consistency_aux;eauto.
Qed.

  
End CSLED_RELOC.

End WITH_RELOC_OFS_MAP.

