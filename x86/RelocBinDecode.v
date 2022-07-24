Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Axioms Globalenvs.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
Require Import Coq.Logic.Eqdep_dec.
Require Import EncDecRet BPProperty.
Require Import TranslateInstr.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(** *Decode Instruction *)

Section CSLED_RELOC.

Variable rtbl_ofs_map: reloc_ofs_map_type.
Variable Instr_reloc_offset: list Instruction -> res Z.

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
  unfold val.
Admitted.

Lemma encode_ofs_signed32_consistency: forall ofs l,
    encode_ofs_signed32 ofs = OK l ->
    decode_ofs_signed32 l = ofs.
Proof.
  unfold encode_ofs_signed32.
  unfold decode_ofs_signed32.
  intros. destr_in H.
  exploit encode_ofs_u32_consistency;eauto.
  intros. rewrite H10.
  eapply Int.signed_repr.
  apply andb_true_iff in Heqb. destruct Heqb.
  apply Z.leb_le in H11.   apply Z.leb_le in H12.
  lia.
Qed.

Hint Resolve encode_ireg_u4_consistency encode_freg_u4_consistency encode_ofs_u32_consistency encode_ofs_u8_consistency encode_ofs_u16_consistency encode_testcond_consistency encode_scale_consistency encode_ofs_u32_consistency_aux encode_ofs_signed32_consistency: encdec.



(** *addrmode decoder *)

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
      let ofs := decode_ofs_signed32 imm in
      if ireg_eq index RSP then
        OK (Addrmode (Some base) None (inl ofs))
      else
        OK (Addrmode (Some base) (Some (index,scale)) (inl ofs))       
    | AddrE9 s i imm =>
      let scale := decode_scale s in
      let ofs := decode_ofs_signed32 imm in
      let index := decode_ireg_u4 X i in
      if ireg_eq index RSP then
        if Archi.ptr64 then
          OK (Addrmode None None (inl ofs))
        else Error (msg "impossible: translate_AddrE_Addrmode")
      else
        OK (Addrmode None (Some (index,scale)) (inl ofs))
    | AddrE11 imm =>
      let ofs := decode_ofs_signed32 imm in
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
    translate_Addrmode_AddrE rtbl_ofs_map sofs res_iofs addr = OK a ->
    not_AddrE0 a = true /\ translate_AddrE_Addrmode sofs res_iofs false false a = OK addr.
Proof.
  unfold translate_Addrmode_AddrE.
  destruct addr.
  destruct base;destruct ofs;intros ad sofs res_iofs H.
  - destr_in H.
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux32 in EQ2.
      destr_in EQ2.
      * monadInv EQ2.
        split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo. rewrite Heqb.
        admit.
      * inv EQ2. split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo.
        do 4 f_equal.
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
    translate_Addrmode_AddrE64 rtbl_ofs_map sofs res_iofs addr = OK (a, x, b) ->
    not_AddrE0 a = true /\ translate_AddrE_Addrmode sofs res_iofs x b a = OK addr.

  unfold translate_Addrmode_AddrE64.
  destruct addr.
  destruct base;destruct ofs;intros ad sofs res_iofs x b H.
  - destr_in H.
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
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
    + monadInv H. destr_in EQ0.
      monadInv EQ0.
      unfold translate_Addrmode_AddrE_aux64 in EQ2.
      destr_in EQ2.
      * monadInv EQ2.
        split. simpl;auto.
        unfold translate_AddrE_Addrmode. cbn [bind].
        rewrite Heqo. rewrite Heqb0.
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
      let imm := decode_ofs_signed32 imm32 in
      OK (Asm.Pjmp_l_rel imm)
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
    let imm := decode_ofs_signed32 imm32 in
    OK (Asm.Pjcc_rel c imm)
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
    let rd := decode_ireg_u4 B rdbits in
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
    encode_rex_prefix_ra rtbl_ofs_map instr_ofs res_iofs r addr = OK (l,rs,a) ->
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
    encode_rex_prefix_fa rtbl_ofs_map instr_ofs res_iofs r addr = OK (l,rs,a) ->
    (not_AddrE0 a = true) /\
    ((l = [] /\  decode_freg_u4 false rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs false false a = OK addr) \/
    (exists rexr rexx rexb , l = [REX_WRXB zero1 rexr rexx rexb] /\  decode_freg_u4 rexr rs = r /\ translate_AddrE_Addrmode instr_ofs res_iofs rexx rexb a = OK addr)).
Admitted.

Lemma encode_rex_prefix_addr_result: forall instr_ofs res_iofs addr l a,
    encode_rex_prefix_addr rtbl_ofs_map instr_ofs res_iofs addr = OK (l,a) ->
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
  | H1: encode_rex_prefix_addr _ _ _ _ = OK _ |- _ =>
    solve_only_addr RELOC
  | H1: encode_ireg_u4 _ = OK _,
        H2: translate_Addrmode_AddrE64 _ _ _ _ = OK _ |- _ =>
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
  | H1: encode_rex_prefix_fa _ _ _ _ _ = OK _ |- _ =>
    solve_fa RELOC
  | H1: encode_rex_prefix_ra _ _ _ _ _ = OK _ |- _ =>
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
  translate_instr rtbl_ofs_map iofs i = OK li ->
  Instr_reloc_offset (li++l) = instr_reloc_offset i.

Theorem translate_instr_consistency: forall instr_ofs i li l,
    well_defined_instr i = true ->
    translate_instr rtbl_ofs_map instr_ofs i = OK li ->
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

  monadInv H. destr_in EQ0.
  monadInv EQ0. cbn [app] in *. autounfold with decunfold.
  simpl in RELOC.
  rewrite RELOC. cbn [bind]. inv EQ.
  rewrite Heqo. do 2 f_equal.
  auto with encdec.
  (* intros. *)
  (* rewrite H12. unfold Int.repr. simpl. *)
  (* rewrite Int.Z_mod_modulus_eq. *)
  (* rewrite Z.mod_eq. erewrite Z.div_small;eauto. *)
  (* rewrite Z.mul_0_r. rewrite Z.sub_0_r. auto. *)
  (* generalize  Int.modulus_pos. lia. *)

  monadInv H. cbn [app] in *. autounfold with decunfold.
  rewrite encode_testcond_consistency. cbn [bind].
  do 2 f_equal. auto with encdec.
Qed.

End CSLED_RELOC.
