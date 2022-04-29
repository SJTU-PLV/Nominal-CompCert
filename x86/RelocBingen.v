(* *******************  *)
(* Author: Yuting Wang  *)
(*         Jinhua Wu    *)
(* Date:   Sep 18, 2019 *)
(* Last updated: Feb 5, 2022 by Jinhua Wu*)
(* **********   *********  *)

Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProgram.
Require Import encode.Hex encode.Bits Memdata encode.Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
Require Import TranslateInstr1.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(* (** * Encoding of instructions and functions *) *)

(* Definition encode_ireg (r: ireg) : res bits := *)
(*   match r with *)
(*   | RAX => OK (b["000"]) *)
(*   | RCX => OK (b["001"]) *)
(*   | RDX => OK (b["010"]) *)
(*   | RBX => OK (b["011"]) *)
(*   | RSP => OK (b["100"]) *)
(*   | RBP => OK (b["101"]) *)
(*   | RSI => OK (b["110"]) *)
(*   | RDI => OK (b["111"]) *)
(*   | _ => Error (msg "Encoding of register not supported") *)
(*   end. *)

(* Definition encode_freg (r: freg) : res bits := *)
(*   match r with *)
(*   | XMM0 => OK (b["000"]) *)
(*   | XMM1 => OK (b["001"]) *)
(*   | XMM2 => OK (b["010"]) *)
(*   | XMM3 => OK (b["011"]) *)
(*   | XMM4 => OK (b["100"]) *)
(*   | XMM5 => OK (b["101"]) *)
(*   | XMM6 => OK (b["110"]) *)
(*   | XMM7 => OK (b["111"]) *)
(*   | _ => Error (msg "Encoding of freg not supported") *)
(*   end. *)

(* Definition encode_scale (s: Z) : res bits := *)
(*   match s with *)
(*   | 1 => OK b["00"] *)
(*   | 2 => OK b["01"] *)
(*   | 4 => OK b["10"] *)
(*   | 8 => OK b["11"] *)
(*   | _ => Error (msg "Translation of scale failed") *)
(*   end. *)

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

(** ** Encoding of the address modes *)

(** Encode the address mode except the displacement *)
Definition encode_addrmode_aux (a: addrmode) (rd:ireg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do rdbits <- encode_ireg rd;
  match ss, bs with
  | None, None =>
    (** No scale index and base register *)
    OK ([bB[b["00"] ++ rdbits ++ b["101"]]])

  | None, Some rb =>
    (** No scale index and with a base register *)
    do rbbits <- encode_ireg rb;
    if ireg_eq rb RSP then
    (** When the base register is RSP, an SIB byte for RSP following
    the ModR/M byte is needed *)
      let bits := b["10"] ++ rdbits ++ b["100"] ++
                  b["00"] ++ b["100"] ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
    else
    (** Otherwise, no SIB byte is needed *)
      OK ([bB[b["10"] ++ rdbits ++ rbbits]])

  | Some (rs, scale), None =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else
      (** With a scale and without a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      let bits := 
          b["00"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ b["101"] in
      OK (encode_int_big 2 (bits_to_Z bits))

  | Some (rs, scale), Some rb =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else    
      (** With a scale and a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      do rbbits <- encode_ireg rb;
      let bits := 
          b["10"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
  end.
    
(** Encode the full address mode *)
Definition encode_addrmode (sofs: Z) i (a: addrmode) (rd: ireg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do abytes <- encode_addrmode_aux a rd;
  do ofs <- match disp with
            | inl ofs =>
              match instr_reloc_offset i with
              |OK iofs =>
               match get_instr_reloc_addend' (iofs + sofs) with
               |OK entry => Error[MSG (instr_to_string i); MSG "unexpected relocEntry"]
               |Error _ => OK ofs
               end
              |Error _ => OK ofs
              end
            | inr (id, ofs) =>
             (***** Remove Proofs By Chris Start ******)
             (*
             if Ptrofs.eq_dec ofs Ptrofs.zero then
              *)
             (***** Remove Proofs By Chris End ******)
              match id with
              |xH => 
               (do iofs <- instr_reloc_offset i;
                get_instr_reloc_addend' (iofs + sofs))
              |_ => Error [MSG (instr_to_string i); MSG ":id is "; POS id; MSG "(expected 1)"]
              end
             (* else *)
             (*   Error [MSG "ptrofs is not zero ";MSG (instr_to_string i); MSG ":id is "; POS id; MSG "ofs: "] *)
            end;
  OK (abytes ++ (encode_int32 ofs)).

Definition encode_addrmode_aux_f (a: addrmode) (frd:freg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do rdbits <- encode_freg frd;
  match ss, bs with
  | None, None =>
    (** No scale index and base register *)
    OK ([bB[b["00"] ++ rdbits ++ b["101"]]])
  | None, Some rb =>
    (** No scale index and with a base register *)
    do rbbits <- encode_ireg rb;
    if ireg_eq rb RSP then
    (** When the base register is RSP, an SIB byte for RSP following
    the ModR/M byte is needed *)
      let bits := b["10"] ++ rdbits ++ b["100"] ++
                  b["00"] ++ b["100"] ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
    else
    (** Otherwise, no SIB byte is needed *)
      OK ([bB[b["10"] ++ rdbits ++ rbbits]])
  | Some (rs, scale), None =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else
      (** With a scale and without a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      let bits := 
          b["00"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ b["101"] in
      OK (encode_int_big 2 (bits_to_Z bits))
  | Some (rs, scale), Some rb =>
    if (ireg_eq rs RSP) then
      Error (msg "RSP cannot be the index of SIB")
    else    
      (** With a scale and a base register *)
      do scbits <- encode_scale scale;
      do rsbits <- encode_ireg rs;
      do rbbits <- encode_ireg rb;
      let bits := 
          b["10"] ++ rdbits ++ b["100"] ++
          scbits ++ rsbits ++ rbbits in
      OK (encode_int_big 2 (bits_to_Z bits))
  end.
    
(** Encode the full address mode with floating supported*)
Definition encode_addrmode_f (sofs: Z) i (a: addrmode) (frd: freg) : res (list byte) :=
  let '(Addrmode bs ss disp) := a in
  do abytes <- encode_addrmode_aux_f a frd;
  do ofs <- match disp with
           | inl ofs =>
              match instr_reloc_offset i with
              |OK iofs =>
               match get_instr_reloc_addend' (iofs + sofs) with
               |OK entry => Error[MSG (instr_to_string i); MSG "unexpected relocEntry"]
               |Error _ => OK ofs
               end
              |Error _ => OK ofs
              end
           | inr (id, ofs) =>
             (***** Remove Proofs By Chris Start ******)
             (*
             if Ptrofs.eq_dec ofs Ptrofs.zero then
             *)
             (***** Remove Proofs By Chris End ******)
               match id with
               |xH => (do iofs <- instr_reloc_offset i;
                      get_instr_reloc_addend' (iofs + sofs))
               |_ => Error [MSG (instr_to_string i); MSG ":id is "; POS id; MSG "(expected 1)"]
              end
             (* else *)
             (*   Error (msg "ptrofs is not zero") *)
           end;
  OK (abytes ++ (encode_int32 ofs)).

(** Encode the conditions *)
Definition encode_testcond (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["84"] :: nil
  | Cond_ne  => HB["0F"] :: HB["85"] :: nil
  | Cond_b   => HB["0F"] :: HB["82"] :: nil
  | Cond_be  => HB["0F"] :: HB["86"] :: nil
  | Cond_ae  => HB["0F"] :: HB["83"] :: nil
  | Cond_a   => HB["0F"] :: HB["87"] :: nil
  | Cond_l   => HB["0F"] :: HB["8C"] :: nil
  | Cond_le  => HB["0F"] :: HB["8E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["8D"] :: nil
  | Cond_g   => HB["0F"] :: HB["8F"] :: nil
  | Cond_p   => HB["0F"] :: HB["8A"] :: nil
  | Cond_np  => HB["0F"] :: HB["8B"] :: nil
  end.

Definition encode_testcond_cmov (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["44"] :: nil
  | Cond_ne  => HB["0F"] :: HB["45"] :: nil
  | Cond_b   => HB["0F"] :: HB["42"] :: nil
  | Cond_be  => HB["0F"] :: HB["46"] :: nil
  | Cond_ae  => HB["0F"] :: HB["43"] :: nil
  | Cond_a   => HB["0F"] :: HB["47"] :: nil
  | Cond_l   => HB["0F"] :: HB["4C"] :: nil
  | Cond_le  => HB["0F"] :: HB["4E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["4D"] :: nil
  | Cond_g   => HB["0F"] :: HB["4F"] :: nil
  | Cond_p   => HB["0F"] :: HB["4A"] :: nil
  | Cond_np  => HB["0F"] :: HB["4B"] :: nil
  end.

Definition encode_testcond_setcc (c:testcond) : list byte :=
  match c with
  | Cond_e   => HB["0F"] :: HB["94"] :: nil
  | Cond_ne  => HB["0F"] :: HB["95"] :: nil
  | Cond_b   => HB["0F"] :: HB["92"] :: nil
  | Cond_be  => HB["0F"] :: HB["96"] :: nil
  | Cond_ae  => HB["0F"] :: HB["93"] :: nil
  | Cond_a   => HB["0F"] :: HB["97"] :: nil
  | Cond_l   => HB["0F"] :: HB["9C"] :: nil
  | Cond_le  => HB["0F"] :: HB["9E"] :: nil
  | Cond_ge  => HB["0F"] :: HB["9D"] :: nil
  | Cond_g   => HB["0F"] :: HB["9F"] :: nil
  | Cond_p   => HB["0F"] :: HB["9A"] :: nil
  | Cond_np  => HB["0F"] :: HB["9B"] :: nil
  end.

(** Encode a single instruction *)
Definition encode_instr (ofs:Z) (i: instruction) : res (list byte) :=
  match i with
  | Pjmp_l_rel jofs =>
    OK (HB["E9"] :: encode_int32 jofs)
  | Pjcc_rel c jofs =>
    let cbytes := encode_testcond c in
    OK (cbytes ++ encode_int32 jofs)
  | Pcall_s id _ =>
    do addend <- get_instr_reloc_addend ofs i;
    OK (HB["E8"] :: encode_int32 addend)
  | Pcall_r reg _ =>
    do rm <- encode_ireg reg;
    (* reg filed must be 2 *)
    let modrm := bB[b["11"] ++ b["010"] ++ rm] in
    OK (HB["FF"] :: modrm :: nil)
  | Pleal rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8D"] :: abytes)
  | Pxorl_r rd =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    OK (HB["31"] :: modrm :: nil)
  | Paddl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["000"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["101"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["2B"] :: modrm :: nil)
  | Pmovl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let opcode := bB[b["10111"] ++ rdbits] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (opcode :: nbytes)
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits] in
    OK (HB["8B"] :: modrm :: nil)
  | Pmovl_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8B"] :: abytes)
  | Pmovl_mr a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK (HB["89"] :: abytes)
  | Pmov_rm_a rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8B"] :: abytes)    
  | Pmov_mr_a a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK (HB["89"] :: abytes)
  | Pmov_rs rd id =>
    do abytes <- encode_addrmode ofs i (Addrmode None None (inr (id,Ptrofs.zero))) rd;
    OK (HB["8B"] :: abytes)
  | Pmovsd_ff frd fr1 =>
    do bfrd <- encode_freg frd;
    do bfr1 <- encode_freg fr1;
    OK (HB["F2"] :: HB["0F"] :: HB["10"] :: bB[b["11"] ++ bfrd ++ bfr1]::nil)
  | Pmovsd_fm_a frd a
  | Pmovsd_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["F2"] :: HB["0F"] :: HB["10"] :: abytes)
  | Pmovsd_mf_a a fr1
  | Pmovsd_mf a fr1 =>
    do abytes <- encode_addrmode_f ofs i a fr1;
    OK(HB["F2"] :: HB["0F"] :: HB["11"] :: abytes)
  | Pmovss_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["F3"] :: HB["0F"] :: HB["10"] :: abytes)
  | Pmovss_mf a fr1 =>
    do abytes <- encode_addrmode_f ofs i a fr1;
    OK(HB["F3"] :: HB["0F"] :: HB["11"] :: abytes)
  | Pfldl_m a =>
    (* the rd bits must be 000 *)
    do abytes <- encode_addrmode_f ofs i a XMM0;
    OK(HB["DD"] :: abytes)
  | Pfstpl_m a =>
    (* the rd bits must be 003 *)
    do abytes <- encode_addrmode_f ofs i a XMM3;
    OK(HB["DD"] :: abytes)
  | Pflds_m a =>
    (* the rd bits must be 000 *)
    do abytes <- encode_addrmode_f ofs i a XMM0;
    OK(HB["D9"] :: abytes)
  | Pfstps_m a =>
    (* the rd bits must be 003 *)
    do abytes <- encode_addrmode_f ofs i a XMM3;
    OK(HB["D9"] :: abytes)
  (* | Pxchg_rr r1 r2 => *)
  (*   do rm <- encode_ireg r1; *)
  (*   do reg <- encode_ireg r2; *)
  (*   OK(HB["87"] :: bB[b["11"] ++ reg ++ rm] :: nil) *)
  | Pmovb_mr a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK(HB["88"] :: abytes)
  | Pmovb_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK(HB["8A"] :: abytes)                     
  | Pmovw_mr a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK(HB["66"] :: HB["89"] :: abytes)
  | Pmovw_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK(HB["66"] :: HB["8B"] :: abytes)
  | Pmovzb_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["B6"] :: modrm ::nil)
  | Pmovzb_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
      OK (HB["0F"] :: HB["B6"] :: abytes)
  | Pmovzw_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["B7"] :: modrm ::nil)
  | Pmovzw_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
      OK (HB["0F"] :: HB["B7"] :: abytes)
  | Pmovsb_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["BE"] :: modrm ::nil)
  | Pmovsb_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
      OK (HB["0F"] :: HB["BE"] :: abytes)
  | Pmovsw_rr rd rs =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg rs;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK (HB["0F"] :: HB["BF"] :: modrm ::nil)
  | Pmovsw_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["0F"] :: HB["BF"] :: abytes)
  | Pmovsq_rm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK (HB["F3"] :: HB["0F"] :: HB["7E"] :: abytes)
  | Pmovsq_mr a frs =>
    do abytes <- encode_addrmode_f ofs i a frs;
    OK (HB["66"] :: HB["0F"] :: HB["D6"] :: abytes)
  | Pcvtsd2ss_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["5A"] :: modrm ::nil)      
  | Pcvtss2sd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["5A"] :: modrm ::nil)
  | Pcvttsd2si_rf rd fr1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["2C"] :: modrm ::nil)
  | Pcvtsi2sd_fr frd r1 =>
    do reg <- encode_freg frd;
      do rm <- encode_ireg r1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F2"] :: HB["0F"] :: HB["2A"] :: modrm ::nil)
  | Pcvttss2si_rf rd fr1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_freg fr1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["2C"] :: modrm ::nil)
  | Pcvtsi2ss_fr frd r1 =>
    do reg <- encode_freg frd;
      do rm <- encode_ireg r1;
      let modrm := bB[ b["11"] ++ reg ++ rm ] in
      OK(HB["F3"] :: HB["0F"] :: HB["2A"] :: modrm ::nil)
  | Pnegl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 3 *)
      let modrm := bB[b["11"] ++ b["011"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pimull_r r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pmull_r r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pdivl r1 =>
    do rm <- encode_ireg r1;
      (* reg field must be 6 *)
      let modrm := bB[b["11"] ++ b["110"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Pandl_rr rd r1  =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["21"] :: modrm :: nil)
  | Pandl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Porl_rr rd r1 =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["09"] :: modrm :: nil)
  | Porl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 1 *)
      let modrm := bB[b["11"] ++ b["001"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pxorl_rr rd r1 =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["31"] :: modrm :: nil)
  | Pxorl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 6 *)
      let modrm := bB[b["11"] ++ b["110"] ++ rm] in
      OK(HB["81"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pnotl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 2 *)
      let modrm := bB[b["11"] ++ b["010"] ++ rm] in
      OK(HB["F7"] :: modrm :: nil)
  | Psall_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Pshrl_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Pshrl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 5 *)
      let modrm := bB[b["11"] ++ b["101"] ++ rm] in
      OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Psarl_rcl rd =>
    do rm <- encode_ireg rd;
      (* reg field must be 7 *)
      let modrm := bB[b["11"] ++ b["111"] ++ rm] in
      OK(HB["D3"] :: modrm :: nil)
  | Psarl_ri rd n =>
    do rm <- encode_ireg rd;
      (* reg field must be 7 *)
      let modrm := bB[b["11"] ++ b["111"] ++ rm] in
      OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Pshld_ri rd r1 n =>
    do reg <- encode_ireg r1;
      do rm <- encode_ireg rd;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["0F"] :: HB["A4"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Prorl_ri rd n =>
    do rm <- encode_ireg rd;
    (* reg field must be 1 *)
    let modrm := bB[b["11"] ++ b["001"] ++ rm] in
    OK(HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Prolw_ri rd n =>
    do rm <- encode_ireg rd;
    (* reg field must be 0 *)
    let modrm := bB[b["11"] ++ b["000"] ++ rm] in
    OK(HB["66"] :: HB["C1"] :: modrm :: (encode_int 1 (Int.unsigned n)))
  | Ptestl_ri r1 n =>
    do rm <- encode_ireg r1;
      (* reg field must be 0 *)
      let modrm := bB[b["11"] ++ b["000"] ++ rm] in
      OK(HB["F7"] :: modrm :: encode_int32 (Int.unsigned n))
  | Pcmov c rd r1 =>
    do reg <- encode_ireg rd;
      do rm <- encode_ireg r1;
      let cc := encode_testcond_cmov c in
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(cc ++ modrm :: nil)
  | Psetcc c rd =>
    do rm <- encode_ireg rd;
      let cc := encode_testcond_setcc c in
      (* reg field is not used *)
      let modrm := bB[b["11"] ++ b["000"] ++ rm] in
      OK(cc ++ modrm :: nil)
  | Paddd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["58"] :: modrm :: nil)
  | Padds_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["58"] :: modrm :: nil)
  | Psubd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["5C"] :: modrm :: nil)
  | Psubs_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["5C"] :: modrm :: nil)
  | Pmuld_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["59"] :: modrm :: nil)
  | Pmuls_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["59"] :: modrm :: nil)
  | Pdivd_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F2"] :: HB["0F"] :: HB["5E"] :: modrm :: nil)
  | Pdivs_ff frd fr1 =>
    do reg <- encode_freg frd;
      do rm <- encode_freg fr1;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["F3"] :: HB["0F"] :: HB["5E"] :: modrm :: nil)
  | Pnegd frd
  | Pnegs frd 
  | Pabsd frd
  | Pabss frd =>
    Error (msg "pseduo instruction Pnegd")
  | Pcomisd_ff fr1 fr2 =>
    do reg <- encode_freg fr1;
      do rm <- encode_freg fr2;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["66"] :: HB["0F"] :: HB["2F"] :: modrm :: nil)
  | Pcomiss_ff fr1 fr2 =>
    do reg <- encode_freg fr1;
      do rm <- encode_freg fr2;
      let modrm := bB[b["11"] ++ reg ++ rm] in
      OK(HB["0F"] :: HB["2F"] :: modrm :: nil)
  | Pxorpd_f frd =>
    do reg <- encode_freg frd;
    do rm <- encode_freg frd;
    let modrm := bB[b["11"] ++ reg ++ rm] in
    OK(HB["66"] :: HB["0F"] :: HB["57"] :: modrm :: nil)
  | Pxorpd_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["66"] :: HB["0F"] :: HB["57"] :: abytes)
  | Pandpd_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["66"] :: HB["0F"] :: HB["58"] :: abytes)
  | Pxorps_f frd =>
    do reg <- encode_freg frd;
    do rm <- encode_freg frd;
    let modrm := bB[b["11"] ++ reg ++ rm] in
    OK(HB["0F"] :: HB["57"] :: modrm :: nil)
  | Pxorps_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["0F"] :: HB["57"] :: abytes)
  | Pandps_fm frd a =>
    do abytes <- encode_addrmode_f ofs i a frd;
    OK(HB["0F"] :: HB["58"] :: abytes)
  | Pjmp_s id sg =>
    do addend <- get_instr_reloc_addend ofs i;
      OK (HB["E9"] :: encode_int32 addend)
  | Pjmp_r reg sg =>
    do rm <- encode_ireg reg;
    (* reg field must be 4 *)
      let modrm := bB[b["11"] ++ b["100"] ++ rm] in
      OK(HB["FF"] :: modrm :: nil)
  | Pjmp_m a =>
    do abytes <- encode_addrmode ofs i a RSP;
    OK(HB["FF"] :: abytes)
  | Ptestl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["85"] :: modrm :: nil)
  | Pret =>
    OK (HB["C3"] :: nil)
  | Pret_iw n =>
    let nbytes := encode_int16 (Int.unsigned n) in
    OK (HB["C2"] :: nbytes)
  | Pimull_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["0F"] :: HB["AF"] :: modrm :: nil)
  | Pimull_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["69"] :: modrm :: nbytes)
  | Pcmpl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["39"] :: modrm :: nil)
  | Pcmpl_ri r1 n =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Pcltd =>
    OK (HB["99"] :: nil)
  | Pidivl r1 =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
    OK (HB["F7"] :: modrm :: nil)
  | Psall_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["100"] ++ rdbits ] in
    let nbytes := [Byte.repr (Int.unsigned n)] in
    OK (HB["C1"] :: modrm :: nbytes)
  | Paddl_rr rd r2 =>
    do rdbits <- encode_ireg rd;
    do r2bits <- encode_ireg r2;
    let modrm := bB[b["11"] ++ r2bits ++ rdbits] in
    OK (HB["01"] :: modrm :: nil)
  | Padcl_rr rd r2 =>
    do rdbits <- encode_ireg rd;
    do r2bits <- encode_ireg r2;
    let modrm := bB[b["11"] ++ r2bits ++ rdbits] in
    OK (HB["11"] :: modrm :: nil)
  | Padcl_ri rd n =>
    do rdbits <- encode_ireg rd;
    (* Mod:11 -> R/M:010 -> RD:010 *)
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    let nbytes := [Byte.repr (Int.unsigned n)] in
    OK (HB["83"] :: modrm :: nbytes)
  | Psbbl_rr rd r2 =>
    do rdbits <- encode_ireg rd;
    do r2bits <- encode_ireg r2;
    let modrm := bB[b["11"] ++ r2bits ++ rdbits] in
    OK (HB["19"] :: modrm :: nil)
  | Prep_movsl =>
    OK (HB["F3"] :: HB["A5"] :: nil)
  | Plabel _
  | Pnop =>
    OK (HB["90"] :: nil)
  | Pbswap32 rd =>
    do rdbits <- encode_ireg rd;
    let tmp := bB[b["11001"] ++ rdbits] in
    OK (HB["0F"] :: tmp :: nil)
  | Pbsfl rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[b["11"] ++ rdbits ++ r1bits] in
    OK (HB["0F"] :: HB["BC"] :: modrm :: nil)          
  | Pbsrl rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[b["11"] ++ rdbits ++ r1bits] in
    OK (HB["0F"] :: HB["BD"] :: modrm :: nil)
  | Psqrtsd frd fr1 =>
    do rdbits <- encode_freg frd;
    do r1bits <- encode_freg fr1;
    let modrm := bB[b["11"] ++ rdbits ++ r1bits] in
    OK (HB["F2"] :: HB["0F"] :: HB["51"] :: modrm :: nil)
  | Pmaxsd frd fr2 =>
    do rdbits <- encode_freg frd;
    do r2bits <- encode_freg fr2;
    let modrm := bB[b["11"] ++ rdbits ++ r2bits] in
    OK (HB["F2"] :: HB["0F"] :: HB["5F"] :: modrm :: nil)
  | Pminsd frd fr2 =>
    do rdbits <- encode_freg frd;
    do r2bits <- encode_freg fr2;
    let modrm := bB[b["11"] ++ rdbits ++ r2bits] in
    OK (HB["F2"] :: HB["0F"] :: HB["5D"] :: modrm :: nil)
  | Pbuiltin ef args res =>
    match ef with
    | EF_annot _ name _ =>
      Error [MSG "Unsupported annot ef "; MSG (name)]
    | EF_debug _ _ _ =>
      Error [MSG "Unsupported debug info "]
    | EF_inline_asm name _ _ =>
      Error [MSG "Unsupported inline asm "; MSG (name)]
    | EF_builtin name _  =>
      Error [MSG "Unsupported builtins "; MSG (name)]
    | _ => Error [MSG "Encoding of the builins is not supported yet"]
    end
  | _ =>
    Error [MSG "Encoding of the instruction is not supported yet: ";
           MSG (instr_to_string i)]
  end.

Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

Definition concat_byte (acc: res (list byte)) i :=
  do code <- acc;
  do c <- EncDecRet.encode_Instruction i;
  OK (code ++ c).

Definition encode_instruction (ofs: Z) (i: instruction) :res (list byte) :=
  do c1 <- translate_instr rtbl_ofs_map ofs i;
  do c <- fold_left concat_byte c1 (OK []);
  OK c.

(* use generated encoder*)
Definition acc_instrs r i := 
  do r' <- r;
  let '(ofs, code) := r' in
  do c <- encode_instruction ofs i;
  (** check instr_size eqaul to encoded instuction size *)
  if Z.eqb (Z.of_nat (length c)) (instr_size i) then
    OK (ofs + instr_size i, code ++ c)
  else
    Error [MSG "Inconsistent instruction size for: ";
          MSG (instr_to_string i)].

(** Translation of a sequence of instructions in a function *)
Definition transl_code (c:code) : res (list byte) :=
  do r <- fold_left acc_instrs c (OK (0, []));
  let '(_, c') := r in
  OK c'.                                                           

End INSTR_SIZE.

(** ** Encoding of data *)

Definition transl_init_data (dofs:Z) (d:init_data) : res (list byte) :=
  match d with
  | Init_int8 i => OK [Byte.repr (Int.unsigned i)]
  | Init_int16 i => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f => OK (encode_int 4 (Int.unsigned (Float32.to_bits f)))
  | Init_float64 f => OK (encode_int 8 (Int64.unsigned (Float.to_bits f)))
  | Init_space n => OK (zero_bytes (Z.to_nat n))
  | Init_addrof id ofs => 
    do addend <- get_reloc_addend dofs;
    if Archi.ptr64 then
      OK (encode_int64 addend)
    else
      OK (encode_int32 addend)
  end.

Definition acc_init_data r d := 
  do r' <- r;
  let '(ofs, rbytes) := r' in
  do dbytes <- transl_init_data ofs d;
  OK (ofs + init_data_size d, rev dbytes ++ rbytes).

Definition transl_init_data_list (l: list init_data) : res (list byte) :=
  do r <- fold_left acc_init_data l (OK (0, []));
  let '(_,bytes) := r in
  OK (rev bytes).

End WITH_RELOC_OFS_MAP.


Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

(** ** Translation of a program *)
Definition transl_section (sec : section) (reloctbl: reloctable) : res section :=
  match sec with
  | sec_text code =>
    do codebytes <- transl_code (gen_reloc_ofs_map reloctbl) instr_size code;
    OK (sec_bytes codebytes)
  | sec_data dl =>
    do databytes <- transl_init_data_list (gen_reloc_ofs_map reloctbl) dl;
    OK (sec_bytes databytes)
  (* | sec_rodata rdl => *)
  (*   do rodatabytes <- transl_init_data_list (gen_reloc_ofs_map reloctbl) rdl; *)
  (*   OK (sec_bytes rodatabytes) *)
  | _ => Error (msg "There are bytes before binary generation")
  end.


Definition acc_fold_section (reloc_map : reloctable_map) (res_sectbl: res sectable) (id: ident) (sec: section) :=
  do sectbl <- res_sectbl;
  let reloc_tbl := 
      match reloc_map ! id with
      | Some t => t
      | None => []
      end in
  do sec' <- transl_section sec reloc_tbl;
  OK (PTree.set id sec' sectbl).
        
Definition transl_sectable (stbl: sectable) (relocmap: reloctable_map) :=
  PTree.fold (acc_fold_section relocmap) stbl (OK (PTree.empty section)).


Definition transf_program (p:program) : res program := 
  do stbl <- transl_sectable (prog_sectable p) (prog_reloctables p);
  do szstrings <- fold_right
                    (fun (id : ident) (acc : res Z) =>
                       match acc with
                       | OK z =>
                         match SymbolString.find_symbol_pos id with
                         | Some pos => OK (z + 2 + Z.of_nat (length pos))
                         | None => Error (msg "cannot find string")
                         end
                       | Error _ => acc
                       end) (OK 0) (map fst (PTree.elements (prog_symbtable p)));
  if zlt szstrings Int.max_unsigned
  then 
  OK {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := stbl;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p;
     |}
  else Error (msg "Too many strings in symbtable").

End INSTR_SIZE.
