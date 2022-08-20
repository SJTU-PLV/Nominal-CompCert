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


Program Definition encode_ofs_u8 (ofs:Z) :res u8 :=
  if ( -1 <? ofs) && (ofs <? (two_power_nat 8)) then
    let ofs8 := bytes_to_bits_opt (bytes_of_int 1 ofs) in
    if assertLength ofs8 8 then
      OK (exist _ ofs8 _)
    else Error (msg "impossible")
  else Error (msg "Offset overflow in encode_ofs_u8").


Definition decode_ofs_u8 (bs:u8) : int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  Int.repr z.

Program Definition encode_ofs_u16 (ofs:Z) :res u16 :=
  (* We input Int.intval to this function, so range checking is nessary *)
  if ( -1 <? ofs) && (ofs <? (two_power_nat 16)) then
    let ofs16 := bytes_to_bits_opt (bytes_of_int 2 ofs) in
    if assertLength ofs16 16 then
    OK (exist _ ofs16 _)
    else Error (msg "impossible in encode_ofs_u16")
  else Error (msg "Offset overflow in encode_ofs_u16").

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

Definition encode_ofs_signed32 (ofs:Z) :=
  if (Int.min_signed <=? ofs) && (ofs <=? Int.max_signed) then
    encode_ofs_u32 (Int.intval (Int.repr ofs))
  else
    Error (msg "Offset overflow in encode_ofs_signed32").

Definition decode_ofs_signed32 (bs:u32) : Z :=
  let i := decode_ofs_u32 bs in
  Int.signed i.

  
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



  
(* Section WITH_RELOC_OFS_MAP. *)

(* Variable rtbl_ofs_map: reloc_ofs_map_type. *)


(* Definition get_reloc_addend (ofs:Z) : res Z := *)
(*   match ZTree.get ofs rtbl_ofs_map with *)
(*   | None => Error [MSG "Cannot find the relocation entry at the offset "; POS (Z.to_pos ofs)] *)
(*   | Some e => OK (reloc_addend e) *)
(*   end. *)

(* Definition get_instr_reloc_addend (ofs:Z) (i:instruction) : res Z := *)
(*   do iofs <- instr_reloc_offset i; *)
(*   get_reloc_addend (ofs + iofs). *)


(* Definition get_instr_reloc_addend' (ofs:Z): res Z := *)
(*   get_reloc_addend ofs. *)

Definition get_reloc_addend (e: option relocentry) :=
  match e with
  | Some e' =>
    OK (reloc_addend e')
  | _ => Error (msg "get reloc addend error")
  end.



Definition translate_Addrmode_AddrE_aux32 (obase: option ireg) (oindex: option (ireg*Z)) (ofs32:u32) : res AddrE :=
  match obase,oindex with
  | None,None =>
    if Archi.ptr64 then
      do rsp <- encode_ireg_u3 RSP;
    (* do not use rip-relative addressing *)
    OK (AddrE11 ofs32)
    (* OK (AddrE9 zero2 rsp ofs32) *)
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
Definition translate_Addrmode_AddrE (e: option relocentry) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        (* do addend <- get_reloc_addend e; *)
        if (Ptrofs.unsigned ofs <? Int.modulus) then
          (* if Z.eqb (Ptrofs.unsigned ofs) addend then *)
            (*32bit mode the addend placed in instruction *)
            do imm32 <- encode_ofs_u32 (Ptrofs.unsigned ofs);
            translate_Addrmode_AddrE_aux32 obase oindex imm32
          (* else Error (msg "addend is not equal to ofs") *)
        else Error (msg "Addrmode32: Out range of unsigned 32bit displacement")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      match e with
      | None =>
          do ofs32 <- encode_ofs_signed32 ofs;
          translate_Addrmode_AddrE_aux32 obase oindex ofs32            
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
      (* use rip-relative addressing *)
      OK (AddrE11 ofs32,zero1,zero1)
      (* OK ((AddrE9 zero2 rsp ofs32),zero1,zero1) *)
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
Definition translate_Addrmode_AddrE64 (e: option relocentry) (addr:addrmode): res (AddrE*u1*u1) :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        (* do addend <- get_reloc_addend e; *)
        if (Ptrofs.unsigned ofs <? Int.modulus) then
          (* addend is the offset of id and access point *)
          (* if Z.eqb (Ptrofs.unsigned ofs) addend then *)
            do imm32 <- encode_ofs_u32 (Ptrofs.unsigned ofs);
            translate_Addrmode_AddrE_aux64 obase oindex imm32
          (* else Error (msg "64bit: addend is not equal to ofs") *)
        else Error (msg "Addrmode64: Out range of unsigned 32bit displacement")                                        
      | _ => Error(msg "64bit: id must be 1")
      end
    | inl ofs =>
      match e with
      | None =>         
          do ofs32 <- encode_ofs_signed32 ofs;
          translate_Addrmode_AddrE_aux64 obase oindex ofs32
      | _ => Error (msg "64bit: impossible relocation entry in addrmode")
      end
    end
  end.



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


Definition encode_rex_prefix_addr (e: option relocentry) (addr: addrmode) : res (list Instruction * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE e in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 e in
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

Definition encode_rex_prefix_ra (e: option relocentry) (r: ireg) (addr: addrmode) : res (list Instruction * u3 * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE e in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 e in
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


Definition encode_rex_prefix_fa (e:option relocentry) (r: freg) (addr: addrmode) : res (list Instruction * u3 * AddrE) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE e in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 e in
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
Definition translate_instr (e: option relocentry) (i:instruction) : res (list Instruction) :=
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE e in
  let translate_Addrmode_AddrE64 := translate_Addrmode_AddrE64 e in
  let encode_rex_prefix_ra := encode_rex_prefix_ra e in
  let encode_rex_prefix_fa := encode_rex_prefix_fa e in
  let encode_rex_prefix_addr := encode_rex_prefix_addr e in
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
    match e with
    | None =>
        do imm <- encode_ofs_signed32 ofs;
        OK [Pjmp_l_rel imm]
    | _ => Error[MSG"Relocation entry in Pjmp_l_rel not expected"; MSG(Z_to_hex_string 4 ofs)]
    end
  | Asm.Pjmp_s id _ =>
    if Pos.eqb id xH then
      (* do addend <- get_reloc_addend e; *)
      (* do imm32 <- encode_ofs_u32 addend; *)
      if Archi.ptr64 then 
        OK [Pjmp_l_rel zero32]
      else
        do imm32 <- encode_ofs_u32 (-4);
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
      (* do addend <- get_reloc_addend e; *)
      (* do imm32 <- encode_ofs_u32 addend; *)
      if Archi.ptr64 then 
        OK [Pcall_ofs zero32]
      else
        do imm32 <- encode_ofs_u32 (-4);
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
    do imm <- encode_ofs_signed32 ofs;
    OK [Pjcc_rel cond imm]
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
    (* do Rrdbits <- encode_ireg_u4 rd; *)
    (* let (R,rdbits) := Rrdbits in *)
    (* use R to extend register instead of B *)
    (* OK ([REX_WRXB zero1 R zero1 zero1; Pbswap32 rdbits]) *)
    do rex_r <- encode_rex_prefix_r rd;
    let (orex, rdbits) := rex_r in
    OK (orex ++ [Pbswap32 rdbits])
  | Asm.Pbswap64 rd =>
    do Brdbits <- encode_ireg_u4 rd;
    let (B,rdbits) := Brdbits in
    OK ([REX_WRXB one1 zero1 zero1 B; Pbswap32 rdbits])
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
    OK ([REPNZ] ++ orex ++ [Pmovss_d_fm a rdbits])
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

