Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import BPProperty.
Require Import EncDecRet BPProperty.
Require Import TranslateInstr.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* Decode;instruction *)

Definition decode_instr' (I: Instruction) : res instruction :=
  match I with
  | jal rdbits J1 J2 J3 J4 =>
    do rd <- decode_ireg0 rdbits;
    do ofs <- decode_immJ J1 J2 J3 J4;
    OK (Pjal_ofs rd (inr ofs))
  | jalr rdbits rsbits imm =>
    do rd <- decode_ireg0 rdbits;
    do rs <- decode_ireg rsbits;
    do ofs <- decode_ofs_u12 imm;
    OK (Pjal_rr rd rs ofs)
  | auipc rdbits imm20 =>
    do rd <- decode_ireg rdbits;
    do ofs <- decode_ofs_u20_unsigned imm20;
    OK (Pauipc rd (inr ofs))
  
  | addiw rdbits rsbits imm12 =>
      if builtin_eq_dec (proj1_sig rdbits) (list_repeat 5 false) then
        OK Pnop
      else
        if Archi.ptr64 then
          do rd <- decode_ireg rdbits;
          do rs <- decode_ireg0 rsbits;
          do imm_Z <- decode_ofs_u12 imm12;
          let imm := Int.repr imm_Z in
          OK (Paddiw rd rs imm)
        else Error [MSG "Only in rv64"]
  | addi rdbits rsbits imm12 =>
      if builtin_eq_dec (proj1_sig rdbits) (list_repeat 5 false) then
        OK Pnop
      else
        do rd <- decode_ireg rdbits;
        do rs <- decode_ireg0 rsbits;
        do imm_Z <- decode_ofs_u12 imm12;
        if Archi.ptr64 then
          let imm := Int64.repr imm_Z in
          OK (Paddil rd rs imm)
        else
          let imm := Int.repr imm_Z in
          OK (Paddiw rd rs imm)
  | slti rdbits rsbits imm12 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_ofs_u12 imm12;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Psltil rd rs imm)
    else
      let imm := Int.repr imm_Z in
      OK (Psltiw rd rs imm)
  | sltiu rdbits rsbits imm12 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_ofs_u12 imm12;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Psltiul rd rs imm)
    else
      let imm := Int.repr imm_Z in
      OK (Psltiuw rd rs imm)
  | andi rdbits rsbits imm12 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_ofs_u12 imm12;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Pandil rd rs imm)
    else
      let imm := Int.repr imm_Z in
      OK (Pandiw rd rs imm)
  | ori rdbits rsbits imm12 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_ofs_u12 imm12;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Poril rd rs imm)
    else
      let imm := Int.repr imm_Z in
      OK (Poriw rd rs imm)
  | xori rdbits rsbits imm12 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_ofs_u12 imm12;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Pxoril rd rs imm)
    else
      let imm := Int.repr imm_Z in
      OK (Pxoriw rd rs imm)
  | slliw rdbits rsbits imm5 =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs <- decode_ireg0 rsbits;
      do imm_Z <- decode_ofs_u5 imm5;
      let imm := Int.repr imm_Z in
      OK (Pslliw rd rs imm)
    else Error [MSG "Only in rv64"]
  | slli rdbits rsbits imm6 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_shamt imm6;
    let imm := Int.repr imm_Z in
    if Archi.ptr64 then
      OK (Psllil rd rs imm)
    else
      OK (Pslliw rd rs imm)
  | srliw rdbits rsbits imm5 =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs <- decode_ireg0 rsbits;
      do imm_Z <- decode_ofs_u5 imm5;
      let imm := Int.repr imm_Z in
      OK (Psrliw rd rs imm)
    else Error [MSG "Only in rv64"]
  | srli rdbits rsbits imm6 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_shamt imm6;
    let imm := Int.repr imm_Z in
    if Archi.ptr64 then
      OK (Psrlil rd rs imm)
    else
      OK (Psrliw rd rs imm)
  | sraiw rdbits rsbits imm5 =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs <- decode_ireg0 rsbits;
      do imm_Z <- decode_ofs_u5 imm5;
      let imm := Int.repr imm_Z in
      OK (Psraiw rd rs imm)
    else Error [MSG "Only in rv64"]
  | srai rdbits rsbits imm6 =>
    do rd <- decode_ireg rdbits;
    do rs <- decode_ireg0 rsbits;
    do imm_Z <- decode_shamt imm6;
    let imm := Int.repr imm_Z in
    if Archi.ptr64 then
      OK (Psrail rd rs imm)
    else
      OK (Psraiw rd rs imm)
  | lui rdbits imm20 =>
    do rd <- decode_ireg rdbits;
    do imm_Z <- decode_ofs_u20_unsigned imm20;
    if Archi.ptr64 then
      let imm := Int64.repr imm_Z in
      OK (Pluil rd imm)
    else
      let imm := Int.repr imm_Z in
      OK (Pluiw rd imm)

  | addw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Paddw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | add rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Paddl rd rs1 rs2)
    else
      OK (Paddw rd rs1 rs2)
  | subw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Psubw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | sub rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Psubl rd rs1 rs2)
    else
      OK (Psubw rd rs1 rs2)
  | mulw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Pmulw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | mul rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pmull rd rs1 rs2)
    else
      OK (Pmulw rd rs1 rs2)
  | mulh rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pmulhl rd rs1 rs2)
    else
      OK (Pmulhw rd rs1 rs2)
  | mulhu rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pmulhul rd rs1 rs2)
    else
      OK (Pmulhuw rd rs1 rs2)
  | divw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Pdivw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | div rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pdivl rd rs1 rs2)
    else
      OK (Pdivw rd rs1 rs2)
  | divuw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Pdivuw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | divu rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pdivul rd rs1 rs2)
    else
      OK (Pdivuw rd rs1 rs2)
  | remw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Premw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | rem rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Preml rd rs1 rs2)
    else
      OK (Premw rd rs1 rs2)
  | remuw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Premuw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | remu rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Premul rd rs1 rs2)
    else
      OK (Premuw rd rs1 rs2)
  | slt rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Psltl rd rs1 rs2)
    else
      OK (Psltw rd rs1 rs2)
  | sltu rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Psltul rd rs1 rs2)
    else
      OK (Psltuw rd rs1 rs2)
  | and rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pandl rd rs1 rs2)
    else
      OK (Pandw rd rs1 rs2)
  | or rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Porl rd rs1 rs2)
    else
      OK (Porw rd rs1 rs2)
  | xor rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pxorl rd rs1 rs2)
    else
      OK (Pxorw rd rs1 rs2)
  | sllw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Psllw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | sll rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Pslll rd rs1 rs2)
    else
      OK (Psllw rd rs1 rs2)
  | srlw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Psrlw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | srl rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Psrll rd rs1 rs2)
    else
      OK (Psrlw rd rs1 rs2)
  | sraw rdbits rs1bits rs2bits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do rs1 <- decode_ireg0 rs1bits;
      do rs2 <- decode_ireg0 rs2bits;
      OK (Psraw rd rs1 rs2)
    else Error [MSG "Only in rv64"]
  | sra rdbits rs1bits rs2bits =>
    do rd <- decode_ireg rdbits;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    if Archi.ptr64 then
      OK (Psral rd rs1 rs2)
    else
      OK (Psraw rd rs1 rs2)
  | beq B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pbeq_ofs rs1 rs2 ofs)
  | bne B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pbne_ofs rs1 rs2 ofs)
  | blt B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pblt_ofs rs1 rs2 ofs)
  | bltu B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pbltu_ofs rs1 rs2 ofs)
  | bge B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pbge_ofs rs1 rs2 ofs)
  | bgeu B1 B2 rs1bits rs2bits B3 B4 =>
    do ofs <- decode_immB B1 B2 B3 B4;
    do rs1 <- decode_ireg0 rs1bits;
    do rs2 <- decode_ireg0 rs2bits;
    OK (Pbgeu_ofs rs1 rs2 ofs)
  
  | lb rdbits rabits ofsbits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do ofs_Z <- decode_ofs_u12 ofsbits;
    do ofs <- Z_to_ofs ofs_Z;
    OK (Plb rd ra ofs)
  | lbu rdbits rabits ofsbits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do ofs_Z <- decode_ofs_u12 ofsbits;
    do ofs <- Z_to_ofs ofs_Z;
    OK (Plbu rd ra ofs)
  | lh rdbits rabits ofsbits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do ofs_Z <- decode_ofs_u12 ofsbits;
    do ofs <- Z_to_ofs ofs_Z;
    OK (Plh rd ra ofs)
  | lhu rdbits rabits ofsbits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do ofs_Z <- decode_ofs_u12 ofsbits;
    do ofs <- Z_to_ofs ofs_Z;
    OK (Plhu rd ra ofs)
  | lw rdbits rabits ofsbits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do ofs_Z <- decode_ofs_u12 ofsbits;
    do ofs <- Z_to_ofs ofs_Z;
    OK (Plw rd ra ofs)
  | ld rdbits rabits ofsbits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do ra <- decode_ireg rabits;
      do ofs_Z <- decode_ofs_u12 ofsbits;
      do ofs <- Z_to_ofs ofs_Z;
      OK (Pld rd ra ofs)
    else Error [MSG "Only in rv64"]

  | sb immS1bits rabits rdbits immS2bits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Psb rd ra ofs)
  | sh immS1bits rabits rdbits immS2bits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Psh rd ra ofs)
  | sw immS1bits rabits rdbits immS2bits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Psw rd ra ofs)
  | sd immS1bits rabits rdbits immS2bits =>
    do rd <- decode_ireg rdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Psd rd ra ofs)

  | fsgnjd fdbits fs1bits _ =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fs1bits;
    OK (Pfmv fd fs)
  | fmvxw rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfmvxs rd fs)
  | fmvwx fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg rsbits;
    OK (Pfmvsx fd rs)
  | fmvxd rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfmvxd rd fs)
  | fmvdx fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg rsbits;
    OK (Pfmvdx fd rs)

  | flw fdbits rabits immbits =>
    do fd <- decode_freg fdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_ofs_u12 immbits;
    do ofs <- Z_to_ofs imm;
    OK (Pfls fd ra ofs)
  | fsw immS1bits rabits fsbits immS2bits =>
    do fs <- decode_freg fsbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Pfss fs ra ofs)
  | fsgnjns fdbits fsbits _ =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfnegs fd fs)
  | fsgnjxs fdbits fsbits _ =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfabss fd fs)
  | fadds fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfadds fd fs1 fs2)
  | fsubs fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfsubs fd fs1 fs2)
  | fmuls fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmuls fd fs1 fs2)
  | fdivs fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfdivs fd fs1 fs2)
  | fmins fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmins fd fs1 fs2)
  | fmaxs fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmaxs fd fs1 fs2)
  | feqs rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfeqs rd fs1 fs2)
  | flts rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pflts rd fs1 fs2)
  | fles rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfles rd fs1 fs2)
  | fsqrts fdbits fsbits =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfsqrts fd fs)
  | fmadds fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfmadds fd fs1 fs2 fs3)
  | fmsubs fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfmsubs fd fs1 fs2 fs3)
  | fnmadds fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfnmadds fd fs1 fs2 fs3)
  | fnmsubs fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfnmsubs fd fs1 fs2 fs3)
  | fcvtws rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfcvtws rd fs)
  | fcvtwus rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfcvtwus rd fs)
  | fcvtsw fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg0 rsbits;
    OK (Pfcvtsw fd rs)
  | fcvtswu fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg0 rsbits;
    OK (Pfcvtswu fd rs)

  | fcvtls rdbits fsbits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do fs <- decode_freg fsbits;
      OK (Pfcvtls rd fs)
    else Error [MSG "Only in rv64"]
  | fcvtlus rdbits fsbits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do fs <- decode_freg fsbits;
      OK (Pfcvtlus rd fs)
    else Error [MSG "Only in rv64"]
  | fcvtsl fdbits rsbits =>
    if Archi.ptr64 then
      do fd <- decode_freg fdbits;
      do rs <- decode_ireg0 rsbits;
      OK (Pfcvtsl fd rs)
    else Error [MSG "Only in rv64"]
  | fcvtslu fdbits rsbits =>
    if Archi.ptr64 then
      do fd <- decode_freg fdbits;
      do rs <- decode_ireg0 rsbits;
      OK (Pfcvtslu fd rs)
    else Error [MSG "Only in rv64"]

  | fload fdbits rabits immbits =>
    do fd <- decode_freg fdbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_ofs_u12 immbits;
    do ofs <- Z_to_ofs imm;
    OK (Pfld fd ra ofs)
  | fsd immS1bits rabits fsbits immS2bits =>
    do fs <- decode_freg fsbits;
    do ra <- decode_ireg rabits;
    do imm <- decode_immS immS1bits immS2bits;
    do ofs <- Z_to_ofs imm;
    OK (Pfsd fs ra ofs)
  | fsgnjnd fdbits fsbits _ =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfnegd fd fs)
  | fsgnjxd fdbits fsbits _ =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfabsd fd fs)
  | faddd fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfaddd fd fs1 fs2)
  | fsubd fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfsubd fd fs1 fs2)
  | fmuld fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmuld fd fs1 fs2)
  | fdivd fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfdivd fd fs1 fs2)
  | fmind fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmind fd fs1 fs2)
  | fmaxd fdbits fs1bits fs2bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfmaxd fd fs1 fs2)
  | feqd rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfeqd rd fs1 fs2)
  | fltd rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfltd rd fs1 fs2)
  | fled rdbits fs1bits fs2bits =>
    do rd <- decode_ireg rdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    OK (Pfled rd fs1 fs2)
  | fsqrtd fdbits fsbits =>
    do fd <- decode_freg fdbits;
    do fs <- decode_freg fsbits;
    OK (Pfsqrtd fd fs)
  | fmaddd fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfmaddd fd fs1 fs2 fs3)
  | fmsubd fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfmsubd fd fs1 fs2 fs3)
  | fnmaddd fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfnmaddd fd fs1 fs2 fs3)
  | fnmsubd fdbits fs1bits fs2bits fs3bits =>
    do fd <- decode_freg fdbits;
    do fs1 <- decode_freg fs1bits;
    do fs2 <- decode_freg fs2bits;
    do fs3 <- decode_freg fs3bits;
    OK (Pfnmsubd fd fs1 fs2 fs3)
  | fcvtwd rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfcvtwd rd fs)
  | fcvtwud rdbits fsbits =>
    do rd <- decode_ireg rdbits;
    do fs <- decode_freg fsbits;
    OK (Pfcvtwud rd fs)
  | fcvtdw fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg0 rsbits;
    OK (Pfcvtdw fd rs)
  | fcvtdwu fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_ireg0 rsbits;
    OK (Pfcvtdwu fd rs)

  | fcvtld rdbits fsbits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do fs <- decode_freg fsbits;
      OK (Pfcvtld rd fs)
    else Error [MSG "Only in rv64"]
  | fcvtlud rdbits fsbits =>
    if Archi.ptr64 then
      do rd <- decode_ireg rdbits;
      do fs <- decode_freg fsbits;
      OK (Pfcvtlud rd fs)
    else Error [MSG "Only in rv64"]
  | fcvtdl fdbits rsbits =>
    if Archi.ptr64 then
      do fd <- decode_freg fdbits;
      do rs <- decode_ireg0 rsbits;
      OK (Pfcvtdl fd rs)
    else Error [MSG "Only in rv64"]
  | fcvtdlu fdbits rsbits =>
    if Archi.ptr64 then
      do fd <- decode_freg fdbits;
      do rs <- decode_ireg0 rsbits;
      OK (Pfcvtdlu fd rs)
    else Error [MSG "Only in rv64"]
  
  | fcvtds fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_freg rsbits;
    OK (Pfcvtds fd rs)
  | fcvtsd fdbits rsbits =>
    do fd <- decode_freg fdbits;
    do rs <- decode_freg rsbits;
    OK (Pfcvtsd fd rs)

  (* | _ => Error [MSG "Not exists or unsupported"] *)
  end.

Ltac solve_preparation H :=
  try (destruct Archi.ptr64 eqn:E;
  monadInv H; unfold decode_instr'; try (rewrite E));
  try (monadInv H; unfold decode_instr').

Ltac solve_Itype_instr H :=
  solve_preparation H;
  try (repeat (erewrite encode_ireg_consistency; eauto));
  try (erewrite encode_ireg0_consistency; eauto);
  try (repeat (erewrite encode_freg_consistency; eauto));
  erewrite encode_ofs_u12_consistency; eauto; simpl;
  try (erewrite encode_ofs_consistency; eauto); simpl;
  try (rewrite Int.repr_signed);
  try (rewrite Int64.repr_signed);
  reflexivity.

Ltac solve_Itype_instr_shamt H :=
  solve_preparation H;
  erewrite encode_ireg_consistency; eauto;
  erewrite encode_ireg0_consistency; eauto;
  try (erewrite encode_ofs_u5_consistency; eauto);
  try (erewrite encode_shamt_consistency; eauto);
  simpl; rewrite Int.repr_unsigned; reflexivity.

Ltac solve_Utype_instr H :=
  solve_preparation H;
  erewrite encode_ireg_consistency; eauto;
  erewrite encode_ofs_u20_unsigned_consistency; eauto;
  simpl; try (rewrite Int.repr_signed);
  try (rewrite Int64.repr_signed);
  reflexivity.

Ltac solve_Rtype_instr H :=
  solve_preparation H;
  try (erewrite encode_ireg_consistency; eauto;
  repeat (erewrite encode_ireg0_consistency; eauto));
  try (repeat (erewrite encode_freg_consistency; eauto));
  simpl; reflexivity.

Ltac solve_Stype_instr H :=
  solve_preparation H;
  try (repeat (erewrite encode_ireg_consistency; eauto));
  try (repeat (erewrite encode_freg_consistency; eauto));
  erewrite encode_immS_consistency; eauto; simpl;
  erewrite encode_ofs_consistency; eauto; simpl; reflexivity.

Ltac solve_Btype_instr H :=
  solve_preparation H;
  erewrite encode_immB_consistency; eauto;
  repeat (erewrite encode_ireg0_consistency; eauto); simpl;
  reflexivity.

Ltac solve_fcvt H :=
  solve_preparation H;
  try (repeat (erewrite encode_freg_consistency; eauto));
  try (repeat (erewrite encode_ireg0_consistency; eauto));
  try (repeat (erewrite encode_ireg_consistency; eauto)); simpl;
  reflexivity.

Theorem translate_instr_consistency_aux :
  forall i I,
  translate_instr' i = OK I ->
  decode_instr' I = OK i.
Proof.
  intros i I H.
  unfold translate_instr' in H.
  destruct i;
  try solve_Itype_instr H;
  try solve_Itype_instr_shamt H;
  try solve_Utype_instr H;
  try solve_Rtype_instr H;
  try solve_Stype_instr H;
  try solve_fcvt H;
  try solve_Btype_instr H.

  (* addiw *)
  monadInv H. destruct Archi.ptr64 eqn:PTR.
  inv EQ3. simpl. destr.
  destruct rd;simpl in EQ;inv EQ;unfold char_to_bool in *;simpl in e;try congruence.
  rewrite PTR.
  solve_Itype_instr H.
  inv EQ3. simpl. destr.
  destruct rd;simpl in EQ;inv EQ;unfold char_to_bool in *;simpl in e;try congruence.
  rewrite PTR.
  solve_Itype_instr H.

  (* addil *)
  destruct Archi.ptr64 eqn:PTR. monadInv H.
  simpl. destr.
  destruct rd;simpl in EQ;inv EQ;unfold char_to_bool in *;simpl in e;try congruence.
  rewrite PTR.
  solve_Itype_instr H.
  monadInv H.

  destruct Archi.ptr64 eqn:PTR;monadInv H;simpl;auto.
  
  (* auipc *)
  - destruct imm; solve_preparation H;
  erewrite encode_ireg_consistency; eauto;
  erewrite encode_ofs_u20_unsigned_consistency; eauto; simpl;
  reflexivity.

  (* jal *)
  - destruct ofs; solve_preparation H;
    erewrite encode_ireg0_consistency; eauto;
    erewrite encode_immJ_consistency; eauto; simpl;
    reflexivity.
Qed.


Definition decode_instr l :=
  match l with
  | i :: l' =>
      do i' <- decode_instr' i;
      OK (i', l')
  | _ => Error (msg "impossible")
  end.

Theorem translate_instr_consistency: forall i li l,
    translate_instr i = OK li ->
    decode_instr (li++l) = OK (i,l).
Proof.
  unfold translate_instr,decode_instr.
  intros. monadInv H. simpl.
  erewrite translate_instr_consistency_aux;eauto. simpl. auto.
Qed.
