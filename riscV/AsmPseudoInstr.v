Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition transf_offset (ofs:offset) : offset :=
  match ofs with
  | Ofslow id ofs =>
      let lo := Ptrofs.sign_ext 12 ofs in
      Ofslow id lo
  | _ => ofs
  end.

Definition transf_instr i : (list instruction) :=
  match i with
  | Ploadsymbol_high rd id ofs =>
      let lo := Ptrofs.sign_ext 12 ofs in
      let hi := Ptrofs.shru (Ptrofs.sub ofs lo) (Ptrofs.repr 12) in
      [Plui_s rd id (Ptrofs.unsigned hi)]
  | Ploadsymbol rd id ofs =>
      (* not consider :  Archi.pic_code *)
      (* I think it is necessary to check the 20-bit bounds for ofs when generating reocation entry for Plui_s *)
      (* We expand Ploadsymbol here because the id_eliminate in assembler is one to one *)
      let lo := Ptrofs.sign_ext 12 ofs in
      let hi := Ptrofs.shru (Ptrofs.sub ofs lo) (Ptrofs.repr 12) in
      [Plui_s rd id (Ptrofs.unsigned hi); Paddi_s rd rd id (Ptrofs.signed lo)]
        
  (* transform pseudo jump instruction *)
  | Pj_s id sg => [Pauipc X31 (inl id); Pjal_rr X0 X31 0]
  | Pj_r rs sg => [Pjal_rr X0 rs 0]
  | Pjal_s id sg => [Pauipc X1 (inl id); Pjal_rr X1 X1 0]
  | Pjal_r rs sg => [Pjal_rr X1 rs 0]

  (* we remove the pseudo instruction that use any type here *)
  | Plw_a rd ra ofs =>
    [Plw rd ra (transf_offset ofs)]
  | Pld_a rd ra ofs =>
    [Pld rd ra (transf_offset ofs)]
  | Psw_a rs ra ofs =>
    [Psw rs ra (transf_offset ofs)]
  | Psd_a rs ra ofs =>
    [Psd rs ra (transf_offset ofs)]
  | Pfld_a rd ra ofs =>
    [Pfld rd ra (transf_offset ofs)]
  | Pfsd_a rs ra ofs =>
    [Pfsd rs ra (transf_offset ofs)]

  (* lower 12 bit offset *)
  | Plb  rd rs ofs => [Plb  rd rs (transf_offset ofs)]
  | Plbu rd rs ofs => [Plbu rd rs (transf_offset ofs)]
  | Plh  rd rs ofs => [Plh  rd rs (transf_offset ofs)]
  | Plhu rd rs ofs => [Plhu rd rs (transf_offset ofs)]
  | Plw  rd rs ofs => [Plw  rd rs (transf_offset ofs)]
  | Pld  rd rs ofs => [Pld  rd rs (transf_offset ofs)]
  | Pfls rd rs ofs => [Pfls rd rs (transf_offset ofs)]
  | Pfld rd rs ofs => [Pfld rd rs (transf_offset ofs)]
  | Psb  rd rs ofs => [Psb  rd rs (transf_offset ofs)]
  | Psh  rd rs ofs => [Psh  rd rs (transf_offset ofs)]
  | Psw  rd rs ofs => [Psw  rd rs (transf_offset ofs)]
  | Psd  rd rs ofs => [Psd  rd rs (transf_offset ofs)]
  | Pfss rd rs ofs => [Pfss rd rs (transf_offset ofs)]
  | Pfsd rd rs ofs => [Pfsd rd rs (transf_offset ofs)]

  (* high 20 bit *)
  | Pluil rd ofs => 
      let lo := Int64.sign_ext 12 ofs in
      let hi := Int64.shru (Int64.sub ofs lo) (Int64.repr 12) in
      [Pluil rd hi]
  | Pluiw rd ofs =>
      let lo := Int.sign_ext 12 ofs in
      let hi := Int.shru (Int.sub ofs lo) (Int.repr 12) in
      if Archi.ptr64 then
        [Pluil rd (Int64.repr (Int.unsigned hi))]
      else
        [Pluiw rd hi]        
      
  (* Some pseudo instructions in riscv manual *)
  | Pmv rd rs =>
    if Archi.ptr64 then
      [Paddil rd rs (Int64.zero)]
    else
      [Paddiw rd rs (Int.zero)]

  (* Some instructions redundant in 64bit mode *)
  | Psltiw rd rs imm =>
      if Archi.ptr64 then
        [Psltil rd rs (Int64.repr (Int.signed imm))]
      else [i]
  | Psltiuw rd rs imm =>
      if Archi.ptr64 then
        [Psltiul rd rs (Int64.repr (Int.signed imm))]
      else [i]
  | Pandiw rd rs imm =>
      if Archi.ptr64 then
        [Pandil rd rs (Int64.repr (Int.signed imm))]
      else [i]       
  | Poriw rd rs imm =>
      if Archi.ptr64 then
        [Poril rd rs (Int64.repr (Int.signed imm))]
      else [i]
  | Pxoriw rd rs imm =>
      if Archi.ptr64 then
        [Pxoril rd rs (Int64.repr (Int.signed imm))]
      else [i]
  (* | Pluiw rd imm => *)
  (*     if Archi.ptr64 then *)
  (*       [Pluil rd (Int64.repr (Int.signed imm))] *)
  (*     else [i] *)
  | Psltw rd rs imm =>
      if Archi.ptr64 then
        [Psltl rd rs imm]
      else [i]
  | Psltuw rd rs imm =>
      if Archi.ptr64 then
        [Psltul rd rs imm]
      else [i]
  | Pandw rd rs1 rs2 =>
      if Archi.ptr64 then
        [Pandl rd rs1 rs2]
      else [i]
  | Porw rd rs1 rs2 =>
      if Archi.ptr64 then
        [Porl rd rs1 rs2]
      else [i]
  | Pxorw rd rs1 rs2 =>
      if Archi.ptr64 then
        [Pxorl rd rs1 rs2]
      else [i]
             
  | _ => [i]
  end.


Definition transf_code (c: code) : code :=
  concat (map transf_instr c).

Definition transf_function (f: function) :=
  {|
    fn_sig := fn_sig f;
    fn_code := transf_code (fn_code f);
    fn_stacksize := fn_stacksize f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.
