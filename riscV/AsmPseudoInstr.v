Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition transf_instr i : (list instruction) :=
  match i with
  | Ploadsymbol_high rd id ofs =>
      [Plui_s rd id (Ptrofs.signed ofs)]
  | Ploadsymbol rd id ofs =>
      (* not consider :  Archi.pic_code *)
      (* I think it is necessary to check the 20-bit bounds for ofs when generating reocation entry for Plui_s *)
      (* We expand Ploadsymbol here because the id_eliminate in assembler is one to one *)
      [Plui_s rd id (Ptrofs.signed ofs); Paddi_s rd rd id (Ptrofs.signed ofs)]
        
  (* transform pseudo jump instruction *)
  | Pj_s id sg => [Pjal_ofs X0 (inl id)]
  | Pj_r rs sg => [Pjal_rr X0 rs 0]
  | Pjal_s id sg => [Pjal_ofs X1 (inl id)]
  | Pjal_r rs sg => [Pjal_rr X1 rs 0]
                     
  (* we remove the pseudo instruction that use any type here *)
  | Plw_a rd ra ofs =>
    [Plw rd ra ofs]
  | Pld_a rd ra ofs =>
    [Pld rd ra ofs]
  | Psw_a rs ra ofs =>
    [Psw rs ra ofs]
  | Psd_a rs ra ofs =>
    [Psd rs ra ofs]
  | Pfld_a rd ra ofs =>
    [Pfld rd ra ofs]
  | Pfsd_a rs ra ofs =>
    [Pfsd rs ra ofs]

  (* Some pseudo instructions in riscv manual *)
  | Pmv rd rs =>
    if Archi.ptr64 then
      [Paddil rd rs (Int64.zero)]
    else
      [Paddiw rd rs (Int.zero)]
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
