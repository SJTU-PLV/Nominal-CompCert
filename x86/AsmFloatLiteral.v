Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import SymbolString.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition gen_float_mask :
  (list (ident * globdef fundef unit)) * (ident * ident * ident * ident) :=
  (* 0x8000_0000_0000_0000 *)
  let Zerod_mask := (Int64.repr (-9223372036854775808:Z)) in
  let negd_mask := [Init_int64 Zerod_mask]++[Init_int64 Int64.zero] in
  (* 0x8000_0000 *)
  let Zeros_mask := (Int.repr (-2147483648:Z)) in
  let negs_mask := [Init_int32 Zeros_mask]++[Init_int32 Int.zero]++[Init_int32 Int.zero]
                                        ++[Init_int32 Int.zero]in
  (* 0x7FFF_FFFF_FFFF_FFFF *)
  let NaNd_mask := (Int64.repr (9223372036854775807:Z)) in
  let absd_mask := [Init_int64 NaNd_mask]++[Init_int64 Int64.mone ] in
  (* 0x7FFF_FFFF *)
  let NaNs_mask := (Int.repr (2147483647:Z)) in
  let abss_mask := [Init_int32 NaNs_mask]++[Init_int32 Int.mone]++[Init_int32 Int.mone]
                                        ++[Init_int32 Int.mone]in
  let negd_var := mkglobvar (tt) (negd_mask) (true) (false) in
  let negs_var := mkglobvar (tt) (negs_mask) (true) (false) in
  let absd_var := mkglobvar (tt) (absd_mask) (true) (false) in
  let abss_var := mkglobvar (tt) (abss_mask) (true) (false) in
  let (neg, abs) := (create_float_mask_ident tt) in
  let (negd, negs) := neg in
  let (absd, abss) := abs in
  let negd_def := (Gvar negd_var) in
  let negs_def := (Gvar negs_var) in
  let absd_def := (Gvar absd_var) in
  let abss_def := (Gvar abss_var) in
  (((negd, negd_def)::(negs, negs_def)::(absd, absd_def)::(abss, abss_def)::[]),
   (negd, negs, absd, abss)).

Section FLOAT_MASK.

Variable (negd negs absd abss:ident).
  
Definition transf_instr (i: instruction):
  (list instruction)*(list (ident * (globdef fundef unit))) :=
  match i with
  | Pmovsd_fi rd n =>
    let id := create_float_literal_ident tt in
    let var := mkglobvar (tt) ([Init_float64 n]) (true) (false) in
    let def := (Gvar var) in
    let i' := Pmovsd_fm rd (Addrmode None None (inr (id,Ptrofs.zero))) in
    ([i'],[(id,def)])
  | Pmovss_fi rd n =>
    let id := create_float_literal_ident tt in
    let var := mkglobvar (tt) ([Init_float32 n]) (true) (false) in
    let def := (Gvar var) in
    let i' := Pmovss_fm rd (Addrmode None None (inr (id,Ptrofs.zero))) in
    ([i'],[(id,def)])
  | Pnegd fd =>
    let i' := Pxorpd_fm fd (Addrmode None None (inr (negd,Ptrofs.zero))) in
    ([i'], [])
  | Pnegs fd =>
    let i' := Pxorps_fm fd (Addrmode None None (inr (negs,Ptrofs.zero))) in
    ([i'], [])
  | Pabsd fd =>
    let i' := Pandpd_fm fd (Addrmode None None (inr (absd,Ptrofs.zero))) in
    ([i'], [])
  | Pabss fd =>
    let i' := Pandps_fm fd (Addrmode None None (inr (abss,Ptrofs.zero))) in
    ([i'], [])
  | _ => ([i],[])
  end.

Definition acc_flt_lit (t: code * list (ident * (globdef fundef unit)))
           (i: instruction) :=
  let (c, flt_lit) := t in
  let (c', flt_lit') := transf_instr i in
  let c'' := c ++ c' in
  let flt_lit'' := flt_lit ++ flt_lit' in
  (c'', flt_lit'').
  
Definition transf_code (c: code) :
  (code*(list (ident * (globdef fundef unit)))) :=
   fold_left acc_flt_lit c ([],[]).
     
Definition transf_def (iddef: ident * (AST.globdef Asm.fundef unit))
  : list (ident * (AST.globdef Asm.fundef unit)) :=
  match iddef with
  | (id, (Gvar v)) => [(id, (Gvar v))]
  | (id, (Gfun (External ef))) => [(id, (Gfun (External ef)))]
  | (id, (Gfun (Internal f))) =>
    let c := fn_code f in
    let (c', flt_lit) :=  transf_code c in 
    let f' := mkfunction (fn_sig f) c' (fn_stacksize f) (fn_ofs_link f) (*SANCC*) in
    [(id, (Gfun (Internal f')))] ++ flt_lit
  end.

Definition gen_float_literal iddef :=
  concat (map transf_def iddef).

End FLOAT_MASK.

Definition transf_program (p: Asm.program) : program :=
  let (mask_defs, mask_idl) := gen_float_mask in
  let '(negd, negs, absd, abss) := mask_idl in
  let defs_mask := (AST.prog_defs p) ++ mask_defs in
  let defs := gen_float_literal negd negs absd abss (defs_mask) in
  {| prog_defs := defs;
     prog_public := AST.prog_public p;
     prog_main := AST.prog_main p |}.
  
