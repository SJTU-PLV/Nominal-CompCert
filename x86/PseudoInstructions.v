Require Import Coqlib Integers AST Memdata Maps.
Require Import Asm Asmgen RealAsm.
Require Import Errors.
Require Import Memory.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope nat_scope.

Definition linear_addr reg ofs :=
  Addrmode (Some reg) None (inl ofs).

Definition Plea := if Archi.ptr64 then Pleaq else Pleal.
Definition Padd dst src z := Plea dst (linear_addr src z).
Definition Psub dst src z := Padd dst src (- z).

Definition Pstoreptr := if Archi.ptr64 then Pmovq_mr else Pmovl_mr.

(* Pstoreptr (linear addr ) (RAX) eval_addrmode32 *)
Definition transf_instr (i: instruction): list instruction :=
  match i with
  | Pallocframe sz ofs_ra ofs_link =>
    let sz := align sz 8 - size_chunk Mptr in
    let addr := linear_addr RSP (Ptrofs.unsigned ofs_link) in
    [ Padd RAX RSP (size_chunk Mptr); Psub RSP RSP sz; Pstoreptr addr RAX]
  | Pfreeframe fsz ofs_ra ofs_link =>
    let sz := align fsz 8 - size_chunk Mptr in
    [ Padd RSP RSP sz ]
  | _ => [ i ]
  end.

Definition transf_code (c: code) : code :=
  concat (map transf_instr c).

Definition transf_function (f: function) :=
  {|
    fn_sig := fn_sig f;
    fn_code := transf_code (fn_code f);
    fn_stacksize := fn_stacksize f;
    fn_ofs_link := fn_ofs_link f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.
