Require Import Coqlib Integers AST Memdata Maps.
Require Import Asm Asmgen RealAsm.
Require Import Errors.
Require Import Memory.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope nat_scope.

Context (coq_string_to_ident : string -> option ident).

Definition sp_adjustment_elf64 (sg:signature) (sz:Z) :=
  match (sg.(sig_cc)).(cc_vararg) with
  | Some _ =>
    let ofs := align (sz-8) 16 in
    let sz :=  ofs + 176 (* save area *) + 8 (* return address *) in
    let sz := align sz 16 in
    (sz -8, ofs)
  | None =>
    let sz := align sz 16 in
    (sz -8, 0)
  end.

(* Pstoreptr (linear addr ) (RAX) eval_addrmode32 *)
(** Set stack alignment to 16  *)
(* variant argument function: update stack size (left for AsmBuiltin.v) *)
Definition transf_instr (sg:signature) (i: instruction): list instruction :=
  match i with
  | Pallocframe sz ofs_ra ofs_link =>
    (* follow Asmexpand.ml *)
    if Archi.ptr64 then
      let (sz, save_regs) := sp_adjustment_elf64 sg sz in
      match (sg.(sig_cc)).(cc_vararg) with
      | Some _ =>
        let addr := linear_addr RSP (Ptrofs.unsigned ofs_link) in
        let savereg_sg := mksignature [] Tvoid cc_default in
        match coq_string_to_ident "__compcert_va_saveregs" with
        | Some savereg_name =>          
          [Padd RAX RSP (size_chunk Mptr);
          Psub RSP RSP sz;
          Pleaq R10 (linear_addr RSP save_regs);
          Pcall_s savereg_name savereg_sg;
          Pstoreptr addr RAX]
        | None =>
          [ Padd RAX RSP (size_chunk Mptr); Psub RSP RSP sz; Pstoreptr addr RAX]
        end
      | None =>
        let addr := linear_addr RSP (Ptrofs.unsigned ofs_link) in
        [ Padd RAX RSP (size_chunk Mptr); Psub RSP RSP sz; Pstoreptr addr RAX]
      end
    else
      let sz := align sz 16 - size_chunk Mptr in
      let addr := linear_addr RSP (Ptrofs.unsigned ofs_link) in
      [ Padd RAX RSP (size_chunk Mptr); Psub RSP RSP sz; Pstoreptr addr RAX]
  | Pfreeframe fsz ofs_ra ofs_link =>
    if Archi.ptr64 then
      let (sz, _) := sp_adjustment_elf64 sg fsz in
      [Padd RSP RSP sz]
    else
      let sz := align fsz 16 - size_chunk Mptr in
    [ Padd RSP RSP sz ]
  | _ => [ i ]
  end.

Definition transf_code (sg: signature) (c: code) : code :=
  concat (map (transf_instr sg) c).

Definition transf_function (f: function) :=
  {|
    fn_sig := fn_sig f;
    fn_code := transf_code f.(fn_sig) (fn_code f);
    fn_stacksize := fn_stacksize f;
    fn_ofs_link := fn_ofs_link f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.
