(* ******************** *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 28, 2020 *)
(* ******************** *)
Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Import ListNotations.

Local Open Scope error_monad_scope.

Definition transf_instr (i: instruction) (cur_sg: signature) : res (list instruction) :=
  match i with
  | Pcall_r _ sg =>
    if (negb Archi.ptr64) && cc_structret (sig_cc sg) then
      let i1 := Psubl_ri RSP (Int.repr 4) in
      let i2 := Pmovl_mr (Addrmode (Some RSP) None (inl 0)) RAX in
      OK ([i]++[i1]++[i2]) else
      OK [i]
  | Pcall_s _ sg =>
    if (negb Archi.ptr64) && cc_structret (sig_cc sg) then
      let i1 := Psubl_ri RSP (Int.repr 4) in
      let i2 := Pmovl_mr (Addrmode (Some RSP) None (inl 0)) RAX in
      OK ([i]++[i1]++[i2]) else
      OK [i]
  | Pret =>
    if (negb Archi.ptr64) && cc_structret (sig_cc cur_sg) then
      (* %rax := [4(%rsp)] *)
      let i1 := Pmovl_rm RAX (Addrmode (Some RSP) None (inl 4)) in
      let i2 := Pret_iw (Int.repr 4) in
      OK ([i1]++[i2]) else
      OK [i]
  |_ => OK [i] 
  end.

Definition acc_transl_instr (sg: signature) (r:res code) (i:instruction) :=
  do acc_i <- r;
  do i' <- transf_instr i sg;
  OK (acc_i ++ i').
  
Definition transl_code (c: code) (sg: signature) : res code :=
  do code <- fold_left (acc_transl_instr sg) c (OK []);
  OK (code).

Definition transf_function (f: function) : res function :=
  (* make sure that code can not have relative jumps*)
  if func_no_jmp_rel_dec f then
    do fn_code' <- transl_code (fn_code f) (fn_sig f);
    OK {|
        fn_sig := fn_sig f;
        fn_code := fn_code';
        fn_stacksize := fn_stacksize f;
        fn_ofs_link := fn_ofs_link f
      |}
  else
    Error [MSG "Code contains relative jumps"].

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
