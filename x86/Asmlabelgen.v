Require Import Coqlib Integers AST Maps.
Require Import Events.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs .
Import ListNotations.

Local Open Scope error_monad_scope.

Section INSTR_SIZE.
  Variable instr_size : instruction -> Z.

Fixpoint findAllLabel (l: list label)(all:list instruction): res (list Z) :=
  match l with
  |[] => OK []
  |h :: t =>
   match label_pos instr_size h 0 all with
   |None => Error (msg"Label not found")
   |Some pos =>
    do tail <-  (findAllLabel t all);
      OK (pos::tail)
   end
  end.

Definition transl_instr (i: instruction) (ofs:Z) (code:code) : res instruction :=
  let sz := instr_size i in
  match i with
  |Pjmp_l lbl =>
   match label_pos instr_size lbl 0 code with
   (* label not found *)
   |None =>   Error (msg"Label not found")
   |Some pos =>
    let relOfs :=  pos - (ofs+sz)  in
    OK (Pjmp_l_rel relOfs)
   end

  |Pjcc cond lbl =>
   match label_pos instr_size lbl 0 code with
   (* label not found *)
   |None =>  Error (msg"Label not found")
   |Some pos =>
    let relOfs := pos - (ofs+sz) in
    OK (Pjcc_rel cond relOfs)
   end

  |Pjcc2 cond1 cond2 lbl =>
   match label_pos instr_size lbl 0 code with
   (* label not found *)
   |None =>  Error (msg"Label not found")
   |Some pos =>
    let relOfs := pos - (ofs+sz) in
    OK (Pjcc2_rel cond1 cond2 relOfs)
   end

  (* Do this after symbol table generation*)
  |Pjmptbl r tbl =>
   do lst <-  findAllLabel tbl code;
   let ofsLst := map (Zplus (-( sz + ofs))) lst in
   OK (Pjmptbl_rel r ofsLst)
  
  | Plabel _ => OK Pnop
  
  |_ =>
   OK i 
  end.


Definition acc_transl_instr c r i :=
  do r' <- r;
    let '(ofs, code) := r' in
    do i' <- transl_instr i ofs c;
      OK (ofs + instr_size i, (i' :: code)).
  
Definition transl_code (c:code) : res code :=
  do rs <- 
     fold_left (acc_transl_instr c)
               c
               (OK (0, []));
  let '(_, c') := rs in
  OK (rev c').


Definition trans_function (f: function) :res function :=
  if func_no_jmp_rel_dec f then 
    do instrs <- transl_code (fn_code f);
      OK (mkfunction (fn_sig f) instrs (fn_stacksize f) (fn_ofs_link f))
  else
    Error (msg "Some source function contains relative jumps").

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef trans_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

End INSTR_SIZE.

