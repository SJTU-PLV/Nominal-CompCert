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

  
Fixpoint findAllLabel (l: list label) (all:list instruction): res (list Z) :=
  match l with
  | [] => OK []
  | h :: t =>
    match label_pos instr_size h 0 all with
    | None => Error (msg"Label not found")
    | Some pos =>
      do tail <-  (findAllLabel t all);
      OK (pos::tail)
    end
  end.

(* we do not check ptr64 for branch instructions, leave for future work *)
Definition transl_instr (i: instruction) (ofs: Z) (code:code) : res instruction :=
  let sz:= instr_size i in
  match i with
  | Pj_l lbl =>
    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pjal_ofs X0 (inr relOfs))   
    end

  | Pbeql  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbeq_ofs rs1 rs2 relOfs)
    end

  | Pbnel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbne_ofs rs1 rs2 relOfs)
    end

  | Pbltl  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pblt_ofs rs1 rs2 relOfs)
    end

  | Pbltul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbltu_ofs rs1 rs2 relOfs)
    end

  | Pbgel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbge_ofs rs1 rs2 relOfs)
    end

  | Pbgeul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbgeu_ofs rs1 rs2 relOfs)
    end

  | Pbeqw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbeq_ofs rs1 rs2 relOfs)
    end

  | Pbnew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbne_ofs rs1 rs2 relOfs)
    end

  | Pbltw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pblt_ofs rs1 rs2 relOfs)
    end

  | Pbltuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbltu_ofs rs1 rs2 relOfs)
    end

  | Pbgew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbge_ofs rs1 rs2 relOfs)
    end

  | Pbgeuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      OK (Pbgeu_ofs rs1 rs2 relOfs)
    end

  | Pbtbl rs tbl =>
    (* ofsLst is the relative address of the start of the current function *)
    do ofsLst <-  findAllLabel tbl code;
    (* let ofsLst := map (Z.add (-( sz + ofs))) lst in *)
    (* Pbtbl_ofs => Pjal_rr which is absolute addressing *)
    OK (Pbtbl_ofs rs ofsLst)

  | Plabel lbl => OK Pnop
                                        
  | _ => OK i
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
  do instrs <- transl_code (fn_code f);
  OK (mkfunction (fn_sig f) instrs (fn_stacksize f)).

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef trans_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

End INSTR_SIZE.
