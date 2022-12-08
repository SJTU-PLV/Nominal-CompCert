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

(** check the branch offset *)
Definition expand_instr (i: instruction) (ofs: Z) (code:code) : res (list instruction) :=
  let sz:= instr_size i in
  match i with
  | Pj_l lbl =>
    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [i]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbeql  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbne_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbnel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbeq_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbltl  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbge_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbltul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbgeu_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbgel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pblt_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbgeul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbltu_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbeqw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbne_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbnew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbeq_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbltw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbge_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbltuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbgeu_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbgew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pblt_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end

  | Pbgeuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
        OK [i]
      else if (- (two_power_nat 19) <=? relOfs) && (relOfs <? (two_power_nat 19)) then
        OK [Pbltu_ofs rs1 rs2 4; Pj_l lbl]
      else Error [MSG "relOfs out of range in "; MSG (instr_to_string i)]
    end
                                        
  | _ => OK [i]
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
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbeq_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbnel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbne_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbltl  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pblt_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbltul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbltu_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbgel  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbge_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbgeul rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbgeu_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbeqw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbeq_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbnew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbne_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbltw  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pblt_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbltuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbltu_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbgew  rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbge_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
    end

  | Pbgeuw rs1 rs2 lbl =>    match label_pos instr_size lbl 0 code with
    | None =>   Error (msg"Label not found")
    | Some pos =>
      let relOfs :=  Z.div2 (pos - (ofs+sz))  in
      if (- (two_power_nat 11) <=? relOfs) && (relOfs <? (two_power_nat 11)) then
      OK (Pbgeu_ofs rs1 rs2 relOfs)
      else Error [MSG "relOfs out of range in transl_instr "; MSG (instr_to_string i)]
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

Definition acc_expand_instr c r i :=
  do r' <- r;
    let '(ofs, code) := r' in
    do i' <- expand_instr i ofs c;
      OK (ofs + code_size instr_size i', code ++ i').

Definition acc_transl_instr c r i :=
  do r' <- r;
    let '(ofs, code) := r' in
    do i' <- transl_instr i ofs c;
      OK (ofs + instr_size i', code ++ [i']).
  
Definition transl_code (c:code) : res code :=
  do (_, c') <- 
     fold_left (acc_expand_instr c)
               c
               (OK (0, []));
  do (_, c'') <- 
     fold_left (acc_transl_instr c')
               c'
               (OK (0, []));
  OK c''.


Definition trans_function (f: function) :res function :=
  do instrs <- transl_code (fn_code f);
  OK (mkfunction (fn_sig f) instrs (fn_stacksize f)).

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef trans_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

End INSTR_SIZE.
