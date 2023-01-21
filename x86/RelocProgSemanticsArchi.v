Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.
Require Import RelocProgGlobalenvs.

(** Evaluating an addressing mode *)

Section WITHGE.

Variable ge: Genv.t.

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

End WITHGE.

Definition exec_load (sz:ptrofs) (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg):=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf sz (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (sz:ptrofs) (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg):=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf sz (undef_regs destroyed rs)) m'
  | None => Stuck
  end.


Open Scope asm.

Definition eval_ros (ge : Genv.t) (ros : ireg + ident) (rs : regset) :=
  match ros with
  | inl r => rs r
  | inr symb => Genv.symbol_address ge symb Ptrofs.zero
  end.


Definition goto_ofs (sz:ptrofs) (ofs:Z) (rs: regset) (m: mem) :=
  match rs#PC with
  | Vptr b o =>
    Next (rs#PC <- (Vptr b (Ptrofs.add o (Ptrofs.add sz (Ptrofs.repr ofs))))) m
  | _ => Stuck
  end.

(* evaluation with globalenvs which are the same in genv_symb *)

Lemma eval_addrmode_match_ge: forall ge1 ge2 a rs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    RelocProgSemanticsArchi.eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
Proof.
  unfold eval_addrmode. destruct Archi.ptr64;intros.
  - unfold eval_addrmode64.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
  - unfold eval_addrmode32.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
Qed.

Lemma exec_load_match_ge: forall sz ge1 ge2 chunk m a rs rd (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_load sz ge1 chunk m a rs rd = exec_load sz ge2 chunk m a rs rd.
Proof.
  unfold exec_load.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.

Lemma exec_store_match_ge: forall sz ge1 ge2 chunk m a rs rd l (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_store sz ge1 chunk m a rs rd l = exec_store sz ge2 chunk m a rs rd l.
Proof.
  unfold exec_store.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.


Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.

(** Execution of instructions *)

Definition exec_instr (ge: Genv.t) (i: instruction) (rs: regset) (m: mem) : outcome :=
  let sz := Ptrofs.repr (instr_size i) in
  let nextinstr := nextinstr sz in
  let nextinstr_nf := nextinstr_nf sz in
  let exec_load := exec_load sz in
  let exec_store := exec_store sz in
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) ) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) ) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) ) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero)) ) m
  | Pmovl_rm rd a =>
      exec_load ge Mint32 m a rs rd
  | Pmovq_rm rd a =>
      exec_load ge Mint64 m a rs rd
  | Pmovl_mr a r1 =>
      exec_store ge Mint32 m a rs r1 nil
  | Pmovq_mr a r1 =>
      exec_store ge Mint64 m a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) ) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) ) m
  | Pmovsd_fm rd a =>
      exec_load ge Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store ge Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) )m
  | Pmovss_fm rd a =>
      exec_load ge Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store ge Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load ge Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store ge Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load ge Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store ge Mfloat32 m a rs ST0 (ST0 :: nil)
  (* | Pxchg_rr r1 r2 => *)
  (*     Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) )) m *)
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store ge Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store ge Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load ge Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load ge Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load ge Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load ge Mint16signed m a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs))) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m
  | Psubl_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n)))) m
  | Paddq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n)))) m
  | Psubq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd (Vlong n)))) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1))) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1))) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n)))) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63)))) ) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) ) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) ) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) ) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) ) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1)) ) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1)) ) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n))) ) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n))) ) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1)) ) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1)) ) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n))) ) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n))) ) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero) ) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero)) ) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1)) ) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1)) ) m 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n))) ) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n))) ) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd)) ) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd)) ) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX)) ) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX)) ) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n))) ) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n))) ) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX)) ) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX)) ) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n))) ) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n))) ) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX)) ) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX)) ) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n))) ) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n))) ) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n))))) ) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n))) ) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n))) ) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) ) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m) ) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) ) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m) ) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) ) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m) ) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m) ) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m) ) m
  | Pcmov c rd r1 =>
    let v :=
        match eval_testcond c rs with
        | Some b => if b then rs#r1 else rs#rd
        | None   => Vundef
      end in
      Next (nextinstr (rs#rd <- v)) m
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs))) ) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1)) ) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1)) ) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1)) ) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1)) ) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd)) ) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd)) ) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs) ) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero)) ) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1)) ) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1)) ) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1)) ) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1)) ) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd)) ) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd)) ) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs) ) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero)) ) m
  (** Branches and calls *)
  | Pjmp_l_rel ofs =>
      goto_ofs sz ofs rs m
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc_rel cond ofs =>
      match eval_testcond cond rs with
      | Some true => goto_ofs sz ofs rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2_rel cond1 cond2 ofs =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_ofs sz ofs rs m
      | Some _, Some _ => Next (nextinstr rs ) m
      | _, _ => Stuck
      end
  | Pjmptbl_rel r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some ofs => goto_ofs sz ofs (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_r r sg =>
    let addr := rs r in
    let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
    match Mem.storev Mptr m sp (Val.offset_ptr rs#PC sz) with
    | None => Stuck
    | Some m2 =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                      #PC <- addr
                              #RSP <- sp) m2
    end
  | Pcall_s id sg =>
    let addr := Genv.symbol_address ge id Ptrofs.zero in
    let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
    match Mem.storev Mptr m sp (Val.offset_ptr rs#PC sz) with
    | None => Stuck
    | Some m2 =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                      #PC <- addr
                              #RSP <- sp) m2
    end
  (* | Pcall (inr gloc) sg => *)
  (*     Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (Genv.symbol_address ge gloc Ptrofs.zero)) m *)
  (* | Pcall (inl r) sg => *)
  (*     Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (rs r)) m *)
  | Pret =>
      match loadvv Mptr m rs#RSP with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)) in
        Next (rs #RSP <- sp
                 #PC <- ra
                 #RA <- Vundef) m
      end

  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load ge (if Archi.ptr64 then Many64 else Many32) m a rs rd 
  | Pmov_mr_a a r1 =>
      exec_store ge (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil 
  | Pmovsd_fm_a rd a =>
      exec_load ge Many64 m a rs rd 
  | Pmovsd_mf_a a r1 =>
      exec_store ge Many64 m a rs r1 nil 
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs ) m
  | Pcfi_adjust n => Next rs m
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  |Pnop => Next (nextinstr rs ) m

  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
  | _ => Stuck
  end.

Lemma exec_instr_refl: forall i rs m ge tge
    (symbol_address_pres: forall id ofs,
    RelocProgGlobalenvs.Genv.symbol_address ge id ofs =
    RelocProgGlobalenvs.Genv.symbol_address tge id ofs),
    exec_instr ge i rs m = exec_instr tge i rs m.
Proof.
  destruct i;simpl;auto;intros.
  1-27: try (erewrite symbol_address_pres;eauto).
  1-24: try (erewrite exec_load_match_ge;eauto;eapply symbol_address_pres;eauto).
  1-12: try (erewrite exec_store_match_ge;eauto;eapply symbol_address_pres;eauto).
  do 3 f_equal.
  unfold eval_addrmode32.
  destruct a. f_equal.
  f_equal. destr.
  destruct p. eapply symbol_address_pres;eauto.
  do 3 f_equal.
  unfold eval_addrmode64.
  destruct a. f_equal.
  f_equal. destr.
  destruct p. eapply symbol_address_pres;eauto.
Qed.


End WITH_INSTR_SIZE.