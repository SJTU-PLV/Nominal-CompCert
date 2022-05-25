(* *******************  *)
(* Author: Yuting Wang, Jinhua Wu *)
(* Date:  May 23, 2022 *)
(* *******************  *)

(** * The semantics of relocatable program using only the symbol table *)

(** The key feature of this semantics: it uses mappings from the ids
    of global symbols to memory locations in deciding their memory
    addresses. These mappings are caculated by using the symbol table.
    *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.

    
(** Global environments using only the symbol table *)

Definition gdef := globdef Asm.fundef unit.

Module Genv.

Section GENV.

Record t: Type := mkgenv {
  genv_symb: PTree.t (block * ptrofs);        (**r mapping symbol -> block * ptrofs *)
  genv_ext_funs: NMap.t (option external_function);             (**r mapping blocks -> external function defintions *)
  genv_instrs: NMap.t (ptrofs -> option instruction);    (**r mapping block  -> instructions mapping *)
  (* genv_sup: sup;               (**r symbol support *) *)
  genv_senv : Globalenvs.Senv.t; (** how to use it *)

  (** some properties about support*)
  (* genv_sup_glob : forall b, sup_In b genv_sup -> exists id, b = Global id; *)
  (* genv_symb_range: forall id b ofs,PTree.get id genv_symb = Some (b,ofs) -> sup_In b genv_sup; *)
  (* genv_defs_range: forall b g, NMap.get _ b genv_defs = Some g -> sup_In b genv_sup; *)
  (* genv_vars_eq: forall id b, PTree.get id genv_symb = Some b -> b = Global id; *)
  (* genv_vars_inj: forall id1 id2 b, *)
  (*   PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2 *)
}.

(** ** Lookup functions *)

Definition find_symbol (ge: t) (id: ident) : option (block * ptrofs):=
  PTree.get id ge.(genv_symb).

Definition symbol_address (ge: t) (id: ident) (ofs: ptrofs) : val :=
  match find_symbol ge id with
  | Some (b, o) => Vptr b (Ptrofs.add ofs o)
  | None => Vundef
  end.

Definition find_ext_funct (ge: t) (v:val) : option external_function :=
  match v with
  | Vptr b ofs =>
    if Ptrofs.eq ofs Ptrofs.zero then
      NMap.get _ b ge.(genv_ext_funs)
    else None
  | _ => None
  end.

Lemma symbol_address_offset : forall ge ofs1 b s ofs,
    symbol_address ge s Ptrofs.zero = Vptr b ofs ->
    symbol_address ge s ofs1 = Vptr b (Ptrofs.add ofs ofs1).
Proof.
  unfold symbol_address. intros. 
  destruct (find_symbol ge s) eqn:FSM.
  - 
    destruct p.
    inv H.
    rewrite Ptrofs.add_zero_l. rewrite Ptrofs.add_commut. auto.
  - 
    inv H.
Qed.

Lemma find_sym_to_addr : forall (ge:t) id b ofs,
    find_symbol ge id = Some (b, ofs) ->
    symbol_address ge id Ptrofs.zero = Vptr b ofs.
Proof.
  intros. unfold symbol_address. rewrite H.
  rewrite Ptrofs.add_zero_l. auto.
Qed.

(** Find an instruction at an offset *)
Definition find_instr (ge: t) (v:val) : option instruction :=
  match v with
  | Vptr b ofs => genv_instrs ge b ofs
  | _ => None
  end.

End GENV.

End Genv.


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
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1)) ) m
      | Some false => Next (nextinstr rs ) m
      | None => Next (nextinstr (rs#rd <- Vundef) ) m
      end
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
        match Mem.loadv Mptr m rs#RSP with
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

(** Note: Builtin instructions are eliminated after AsmBuiltinInline.v . And the size of builtin instructions are unspecific *)
(** * Evaluation of builtin arguments, *)

Section EVAL_BUILTIN_ARG.

Variable A: Type.

Variable ge: Genv.t.
Variable e: A -> val.
Variable sp: val.
Variable m:mem. 

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m  (Genv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.


(** Small step semantics *)

Inductive step (ge: Genv.t) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some i ->
      exec_instr ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
(* | exec_step_builtin: *)
(*     forall b ofs ef args res rs m vargs t vres rs' m', *)
(*       rs PC = Vptr b ofs -> *)
(*       Genv.find_ext_funct ge (Vptr b ofs) = None -> *)
(*       Genv.find_instr ge (Vptr b ofs) = Some (Pbuiltin ef args res)  -> *)
(*       eval_builtin_args preg ge rs (rs RSP) m args vargs -> *)
(*       external_call ef (Genv.genv_senv ge) vargs m t vres m' -> *)
(*         rs' = nextinstr_nf  *)
(*                 (set_res res vres *)
(*                          (undef_regs (map preg_of (destroyed_by_builtin ef)) rs))  *)
(*                 (Ptrofs.repr (instr_size (Pbuiltin ef args res))) -> *)
(*         step ge (State rs m) t (State rs' m') *)
| exec_step_external:
    forall b ofs ef args res rs m t rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = Some ef ->
      forall ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
        (RA_NOT_VUNDEF: ra <> Vundef)
        (ARGS: extcall_arguments (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args),
        external_call ef (Genv.genv_senv ge) args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)
                                      (undef_regs (map preg_of destroyed_at_call) rs)))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
        step ge (State rs m) t (State rs' m').

(** Initialization of the global environment *)
Definition gen_global (id:ident) (e:symbentry) : (block*ptrofs) :=
  match e.(symbentry_secindex) with
  | secindex_normal sec =>
    (Global sec, Ptrofs.repr e.(symbentry_value))
  | _ =>
    (Global id, Ptrofs.zero)
  end.

Definition gen_symb_map (symbtbl: symbtable) : PTree.t (block * ptrofs) :=
  PTree.map gen_global symbtbl.


(* Fixpoint add_globals (ge:Genv.t) (t: symbtable) : Genv.t := *)
(*   match t with *)
(*   | nil => ge *)
(*   | (e::l) =>  *)
(*     let ge' := add_external_global extfuns ge e in *)
(*     add_external_globals extfuns ge' l *)
(*   end.  *)



(* Fixpoint add_external_globals (extfuns: PTree.t external_function) *)
(*          (ge:Genv.t) (t: symbtable) : Genv.t := *)
(*   match t with *)
(*   | nil => ge *)
(*   | (e::l) =>  *)
(*     let ge' := add_external_global extfuns ge e in *)
(*     add_external_globals extfuns ge' l *)
(*   end.  *)


(* Lemma genv_senv_add_external_global: *)
(*   forall exts ge a, *)
(*     Genv.genv_senv (add_external_global exts ge a) = *)
(*     Genv.genv_senv ge. *)
(* Proof. *)
(*   unfold add_external_global. intros. destr. *)
(* Qed. *)

(* Lemma genv_senv_add_external_globals: *)
(*   forall st exts ge, *)
(*     Genv.genv_senv (add_external_globals exts ge st) = *)
(*     Genv.genv_senv ge. *)
(* Proof. *)
(*   induction st; simpl; intros; eauto. *)
(*   rewrite IHst. *)
(*   apply genv_senv_add_external_global. *)
(* Qed. *)

(* Lemma add_external_global_pres_instrs : forall extfuns ge e, *)
(*     Genv.genv_instrs (add_external_global extfuns ge e) = Genv.genv_instrs ge. *)
(* Proof. *)
(*   intros. unfold add_external_global. *)
(*   cbn. auto. *)
(* Qed. *)

(* Lemma add_external_globals_pres_instrs : forall extfuns stbl ge, *)
(*     Genv.genv_instrs (add_external_globals extfuns ge stbl) = Genv.genv_instrs ge. *)
(* Proof. *)
(*   induction stbl; simpl; intros. *)
(*   - auto. *)
(*   - etransitivity.  *)
(*     rewrite IHstbl; eauto. *)
(*     eapply add_external_global_pres_instrs; eauto. *)
(* Qed. *)

(* Hint Resolve in_eq in_cons. *)

(* Definition only_internal_symbol i stbl :=  *)
(*     (forall e, In e stbl -> symbentry_id e = i -> is_symbentry_internal e = true). *)

(* Lemma add_external_globals_pres_find_symbol : forall extfuns stbl ge i, *)
(*     only_internal_symbol i stbl -> *)
(*     Genv.find_symbol (add_external_globals extfuns ge stbl) i = Genv.find_symbol ge i. *)
(* Proof. *)
(*   unfold only_internal_symbol. *)
(*   induction stbl as [|e stbl]; intros; simpl. *)
(*   - auto. *)
(*   - etransitivity. *)
(*     erewrite IHstbl; eauto. *)
(*     unfold add_external_global. *)
(*     unfold Genv.find_symbol. cbn. *)
(*     destr; eauto. *)
(*     destruct (peq (symbentry_id e) i). *)
(*     + subst.  *)
(*       generalize (H e (in_eq _ _) eq_refl). *)
(*       congruence. *)
(*     + erewrite PTree.gso; eauto. *)
(* Qed. *)

(* Lemma add_external_globals_pres_find_symbol' : forall extfuns stbl ge i, *)
(*     ~ In i (get_symbentry_ids stbl) -> *)
(*     Genv.find_symbol (add_external_globals extfuns ge stbl) i = Genv.find_symbol ge i. *)
(* Proof. *)
(*   intros extfuns stbl ge i NIN. *)
(*   eapply add_external_globals_pres_find_symbol; eauto. *)
(*   red. intros e IN EQ. subst. *)
(*   exfalso. eapply NIN.  *)
(*   eapply in_map; eauto. *)
(* Qed. *)

(* Lemma add_external_globals_pres_ext_funs: *)
(*   forall (stbl : symbtable) (extfuns : PTree.t external_function) (ge : Genv.t) (i : ident), *)
(*     Pos.lt i (Genv.genv_next ge) -> *)
(*     (Genv.genv_ext_funs (add_external_globals extfuns ge stbl)) ! i = (Genv.genv_ext_funs ge) ! i. *)
(* Proof. *)
(*   induction stbl as [| e stbl]. *)
(*   - intros extfuns ge i LT. *)
(*     cbn. auto. *)
(*   - intros extfuns ge i LT. *)
(*     cbn. *)
(*     erewrite IHstbl; eauto. *)
(*     + unfold add_external_global; cbn. *)
(*       repeat (destr; auto).  *)
(*       rewrite PTree.gso; auto. *)
(*       xomega. *)
(*     + unfold add_external_global; cbn. *)
(*       destr; xomega. *)
(* Qed. *)


(* Definition find_symbol_block_bound ge := *)
(*   forall id b ofs, Genv.find_symbol ge id = Some (b, ofs) -> Pos.lt b (Genv.genv_next ge). *)

(* Lemma add_global_pres_find_symbol_block_bound: forall extfuns ge e, *)
(*   find_symbol_block_bound ge -> find_symbol_block_bound (add_external_global extfuns ge e). *)
(* Proof. *)
(*   unfold find_symbol_block_bound. intros. *)
(*   unfold add_external_global in *. cbn in *. *)
(*   unfold Genv.find_symbol in H0. cbn in H0. *)
(*   destr. *)
(*   - eapply H; eauto. *)
(*   - destruct (peq (symbentry_id e) id). *)
(*     + subst. rewrite PTree.gss in H0. inv H0. *)
(*       apply Plt_succ. *)
(*     + rewrite PTree.gso in H0; auto. *)
(*       apply Plt_trans_succ; auto.  *)
(*       eapply H; eauto. *)
(* Qed. *)

(* Lemma add_external_globals_pres_find_symbol_block_bound: forall stbl extfuns ge, *)
(*   find_symbol_block_bound ge -> find_symbol_block_bound (add_external_globals extfuns ge stbl). *)
(* Proof. *)
(*   induction stbl; intros; simpl. *)
(*   - auto. *)
(*   - apply IHstbl. apply add_global_pres_find_symbol_block_bound. auto. *)
(* Qed. *)


(* Definition sec_index_to_block (i:N) : block := *)
(*   match i with *)
(*   | N0 => 1%positive *)
(*   | Npos p => p *)
(*   end. *)

(* Definition acc_symb_map (e:symbentry) (m:PTree.t (block * ptrofs)) := *)
(*   let id := symbentry_id e in *)
(*   match symbentry_secindex e with *)
(*   | secindex_normal i => *)
(*     let b := sec_index_to_block i in *)
(*     let ofs := Ptrofs.repr (symbentry_value e) in *)
(*     PTree.set id (b,ofs) m *)
(*   | _ => m *)
(*   end. *)

(* Definition gen_symb_map (t:symbtable) : PTree.t (block * ptrofs) := *)
(*   fold_right acc_symb_map (PTree.empty (block * ptrofs)) t. *)

Definition acc_instr_map r (i:instruction) :=
  let '(ofs, map) := r in
  let map' := fun o => if Ptrofs.eq_dec ofs o then Some i else (map o) in
  let ofs' := Ptrofs.add ofs (Ptrofs.repr (instr_size i)) in
  (ofs', map').

Definition gen_instr_map (c:code) :=
  let '(_, map) := fold_left acc_instr_map c (Ptrofs.zero, fun o => None) in
  map.

Definition acc_code_map r (id:ident) (sec:section) :=
  match sec with
  | sec_text c =>
    NMap.set _ (Global id) (gen_instr_map c) r
  | _ => r
  end.

Definition gen_code_map (sectbl: sectable) :=
  PTree.fold acc_code_map sectbl (NMap.init _ (fun o => None)).

Definition acc_extfuns (idg: ident * gdef) extfuns :=
  let '(id, gdef) := idg in
  match gdef with
  | Gfun (External ef) => NMap.set  _ (Global id) (Some ef) extfuns
  | _ => extfuns
  end.

Definition gen_extfuns (idgs: list (ident * gdef)) :=
  fold_right acc_extfuns (NMap.init _ None) idgs.

(* Lemma PTree_Properteis_of_list_get_extfuns : forall defs i f, *)
(*     list_norepet (map fst defs) -> *)
(*     (PTree_Properties.of_list defs) ! i = (Some (Gfun (External f))) -> *)
(*     (gen_extfuns defs) ! i = Some f. *)
(* Proof. *)
(*   induction defs as [|def defs]. *)
(*   - cbn. intros. rewrite PTree.gempty in H0. congruence. *)
(*   - intros i f NORPT OF. destruct def as (id, def). *)
(*     inv NORPT. *)
(*     destruct (ident_eq id i). *)
(*     + subst. erewrite PTree_Properties_of_list_cons in OF; auto. *)
(*       inv OF. cbn. *)
(*       rewrite PTree.gss. auto. *)
(*     + erewrite PTree_Properties_of_list_tail in OF; eauto. *)
(*       cbn. repeat (destr; eauto; subst). *)
(*       erewrite PTree.gso; auto. *)
(* Qed. *)

Definition globalenv (p: program) : Genv.t :=
  let symbmap := gen_symb_map (prog_symbtable p) in
  let imap := gen_code_map (prog_sectable p) in
  let extfuns := gen_extfuns p.(prog_defs) in
  Genv.mkgenv symbmap extfuns imap p.(prog_senv).
  
(* Definition globalenv (p: program) : Genv.t := *)
(*   let symbmap := gen_symb_map (prog_symbtable p) in *)
(*   let imap := gen_instr_map' (SecTable.get sec_code_id (prog_sectable p)) in *)
(*   let nextblock := 4%positive in *)
(*   let genv := Genv.mkgenv symbmap  *)
(*                           (PTree.empty external_function)  *)
(*                           imap  *)
(*                           nextblock  *)
(*                           (prog_senv p) in *)
(*   let extfuns := gen_extfuns p.(prog_defs) in *)
(*   add_external_globals extfuns genv p.(prog_symbtable). *)



(** Initialization of memory *)
Section WITHGE1.

Variable ge:Genv.t.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge gloc ofs)
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Definition alloc_external_symbol (r: option mem) (id: ident) (e:symbentry): option mem :=
  match r with
  | None => None
  | Some m =>
  match symbentry_type e with
  | symb_notype =>
    match symbentry_secindex e with
    | secindex_undef =>
      let (m1, b) := Mem.alloc_glob id m 0 0 in Some m1
    | _ => None
    end
  | symb_func =>
    match symbentry_secindex e with
    | secindex_undef =>
      let (m1, b) := Mem.alloc_glob id m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty        
    | secindex_comm => 
      None (**r Impossible *)
    | secindex_normal _ => Some m
    end
  | symb_data =>
    match symbentry_secindex e with
    | secindex_undef
    | secindex_comm => 
      let sz := symbentry_size e in
      let (m1, b) := Mem.alloc_glob id m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        Mem.drop_perm m2 b 0 sz Nonempty
      end        
    | secindex_normal _ => Some m
    end
  end
  end.

Definition alloc_external_symbols (m: mem) (t: symbtable) : option mem :=
  PTree.fold alloc_external_symbol t (Some m).

(* Definition store_internal_global (b:block) (ofs:Z) (m: mem) (idg: ident * option gdef): option (mem * Z) := *)
(*   let '(id, gdef) := idg in *)
(*   match gdef with *)
(*   | Some (Gvar v) => *)
(*     if is_var_internal v then *)
(*       let init := gvar_init v in *)
(*       let isz := init_data_list_size init in *)
(*       match Globalenvs.store_zeros m b ofs isz with *)
(*       | None => None *)
(*       | Some m1 => *)
(*         match store_init_data_list m1 b ofs init with *)
(*         | None => None *)
(*         | Some m2 =>  *)
(*           match Mem.drop_perm m2 b ofs (ofs+isz) (Globalenvs.Genv.perm_globvar v) with *)
(*           | None => None *)
(*           | Some m3 => Some (m3, ofs + isz) *)
(*           end *)
(*         end *)
(*       end *)
(*     else *)
(*       Some (m, ofs) *)
(*   | _ => Some (m, ofs) *)
(*   end. *)

(* Definition acc_store_internal_global b r (idg: ident * option gdef) := *)
(*   match r with *)
(*   | None => None *)
(*   | Some (m, ofs) => *)
(*     store_internal_global b ofs m idg *)
(*   end. *)

(* Definition store_internal_globals (b:block) (m: mem) (gl: list (ident * option gdef))  *)
(*   : option mem := *)
(*   match fold_left (acc_store_internal_global b) gl (Some (m, 0)) with *)
(*   | None => None *)
(*   | Some (m',_) => Some m' *)
(*   end. *)

Definition get_symbol_type (symbtbl: symbtable) (id: ident) :=
  match symbtbl!id with
  | Some e =>
    Some (e.(symbentry_type))
  | _ => None
  end.


Definition alloc_section (symbtbl: symbtable) (r: option mem) (id: ident) (sec: section) : option mem :=
  match r with
  | None => None
  | Some m =>
    let sz := sec_size instr_size sec in
    (**r Assume section ident corresponds to a symbol entry *)
    match get_symbol_type symbtbl id with
    | Some ty =>
      match sec, ty with
      | sec_data init, symb_rwdata =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Writable
          end       
        end
      | sec_data init, symb_rodata =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Readable
          end
        end
      | sec_text code, symb_func =>        
        let (m1, b) := Mem.alloc_glob id m 0 sz in
        Mem.drop_perm m1 b 0 sz Nonempty
      | _, _ => None                 
      end
    | None => None
    end
  end.

Definition alloc_sections (symbtbl: symbtable) (sectbl: sectable) (m:mem) :option mem :=
  PTree.fold (alloc_section symbtbl) sectbl (Some m).

(* Definition alloc_rodata_section (t:sectable) (m:mem) : option mem := *)
(*   match SecTable.get sec_rodata_id t with *)
(*   | None => None *)
(*   | Some sec => *)
(*     let sz := (sec_size sec) in *)
(*     match sec with *)
(*     | sec_data init => *)
(*       let '(m1, b) := Mem.alloc m 0 sz in *)
(*       match store_zeros m1 b 0 sz with *)
(*       | None => None *)
(*       | Some m2 => *)
(*         match store_init_data_list m2 b 0 init with *)
(*         | None => None *)
(*         | Some m3 => Mem.drop_perm m3 b 0 sz Readable *)
(*         end *)
(*       end *)
(*     | _ => None *)
(*     end *)
(*   end. *)

(* Definition alloc_data_section (t:sectable) (m:mem) : option mem := *)
(*   match SecTable.get sec_data_id t with *)
(*   | None => None *)
(*   | Some sec => *)
(*     let sz := (sec_size sec) in *)
(*     match sec with *)
(*     | sec_data init => *)
(*       let '(m1, b) := Mem.alloc m 0 sz in *)
(*       match store_zeros m1 b 0 sz with *)
(*       | None => None *)
(*       | Some m2 => *)
(*         match store_init_data_list m2 b 0 init with *)
(*         | None => None *)
(*         | Some m3 => Mem.drop_perm m3 b 0 sz Writable *)
(*         end *)
(*       end *)
(*     | _ => None *)
(*     end *)
(*   end. *)

(* Definition alloc_code_section (t:sectable) (m:mem) : option mem := *)
(*   match SecTable.get sec_code_id t with *)
(*   | None => None *)
(*   | Some sec => *)
(*     let sz := sec_size sec in *)
(*     let (m1, b) := Mem.alloc m 0 sz in *)
(*     Mem.drop_perm m1 b 0 sz Nonempty *)
(*   end. *)

End WITHGE1.

Definition init_mem (p: program) :=
  let ge := globalenv p in
  match alloc_sections ge p.(prog_symbtable) p.(prog_sectable) Mem.empty with
  | Some m1 =>
    alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.
  
(* Definition init_mem (p: program) := *)
(*   let ge := globalenv p in *)
(*   let stbl := prog_sectable p in *)
(*   match alloc_rodata_section ge stbl Mem.empty with *)
(*   | None => None *)
(*   | Some m1 => *)
(*     match alloc_data_section ge stbl m1 with *)
(*     | None => None *)
(*     | Some m2 => *)
(*       match alloc_code_section stbl m2 with *)
(*       | None => None *)
(*       | Some m3 => *)
(*         alloc_external_symbols m3 (prog_symbtable p) *)
(*       end *)
(*     end *)
(*   end. *)

(** Properties about init_mem *)

Lemma store_init_data_nextblock : forall v ge m b ofs m',
  store_init_data ge m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v; simpl in *; try now (eapply Mem.nextblock_store; eauto).
  inv H. auto.
Qed.
    
Lemma store_init_data_list_nextblock : forall l ge m b ofs m',
  store_init_data_list ge m b ofs l = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_nextblock; eauto.
    exploit IHl; eauto. intros. congruence.
Qed.

(* Lemma alloc_rodata_section_nextblock: forall ge stbl m m', *)
(*   alloc_rodata_section ge stbl m = Some m' -> Mem.nextblock m' = Pos.succ (Mem.nextblock m). *)
(* Proof. *)
(*   intros ge stbl m m' ALLOC. *)
(*   unfold alloc_rodata_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.nextblock_alloc; eauto. *)
(*   intros NB1. *)
(*   exploit Globalenvs.Genv.store_zeros_nextblock; eauto. *)
(*   intros NB2. *)
(*   exploit store_init_data_list_nextblock; eauto. *)
(*   intros NB3. *)
(*   exploit Mem.nextblock_drop; eauto. *)
(*   intros NB4.  *)
(*   congruence. *)
(* Qed. *)

(* Lemma alloc_data_section_nextblock: forall ge stbl m m', *)
(*   alloc_data_section ge stbl m = Some m' -> Mem.nextblock m' = Pos.succ (Mem.nextblock m). *)
(* Proof. *)
(*   intros ge stbl m m' ALLOC. *)
(*   unfold alloc_data_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.nextblock_alloc; eauto. *)
(*   intros NB1. *)
(*   exploit Globalenvs.Genv.store_zeros_nextblock; eauto. *)
(*   intros NB2. *)
(*   exploit store_init_data_list_nextblock; eauto. *)
(*   intros NB3. *)
(*   exploit Mem.nextblock_drop; eauto. *)
(*   intros NB4.  *)
(*   congruence. *)
(* Qed. *)

(* Lemma alloc_code_section_nextblock: forall stbl m m', *)
(*   alloc_code_section stbl m = Some m' -> Mem.nextblock m' = Pos.succ (Mem.nextblock m). *)
(* Proof. *)
(*   intros stbl m m' ALLOC. *)
(*   unfold alloc_code_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.nextblock_alloc; eauto. *)
(*   intros NB1. *)
(*   exploit Mem.nextblock_drop; eauto. *)
(*   intros NB2. congruence. *)
(* Qed. *)


(* Definition num_of_external_symbs (tbl:SymbTable.t) := *)
(*   length (filter (fun s => negb (is_symbentry_internal s)) tbl). *)

(* Lemma alloc_external_symbol_nextblock1 : forall e m m', *)
(*   is_symbentry_internal e = false -> *)
(*   alloc_external_symbol m e = Some m' ->  *)
(*   Mem.nextblock m' = Pos.succ (Mem.nextblock m). *)
(* Proof. *)
(*   intros e m m' SI ALLOC. *)
(*   unfold alloc_external_symbol in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(*   - erewrite Mem.nextblock_drop; eauto. *)
(*     erewrite Mem.nextblock_alloc; eauto. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(*   - erewrite Mem.nextblock_drop; eauto. *)
(*     erewrite Genv.store_zeros_nextblock; eauto. *)
(*     erewrite Mem.nextblock_alloc; eauto. *)
(*   - erewrite Mem.nextblock_drop; eauto. *)
(*     erewrite Genv.store_zeros_nextblock; eauto. *)
(*     erewrite Mem.nextblock_alloc; eauto. *)
(*   - erewrite Mem.nextblock_alloc; eauto. *)
(* Qed. *)

(* Lemma alloc_external_symbol_nextblock2 : forall e m m', *)
(*   is_symbentry_internal e = true -> *)
(*   alloc_external_symbol m e = Some m' ->  *)
(*   Mem.nextblock m' = Mem.nextblock m. *)
(* Proof. *)
(*   intros e m m' SI ALLOC. *)
(*   unfold alloc_external_symbol in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(*   - unfold is_symbentry_internal in SI. *)
(*     rewrite Heqs0 in SI. congruence. *)
(* Qed. *)

(* Lemma alloc_external_symbols_nextblock: forall tbl m1 m, *)
(*   alloc_external_symbols m1 tbl = Some m -> *)
(*   Mem.nextblock m = pos_advance_N (Mem.nextblock m1) (num_of_external_symbs tbl). *)
(* Proof. *)
(*   induction tbl; intros; inv H. *)
(*   - auto. *)
(*   - destr_match_in H1; inv H1. *)
(*     simpl.  *)
(*     exploit IHtbl; eauto. intros NB. *)
(*     destruct (is_symbentry_internal a) eqn:SI.     *)
(*     + exploit alloc_external_symbol_nextblock2; eauto. *)
(*       intros NB1. *)
(*       cbn. rewrite SI. cbn.  *)
(*       rewrite NB. f_equal. auto. *)
(*     + exploit alloc_external_symbol_nextblock1; eauto. *)
(*       intros NB1. *)
(*       cbn. rewrite SI. cbn. *)
(*       rewrite NB. f_equal. auto. *)
(* Qed. *)

(* Lemma add_external_global_nextblock1: forall ge extfuns e, *)
(*     is_symbentry_internal e = false -> *)
(*     Genv.genv_next (add_external_global extfuns ge e) =  *)
(*     Pos.succ (Genv.genv_next ge). *)
(* Proof. *)
(*   intros ge extfuns e SI. *)
(*   unfold add_external_global. *)
(*   rewrite SI. cbn. auto. *)
(* Qed.   *)

(* Lemma add_external_global_nextblock2: forall ge extfuns e, *)
(*     is_symbentry_internal e = true -> *)
(*     Genv.genv_next (add_external_global extfuns ge e) =  *)
(*     Genv.genv_next ge. *)
(* Proof. *)
(*   intros ge extfuns e SI. *)
(*   unfold add_external_global. *)
(*   rewrite SI. cbn. auto. *)
(* Qed. *)

(* Lemma add_external_globals_nextblock: forall tbl ge extfuns, *)
(*   Genv.genv_next (add_external_globals extfuns ge tbl) =  *)
(*   pos_advance_N (Genv.genv_next ge) (num_of_external_symbs tbl). *)
(* Proof. *)
(*   induction tbl; intros; simpl. *)
(*   - auto. *)
(*   - rewrite IHtbl.  *)
(*     destruct (is_symbentry_internal a) eqn:SI. *)
(*     + erewrite add_external_global_nextblock2; eauto. *)
(*       cbn. rewrite SI. cbn. auto. *)
(*     + erewrite add_external_global_nextblock1; eauto. *)
(*       cbn. rewrite SI. cbn. auto. *)
(* Qed. *)


(* Lemma init_mem_genv_next: forall (p: program) m, *)
(*   init_mem p = Some m -> *)
(*   Genv.genv_next (globalenv p) = Mem.nextblock m. *)
(* Proof. *)
(*   unfold init_mem; intros. *)
(*   destruct (Mem.alloc Mem.empty 0 0) eqn:ALLOC. *)
(*   destr_match_in H; inv H. destr_in H1. destr_in H1.  *)
(*   exploit alloc_rodata_section_nextblock; eauto. intros NB1. *)
(*   rewrite Mem.nextblock_empty in NB1. cbn in NB1. *)
(*   exploit alloc_data_section_nextblock; eauto. intros NB2. *)
(*   exploit alloc_code_section_nextblock; eauto. intros NB3. *)
(*   exploit alloc_external_symbols_nextblock; eauto. intros NB4. *)
(*   unfold globalenv. *)
(*   erewrite add_external_globals_nextblock. cbn. *)
(*   rewrite NB1 in NB2. rewrite NB2 in NB3. cbn in NB3. congruence. *)
(* Qed. *)


(* Lemma store_init_data_stack : forall v ge (m m' : mem) (b : block) (ofs : Z), *)
(*        store_init_data ge m b ofs v = Some  m' -> Mem.stack (Mem.support m') = Mem.stack (Mem.support m). *)
(* Proof. *)
(*   intros v ge0 m m' b ofs H. destruct v; simpl in *; try (now eapply Mem.store_stack_unchanged; eauto). *)
(*   inv H. auto. *)
(* Qed. *)

(* Lemma store_init_data_list_stack : forall l ge (m m' : mem) (b : block) (ofs : Z), *)
(*        store_init_data_list ge m b ofs l = Some m' -> Mem.stack m' = Mem.stack m. *)
(* Proof. *)
(*   induction l; intros. *)
(*   - simpl in H. inv H. auto. *)
(*   - simpl in H. destr_match_in H; inv H. *)
(*     exploit store_init_data_stack; eauto. *)
(*     exploit IHl; eauto. *)
(*     intros. congruence. *)
(* Qed. *)

(* Lemma alloc_external_symbol_stack: forall e m m', *)
(*     alloc_external_symbol m e = Some m' -> Mem.stack m = Mem.stack m'. *)
(* Proof. *)
(*   intros e m m' ALLOC. *)
(*   unfold alloc_external_symbol in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   - exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*     exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*     congruence. *)
(*   - exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*     exploit Genv.store_zeros_stack; eauto. *)
(*     exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*     congruence. *)
(*   - exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*     exploit Genv.store_zeros_stack; eauto. *)
(*     exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*     congruence. *)
(*   - exploit Mem.alloc_stack_unchanged; eauto.  *)
(* Qed. *)

    
(* Lemma alloc_external_symbols_stack: forall stbl m m', *)
(*     alloc_external_symbols m stbl = Some m' -> Mem.stack m = Mem.stack m'. *)
(* Proof. *)
(*   induction stbl; inversion 1. *)
(*   - inv H. auto. *)
(*   - destr_match_in H1; inv H1. *)
(*     exploit alloc_external_symbol_stack; eauto. *)
(*     intros STKEQ. rewrite STKEQ. *)
(*     erewrite IHstbl; eauto. *)
(* Qed. *)

(* Lemma alloc_rodata_section_stack: forall ge stbl m m', *)
(*     alloc_rodata_section ge stbl m = Some m' ->  *)
(*     Mem.stack m = Mem.stack m'. *)
(* Proof. *)
(*   intros ge stbl m m' ALLOC. *)
(*   unfold alloc_rodata_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*   exploit store_init_data_list_stack; eauto. *)
(*   exploit Genv.store_zeros_stack; eauto. *)
(*   exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*   congruence. *)
(* Qed. *)

(* Lemma alloc_data_section_stack: forall ge stbl m m', *)
(*     alloc_data_section ge stbl m = Some m' ->  *)
(*     Mem.stack m = Mem.stack m'. *)
(* Proof. *)
(*   intros ge stbl m m' ALLOC. *)
(*   unfold alloc_data_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*   exploit store_init_data_list_stack; eauto. *)
(*   exploit Genv.store_zeros_stack; eauto. *)
(*   exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*   congruence. *)
(* Qed. *)

(* Lemma alloc_code_section_stack: forall stbl m m', *)
(*     alloc_code_section stbl m = Some m' ->  *)
(*     Mem.stack m = Mem.stack m'. *)
(* Proof. *)
(*   intros stbl m m' ALLOC. *)
(*   unfold alloc_code_section in ALLOC. *)
(*   repeat destr_in ALLOC. *)
(*   exploit Mem.drop_perm_stack_unchanged; eauto. *)
(*   exploit Mem.alloc_stack_unchanged; eauto. intros. *)
(*   congruence. *)
(* Qed. *)

(* Lemma init_mem_stack: *)
(*   forall p m, *)
(*     init_mem p = Some m -> *)
(*     Mem.stack m = nil. *)
(* Proof. *)
(*   intros. unfold init_mem in H. *)
(*   repeat destr_in H. *)
(*   erewrite <- alloc_external_symbols_stack; eauto. *)
(*   erewrite <- alloc_code_section_stack; eauto. *)
(*   erewrite <- alloc_data_section_stack; eauto. *)
(*   erewrite <- alloc_rodata_section_stack; eauto. *)
(*   erewrite Mem.empty_stack; eauto. *)
(* Qed. *)



Section INITDATA.

Variable ge: Genv.t.

Remark store_init_data_perm:
  forall k prm b' q i b m p m',
  store_init_data ge m b p i = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. 
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem.
  destruct i; simpl in H; eauto. 
  inv H; tauto.
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl b m p m',
  store_init_data_list ge m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q k prm). 
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.

Lemma store_init_data_exists:
  forall m b p i,
    Mem.range_perm m b p (p + init_data_size i) Cur Writable ->
    (* Mem.stack_access (Mem.stack m) b p (p + init_data_size i)  -> *)
    (Genv.init_data_alignment i | p) ->
    (* (forall id ofs, i = Init_addrof id ofs -> exists b, find_symbol ge id = Some b) -> *)
    exists m', store_init_data ge m b p i = Some m'.
Proof.
  intros. 
  assert (DFL: forall chunk v,
          init_data_size i = size_chunk chunk ->
          Genv.init_data_alignment i = align_chunk chunk ->
          exists m', Mem.store chunk m b p v = Some m').
  { intros. destruct (Mem.valid_access_store m chunk b p v) as (m' & STORE).
    split. rewrite <- H1; auto.
    rewrite  <- H2. auto.
    exists m'; auto. }
  destruct i; eauto.
  simpl. exists m; auto.
Qed.

(* SACC
Lemma store_init_data_stack_access:
  forall m b p i1 m1,
    store_init_data ge m b p i1 = Some m1 ->
    forall b' lo hi,
      stack_access (Mem.stack m1) b' lo hi <-> stack_access (Mem.stack m) b' lo hi.
Proof.
  unfold store_init_data.
  destruct i1; intros; try now (eapply Mem.store_stack_access ; eauto).
  inv H; tauto.
Qed.
*)

Lemma store_init_data_list_exists:
  forall b il m p,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
  (* stack_access (Mem.stack m) b p (p + init_data_list_size il) -> *)
  Genv.init_data_list_aligned p il ->
  (* (forall id ofs, In (Init_addrof id ofs) il -> exists b, find_symbol ge id = Some b) -> *)
  exists m', store_init_data_list ge m b p il = Some m'.
Proof.
  induction il as [ | i1 il ]; simpl; intros.
- exists m; auto.
- destruct H0. 
  destruct (@store_init_data_exists m b p i1) as (m1 & S1); eauto.
  red; intros. apply H. generalize (init_data_list_size_pos il); lia.
  (* generalize (init_data_list_size_pos il); omega. *)
  rewrite S1.
  apply IHil; eauto.
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); lia.
Qed.

End INITDATA.

Inductive initial_state_gen (p: program) (rs: regset) m: state -> Prop :=
| initial_state_gen_intro:
    forall m1 m2 stk
      (MALLOC: Mem.alloc m 0 (max_stacksize + align (size_chunk Mptr) 8) = (m1,stk))
      (MST: Mem.storev Mptr m1 (Vptr stk (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m2),
      let ge := (globalenv p) in
      let rs0 :=
          rs # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr)))) in
      initial_state_gen p rs m (State rs0 m2).


(** Execution of whole programs. *)
(* Inductive initial_state_gen (p: program) (rs: regset) m: state -> Prop := *)
(*   | initial_state_gen_intro: *)
(*       forall m1 m2 m3 bstack m4 *)
(*       (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1,bstack)) *)
(*       (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit + align (size_chunk Mptr) 8) Writable = Some m2) *)
(*       (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3) *)
(*       (MST: Mem.storev Mptr m3 (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m4), *)
(*       let ge := (globalenv p) in *)
(*       let rs0 := *)
(*         rs # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero) *)
(*            # RA <- Vnullptr *)
(*            # RSP <- (Vptr bstack (Ptrofs.sub (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr)))) in *)
(*       initial_state_gen p rs m (State rs0 m4). *)

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m,
    init_mem prog = Some m ->
    initial_state_gen prog rs m s ->
    initial_state prog rs s.

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

(* Local Existing Instance mem_accessors_default. *)

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen step (initial_state p rs) final_state (globalenv p) (Genv.genv_senv (globalenv p)).

(** Determinacy of the [Asm] semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
(* + discriminate. *)
(* + discriminate. *)
(* + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0. *)
(*   exploit external_call_determ. eexact H5. eexact H11. intros [A B]. *)
(*   split. auto. intros. destruct B; auto. subst. auto. *)
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H7. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  (* eapply external_call_trace_length; eauto. *)
- (* initial states *)
  inv H; inv H0. assert (m = m0) by congruence. subst. inv H2; inv H3.
  assert (m1 = m3 /\ stk = stk0) by intuition congruence. destruct H0; subst.
  assert (m2 = m4) by congruence. subst.
  f_equal. (* congruence. *)
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. simpl. intros s t s' STEP.
  inv STEP; simpl. lia.
  eapply external_call_trace_length; eauto.
  (* eapply external_call_trace_length; eauto. *)
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists. eapply exec_step_internal; eauto.
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    (* eexists. eapply exec_step_builtin; eauto. *)
    (* edestruct external_call_receptive as (vres2 & m2 & EC2); eauto. *)
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.
Qed.

End WITH_INSTR_SIZE.
