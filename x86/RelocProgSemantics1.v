(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 6, 2019  *)
(* *******************  *)

(** * The semantics of relocatable program using both the symbol and the relocation tables *)

(** The key feature of this semantics: it uses mappings from the
    offsets of global symbols in their corresponding sections to
    memory locations in deciding their memory addresses. These
    mappings are calculated by using both the symobl and the
    relocation tables *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require RelocProgSemantics Reloctablesgen.
Require Import LocalLib.
(** Global environments *)

Definition gdef := globdef Asm.fundef unit.

Module Genv.

Section GENV.

Record t: Type := mkgenv {
  genv_reloc_ofs_symb: PTree.t (ZTree.t ident);
  genv_genv : RelocProgSemantics.Genv.t;
}.

(** ** Lookup functions *)

Definition find_symbol (ge: t) (sec_index: ident) (idofs: Z) : option (block * ptrofs):=
  let ge' := ge.(genv_genv) in
  match ge.(genv_reloc_ofs_symb) ! sec_index with
  | Some  ofs_map =>
    match ZTree.get idofs ofs_map with
    | None => None
    | Some id => RelocProgSemantics.Genv.find_symbol ge' id
    end
  | _ => None
  end.


Definition symbol_address (ge: t) (sec_index: ident) (idofs: Z) (ofs: ptrofs) : val :=
  match find_symbol ge sec_index idofs with
  | Some (b, o) => Vptr b (Ptrofs.add ofs o)
  | None => Vundef
  end.

Definition find_ext_funct (ge: t) (v:val) : option external_function :=
  RelocProgSemantics.Genv.find_ext_funct (genv_genv ge) v.

(* Lemma symbol_address_offset : forall ge ofs1 b s ofs, *)
(*     symbol_address ge s Ptrofs.zero = Vptr b ofs -> *)
(*     symbol_address ge s ofs1 = Vptr b (Ptrofs.add ofs ofs1). *)
(* Proof. *)
(*   unfold symbol_address. intros.  *)
(*   destruct (find_symbol ge s) eqn:FSM. *)
(*   -  *)
(*     destruct p. *)
(*     inv H. *)
(*     rewrite Ptrofs.add_zero_l. rewrite Ptrofs.add_commut. auto. *)
(*   -  *)
(*     inv H. *)
(* Qed. *)

(* Lemma find_sym_to_addr : forall (ge:t) id b ofs, *)
(*     find_symbol ge id = Some (b, ofs) -> *)
(*     symbol_address ge id Ptrofs.zero = Vptr b ofs. *)
(* Proof. *)
(*   intros. unfold symbol_address. rewrite H. *)
(*   rewrite Ptrofs.add_zero_l. auto. *)
(* Qed. *)

Definition find_instr (ge: t) (v:val) : option instruction :=
  RelocProgSemantics.Genv.find_instr (genv_genv ge) v.

(* Definition to_reloc_prog_genv (ge:t) := genv_genv ge. *)

End GENV.

End Genv.

(* Coercion Genv.to_reloc_prog_genv: Genv.t >-> RelocProgSemantics.Genv.t. *)

(** Evaluating an addressing mode *)

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
Section WITH_SEC_ID.
Variable sec_id :ident.    
  
Section WITHGE.

Variable ge: Genv.t.


Definition eval_addrmode32 (idofs: option Z) (a: addrmode) (rs: regset) : val :=
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
            | inr(id, ofs) => 
              match idofs with
              | None => Vundef
              | Some idofs =>
                Genv.symbol_address ge sec_id idofs ofs
              end
            end)).

Definition eval_addrmode64 (idofs:option Z) (a: addrmode) (rs: regset) : val :=
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
            | inr(id, ofs) => 
              match idofs with
              | None => Vundef
              | Some idofs =>
                Genv.symbol_address ge sec_id idofs ofs
              end
            end)).

Definition eval_addrmode (idofs: option Z) (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 idofs a rs else eval_addrmode32 idofs a rs.

End WITHGE.

Definition exec_load (sz:ptrofs) (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                     (idofs: option Z) (a: addrmode) (rs: regset) 
                     (rd: preg):=
  match Mem.loadv chunk m (eval_addrmode ge idofs a rs) with
  | Some v => Next (nextinstr_nf sz (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (sz:ptrofs) (ge: Genv.t) (chunk: memory_chunk) (m: mem)
                      (idofs: option Z) (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg):=
  match Mem.storev chunk m (eval_addrmode ge idofs a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf sz (undef_regs destroyed rs)) m'
  | None => Stuck
  end.

Open Scope asm.

(* Definition eval_ros (ge : Genv.t) (idofs: option Z) (ros : ireg + ident) (rs : regset) := *)
(*   match ros with *)
(*   | inl r => rs r *)
(*   | inr _ =>  *)
(*     match idofs with *)
(*     | None => Vundef *)
(*     | Some idofs => Genv.symbol_address ge RELOC_CODE idofs Ptrofs.zero *)
(*     end *)
(*   end. *)

(** Execution of instructions *)

Definition get_pc_offset (rs:regset) : option Z :=
  match rs#PC with
  | Vptr _ ofs => Some (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition id_reloc_offset sofs (i:instruction) : option Z :=
  match Reloctablesgen.instr_reloc_offset i with
  | Error _ => None
  | OK ofs => Some (sofs + ofs)
  end.

Definition exec_instr (ge: Genv.t) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match get_pc_offset rs with
  | None => Stuck
  | Some ofs => 
    let sz := Ptrofs.repr (instr_size i) in 
    let idofs := id_reloc_offset ofs i in
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
      match idofs with
      | None => Stuck
      | Some idofs => 
        let symbaddr := (Genv.symbol_address ge sec_id idofs Ptrofs.zero) in
        Next (nextinstr_nf (rs#rd <- symbaddr) ) m
      end
    | Pmovl_rm rd a =>
      exec_load ge Mint32 m idofs a rs rd 
    | Pmovq_rm rd a =>
      exec_load ge Mint64 m idofs a rs rd 
    | Pmovl_mr a r1 =>
      exec_store ge Mint32 m idofs a rs r1 nil 
    | Pmovq_mr a r1 =>
      exec_store ge Mint64 m idofs a rs r1 nil 
    | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) ) m
    | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) ) m
    | Pmovsd_fm rd a =>
      exec_load ge Mfloat64 m idofs a rs rd  
    | Pmovsd_mf a r1 =>
      exec_store ge Mfloat64 m idofs a rs r1 nil 
    | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) ) m
    | Pmovss_fm rd a =>
      exec_load ge Mfloat32 m idofs a rs rd 
    | Pmovss_mf a r1 =>
      exec_store ge Mfloat32 m idofs a rs r1 nil 
    | Pfldl_m a =>
      exec_load ge Mfloat64 m idofs a rs ST0 
    | Pfstpl_m a =>
      exec_store ge Mfloat64 m idofs a rs ST0 (ST0 :: nil) 
    | Pflds_m a =>
      exec_load ge Mfloat32 m idofs a rs ST0 
    | Pfstps_m a =>
      exec_store ge Mfloat32 m idofs a rs ST0 (ST0 :: nil) 
    (* | Pxchg_rr r1 r2 => *)
    (*   Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) ) m *)
    (** Moves with conversion *)
    | Pmovb_mr a r1 =>
      exec_store ge Mint8unsigned m idofs a rs r1 nil 
    | Pmovw_mr a r1 =>
      exec_store ge Mint16unsigned m idofs a rs r1 nil 
    | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) ) m
    | Pmovzb_rm rd a =>
      exec_load ge Mint8unsigned m idofs a rs rd 
    | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) ) m
    | Pmovsb_rm rd a =>
      exec_load ge Mint8signed m idofs a rs rd 
    | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) ) m
    | Pmovzw_rm rd a =>
      exec_load ge Mint16unsigned m idofs a rs rd 
    | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) ) m
    | Pmovsw_rm rd a =>
      exec_load ge Mint16signed m idofs a rs rd 
    | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1)) ) m
    | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1)) ) m
    | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd)) ) m
    | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1)) ) m
    | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1)) ) m
    | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1))) ) m
    | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1))) ) m
    | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1))) ) m
    | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1))) ) m
    | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1))) ) m
    | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1))) ) m
    | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1))) ) m
    | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1))) ) m
    (** Integer arithmetic *)
    | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge idofs a rs)) ) m
    | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge idofs a rs)) ) m
    | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd)) ) m
    | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd)) ) m
    | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n))) ) m
    | Psubl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n))) ) m
    | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n))) ) m
    | Psubq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd (Vlong n))) ) m
    | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1)) ) m
    | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1)) ) m
    | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1)) ) m
    | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1)) ) m
    | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n))) ) m
    | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n))) ) m
    | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1)) ) m
    | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1)) ) m
    | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1)) ) m
    | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1)) ) m
    | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) ) m
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
      RelocProgSemantics.goto_ofs sz  ofs rs m
    | Pjmp_s _ sg =>
      match idofs with
      | None => Stuck
      | Some idofs =>
        let symbaddr := (Genv.symbol_address ge sec_id idofs Ptrofs.zero) in
        Next (rs#PC <- symbaddr) m
      end
    | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
    | Pjcc_rel cond ofs =>
      match eval_testcond cond rs with
      | Some true => RelocProgSemantics.goto_ofs sz ofs rs m
      | Some false => Next (nextinstr rs ) m
      | None => Stuck
      end
    | Pjcc2_rel cond1 cond2 ofs =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => RelocProgSemantics.goto_ofs sz ofs rs m
      | Some _, Some _ => Next (nextinstr rs ) m
      | _, _ => Stuck
      end
    | Pjmptbl_rel r tbl =>
      match rs#r with
      | Vint n =>
        match list_nth_z tbl (Int.unsigned n) with
        | None => Stuck
        | Some ofs => RelocProgSemantics.goto_ofs sz ofs (rs #RAX <- Vundef #RDX <- Vundef) m
        end
      | _ => Stuck
      end
    | Pcall_s _ _ =>
      match idofs with
      | None => Stuck
      | Some idofs => 
        let addr := Genv.symbol_address ge sec_id idofs Ptrofs.zero in
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
        match Mem.storev Mptr m sp (Val.offset_ptr rs#PC sz) with
        | None => Stuck
        | Some m2 =>
          Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                          #PC <- addr
                                  #RSP <- sp) m2
        end
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
    (* | Pcall (inr gloc) sg => *)
    (*     Next (rs#RA <- (Val.offset_ptr rs#PC ) #PC <- (Genv.symbol_address ge gloc Ptrofs.zero)) m *)
    (* | Pcall (inl r) sg => *)
    (*     Next (rs#RA <- (Val.offset_ptr rs#PC ) #PC <- (rs r)) m *)
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
      exec_load ge (if Archi.ptr64 then Many64 else Many32) m idofs a rs rd 
    | Pmov_mr_a a r1 =>
      exec_store ge (if Archi.ptr64 then Many64 else Many32) m idofs a rs r1 nil 
    | Pmovsd_fm_a rd a =>
      exec_load ge Many64 m idofs a rs rd 
    | Pmovsd_mf_a a r1 =>
      exec_store ge Many64 m idofs a rs r1 nil 
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
    end
  end.

End WITH_SEC_ID.
(** * Evaluation of builtin arguments *)

(* Section EVAL_BUILTIN_ARG. *)

(* Variable A: Type. *)

(* Variable ge: Genv.t. *)
(* Variable idofs: option Z. *)
(* Variable e: A -> val. *)
(* Variable sp: val. *)
(* Variable m:mem.  *)

(* Inductive eval_builtin_arg: builtin_arg A -> val -> Prop := *)
(*   | eval_BA: forall x, *)
(*       eval_builtin_arg (BA x) (e x) *)
(*   | eval_BA_int: forall n, *)
(*       eval_builtin_arg (BA_int n) (Vint n) *)
(*   | eval_BA_long: forall n, *)
(*       eval_builtin_arg (BA_long n) (Vlong n) *)
(*   | eval_BA_float: forall n, *)
(*       eval_builtin_arg (BA_float n) (Vfloat n) *)
(*   | eval_BA_single: forall n, *)
(*       eval_builtin_arg (BA_single n) (Vsingle n) *)
(*   | eval_BA_loadstack: forall chunk ofs v, *)
(*       Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v -> *)
(*       eval_builtin_arg (BA_loadstack chunk ofs) v *)
(*   | eval_BA_addrstack: forall ofs, *)
(*       eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs) *)
(*   | eval_BA_loadglobal: forall chunk id idofs' ofs v, *)
(*       idofs = Some idofs' -> *)
(*       Mem.loadv chunk m  (Genv.symbol_address ge RELOC_CODE idofs' ofs) = Some v -> *)
(*       eval_builtin_arg (BA_loadglobal chunk id ofs) v *)
(*   | eval_BA_addrglobal: forall id ofs idofs', *)
(*       idofs = Some idofs' -> *)
(*       eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge RELOC_CODE idofs' ofs) *)
(*   | eval_BA_splitlong: forall hi lo vhi vlo, *)
(*       eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo -> *)
(*       eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo). *)

(* Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop := *)
(*   list_forall2 eval_builtin_arg al vl. *)

(* Lemma eval_builtin_arg_determ: *)
(*   forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v. *)
(* Proof. *)
(*   induction 1; intros v' EV; inv EV; try congruence. *)
(*   f_equal; eauto. *)
(* Qed. *)

(* Lemma eval_builtin_args_determ: *)
(*   forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl. *)
(* Proof. *)
(*   induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ. *)
(* Qed. *)

(* End EVAL_BUILTIN_ARG. *)


(** Small step semantics *)

Inductive step (ge: Genv.t) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs i rs m rs' m' sec_id,
      rs PC = Vptr b ofs ->
      b = Global sec_id ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some i ->
      exec_instr sec_id ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
(* | exec_step_builtin: *)
(*     forall b ofs ef args res rs m vargs t vres rs' m' idofs, *)
(*       rs PC = Vptr b ofs -> *)
(*       Genv.find_ext_funct ge (Vptr b ofs) = None -> *)
(*       Genv.find_instr ge (Vptr b ofs) = Some (Pbuiltin ef args res)  -> *)
(*       id_reloc_offset (Ptrofs.unsigned ofs) (Pbuiltin ef args res) = idofs -> *)
(*       eval_builtin_args preg ge idofs rs (rs RSP) m args vargs -> *)
(*       external_call ef (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge)) vargs m t vres m' -> *)
(*         rs' = nextinstr_nf *)
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
        external_call ef (RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge)) args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)
                                      (undef_regs (map preg_of destroyed_at_call) rs)))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
        step ge (State rs m) t (State rs' m').

(** Initialization of the global environment *)

(* Given relocentry [e] and symtable [stbl], updates the mapping [m] that
associates relocation offsets with their identifiers. *)
Definition acc_reloc_ofs_symb (e:relocentry) (m:ZTree.t ident) : ZTree.t ident :=
  ZTree.set (reloc_offset e) (reloc_symb e) m.


Definition gen_reloc_ofs_symb (rtbl: reloctable) : ZTree.t ident :=
  fold_right (acc_reloc_ofs_symb) (ZTree.empty ident) rtbl.

(* Definition add_reloc_ofs_symb (stbl: symbtable) (i:reloctable_id)  (rmap: reloctable_map) *)
(*            (ofsmap: reloctable_id -> ZTree.t ident) := *)
(*   let rtbl := get_reloctable i rmap in *)
(*   let m := gen_reloc_ofs_symb stbl rtbl in *)
(*   fun i' => if reloctable_id_eq i i' then m else ofsmap i'. *)

(* Definition gen_reloc_ofs_symbs (p:program) := *)
(*   let stbl := p.(prog_symbtable) in *)
(*   let rmap := p.(prog_reloctables) in *)
(*   let ofsmap := fun i => ZTree.empty ident in *)
(*   let ofsmap1 := add_reloc_ofs_symb stbl RELOC_RODATA rmap ofsmap in *)
(*   let ofsmap2 := add_reloc_ofs_symb stbl RELOC_DATA rmap ofsmap1 in *)
(*   let ofsmap3 := add_reloc_ofs_symb stbl RELOC_CODE rmap ofsmap2 in *)
(*   ofsmap3. *)

Definition gen_reloc_ofs_symbs (p:program) :=
  PTree.map1 gen_reloc_ofs_symb p.(prog_reloctables).

Definition globalenv (p: program) : Genv.t :=
  let ofsmap := gen_reloc_ofs_symbs p in
  let genv1 := RelocProgSemantics.globalenv instr_size p in
  Genv.mkgenv ofsmap genv1.


(** Initialization of memory *)
Section WITHGE1.

Variable ge:Genv.t.


Definition store_init_data (sec_id: ident) (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge sec_id p ofs)
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (sec_id: ident) (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data sec_id m b p id with
      | None => None
      | Some m' => store_init_data_list sec_id m' b (p + init_data_size id) idl'
      end
  end.

Definition alloc_section (symbtbl: symbtable) (r: option mem) (id: ident) (sec: section) : option mem :=
  match r with
  | None => None
  | Some m =>
    let sz := sec_size instr_size sec in
    (**r Assume section ident corresponds to a symbol entry *)
    match RelocProgSemantics.get_symbol_type symbtbl id with
    | Some ty =>
      match sec, ty with
      | sec_data init, symb_rwdata =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list id m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Writable
          end
        end
      | sec_data init, symb_rodata =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list id m2 b 0 init with
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

End WITHGE1.

Definition init_mem (p: program) :=
  let ge := globalenv p in
  match alloc_sections ge p.(prog_symbtable) p.(prog_sectable) Mem.empty with
  | Some m1 =>
    RelocProgSemantics.alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.


(* (** Execution of whole programs. *) *)
(* Inductive initial_state_gen (p: program) (rs: regset) m: state -> Prop := *)
(*   | initial_state_gen_intro: *)
(*       forall m1 m2 m3 bstack m4 *)
(*       (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1,bstack)) *)
(*       (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit + align (size_chunk Mptr) 8) Writable = Some m2) *)
(*       (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3) *)
(*       (MST: Mem.storev Mptr m3 (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m4), *)
(*       let ge := (globalenv p) in *)
(*       let rs0 := *)
(*         rs # PC <- (RelocProgSemantics.Genv.symbol_address (Genv.genv_genv ge)  *)
(*                                                           p.(prog_main) Ptrofs.zero) *)
(*            # RA <- Vnullptr *)
(*            # RSP <- (Vptr bstack (Ptrofs.sub (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr)))) in *)
(*       initial_state_gen p rs m (State rs0 m4). *)

(* Inductive initial_state (prog: program) (rs: regset) (s: state): Prop := *)
(* | initial_state_intro: forall m, *)
(*     init_mem prog = Some m -> *)
(*     initial_state_gen prog rs m s -> *)
(*     initial_state prog rs s. *)

(* Inductive final_state: state -> int -> Prop := *)
(*   | final_state_intro: forall rs m r, *)
(*       rs#PC = Vnullptr -> *)
(*       rs#RAX = Vint r -> *)
(*       final_state (State rs m) r. *)

(* Local Existing Instance mem_accessors_default. *)

Definition genv_senv (ge:Genv.t) :=
  RelocProgSemantics.Genv.genv_senv (Genv.genv_genv ge).

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen step (RelocProgSemantics.initial_state instr_size p rs) (RelocProgSemantics.final_state) (globalenv p) 
                (genv_senv (globalenv p)).

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
(* + unfold exec_instr in H4. destr_in H4; discriminate. *)
(* + unfold exec_instr in H12. destr_in H12; discriminate. *)
(* + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0. *)
(*   exploit external_call_determ. eexact H6. eexact H12. intros [A B]. *)
(*   split. auto. intros. destruct B; auto. subst. auto. *)
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H7. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  (* eapply external_call_trace_length; eauto. *)
- (* initial states *)
  inv H; inv H0. assert (m = m0) by congruence. subst. inv H2; inv H3.  assert (m1 = m3 /\ stk = stk0) by intuition congruence. destruct H0; subst.
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
  inv STEP; simpl. omega.
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
    (* edestruct external_call_receptive as (vres2 & m2 & EC2); eauto. *)
    (* eexists. eapply exec_step_builtin; eauto. *)
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.
Qed.

End WITH_INSTR_SIZE.
