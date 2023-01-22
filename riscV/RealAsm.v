Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import Floats.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.

Section INSTRSIZE.
Variable instr_size : instruction -> Z.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

  (* only eliminate the f argument here, not complete *)
  (** TODO: eliminate pseudo instructions and semantics for additional instructions *)
  Definition exec_instr (i: instruction) (rs: regset) (m: mem) : outcome :=
  let sz := Ptrofs.repr (instr_size i) in
  let nextinstr := nextinstr sz in
  let exec_load := exec_load ge sz in
  let exec_store := exec_store ge sz in
  match i with
  | Pmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit integer register-immediate instructions *)
  | Paddiw d s i =>
      Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m
  | Psltiw d s i =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m
  | Psltiuw d s i =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m
  | Pandiw d s i =>
      Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m
  | Poriw d s i =>
      Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m
  | Pxoriw d s i =>
      Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m
  | Pslliw d s i =>
      Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m
  | Psrliw d s i =>
      Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m
  | Psraiw d s i =>
      Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m
  | Pluiw d i =>
      Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m

(** 32-bit integer register-register instructions *)
  | Paddw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m
  | Psubw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m
  | Pmulw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m
  | Pmulhw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m
  | Pmulhuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m
  | Pdivw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m
  | Pdivuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m
  | Premw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m
  | Premuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m
  | Psltw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m
  | Psltuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m
  | Pseqw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m
  | Psnew d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m
  | Pandw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m
  | Porw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m
  | Pxorw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m
  | Psllw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m
  | Psrlw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
  | Psraw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m

(** 64-bit integer register-immediate instructions *)
  | Paddil d s i =>
      Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m
  | Psltil d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m
  | Psltiul d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m
  | Pandil d s i =>
      Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m
  | Poril d s i =>
      Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m
  | Pxoril d s i =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m
  | Psllil d s i =>
      Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m
  | Psrlil d s i =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m
  | Psrail d s i =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m
  | Pluil d i =>
      Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m

(** 64-bit integer register-register instructions *)
  | Paddl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
  | Psubl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
  | Pmull d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
  | Pmulhl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m
  | Pmulhul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m
  | Pdivl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m
  | Pdivul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m
  | Preml d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m
  | Premul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m
  | Psltl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m
  | Psltul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m
  | Pseql d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m
  | Psnel d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m
  | Pandl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
  | Porl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m
  | Pxorl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m
  | Pslll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
  | Psrll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
  | Psral d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m

  | Pcvtl2w d s =>
      Next (nextinstr (rs#d <- (Val.loword rs##s))) m
  | Pcvtw2l r =>
      Next (nextinstr (rs#r <- (Val.longofint rs#r))) m

(** Unconditional jumps.  Links are always to X1/RA. *)
  (* | Pj_l l => *)
  (*     goto_label f l rs m *)
  | Pj_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pj_r r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pjal_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
              #RA <- (Val.offset_ptr rs#PC (Ptrofs.repr (instr_size i)))
           ) m
  | Pjal_r r sg =>
      Next (rs#PC <- (rs#r)
              #RA <- (Val.offset_ptr rs#PC (Ptrofs.repr (instr_size i)))
           ) m

(** Loads and stores *)
  | Plb d a ofs =>
      exec_load Mint8signed rs m d a ofs
  | Plbu d a ofs =>
      exec_load Mint8unsigned rs m d a ofs
  | Plh d a ofs =>
      exec_load Mint16signed rs m d a ofs
  | Plhu d a ofs =>
      exec_load Mint16unsigned rs m d a ofs
  | Plw d a ofs =>
      exec_load Mint32 rs m d a ofs
  | Plw_a d a ofs =>
      exec_load Many32 rs m d a ofs
  | Pld d a ofs =>
      exec_load Mint64 rs m d a ofs
  | Pld_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Psb s a ofs =>
      exec_store Mint8unsigned rs m s a ofs
  | Psh s a ofs =>
      exec_store Mint16unsigned rs m s a ofs
  | Psw s a ofs =>
      exec_store Mint32 rs m s a ofs
  | Psw_a s a ofs =>
      exec_store Many32 rs m s a ofs
  | Psd s a ofs =>
      exec_store Mint64 rs m s a ofs
  | Psd_a s a ofs =>
      exec_store Many64 rs m s a ofs

(** Floating point register move *)
  | Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit (single-precision) floating point *)
  | Pfls d a ofs =>
      exec_load Mfloat32 rs m d a ofs
  | Pfss s a ofs =>
      exec_store Mfloat32 rs m s a ofs

  | Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtswu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m

  | Pfcvtls d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtlus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m
  | Pfcvtsl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtslu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m

(** 64-bit (double-precision) floating point *)
  | Pfld d a ofs =>
      exec_load Mfloat64 rs m d a ofs
  | Pfld_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Pfsd s a ofs =>
      exec_store Mfloat64 rs m s a ofs
  | Pfsd_a s a ofs =>
      exec_store Many64 rs m s a ofs

  | Pfnegd d s =>
      Next (nextinstr (rs#d <- (Val.negf rs#s))) m
  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtdwu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m

  | Pfcvtld d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtlud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m
  | Pfcvtdl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m
  | Pfcvtdlu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m

  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

(** Pseudo-instructions *)
  | Pallocframe sz pos =>
    if zle 0 sz then
      match rs # PC with
      |Vptr (Global id) _
       =>
       let (m0,path) := Mem.alloc_frame m id in
       let (m1, stk) := Mem.alloc m0 0 sz in
       match Mem.record_frame (Mem.push_stage m1) (Memory.mk_frame sz) with
       |None => Stuck
       |Some m2 =>
        let sp := Vptr stk Ptrofs.zero in
        match Mem.storev Mptr m2 (Val.offset_ptr sp pos) rs#SP with
        | None => Stuck
        | Some m3 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m3
        end
       end
     |_ => Stuck
      end
    else Stuck
      (* let (m1, stk) := Mem.alloc m 0 sz in *)
      (* let sp := (Vptr stk Ptrofs.zero) in *)
      (* match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with *)
      (* | None => Stuck *)
      (* | Some m2 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2 *)
      (* end *)
  | Pfreeframe sz pos =>
    (* if zle 0 sz then *)
    (*   match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with *)
    (*   | None => Stuck *)
    (*   | Some sp => *)
    (*     match rs#SP with *)
    (*     | Vptr stk ofs => *)
    (*       if check_topframe sz (Mem.astack (Mem.support m)) then *)
    (*         if Val.eq sp (parent_sp_stree (Mem.stack (Mem.support m))) then *)
    (*           if Val.eq (Vptr stk ofs) (top_sp_stree (Mem.stack (Mem.support m))) then *)
    (*               match Mem.free m stk 0 fsz with *)
    (*               | None => Stuck *)
    (*               | Some m' => *)
    (*                 match Mem.return_frame m' with *)
    (*                 | None => Stuck *)
    (*                 | Some m'' => *)
    (*                   match Mem.pop_stage m'' with *)
    (*                     | None => Stuck *)
    (*                     | Some m''' => *)
    (*                     Next (nextinstr (rs#RSP <- sp #RA <- ra)) m''' *)
    (*                   end *)
    (*                 end *)
    (*               end else Stuck else Stuck else Stuck *)
    (*           | _ => Stuck *)
    (*           end *)
    (*       end *)
    (*   end else Stuck *)
    
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd s ofs =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m
  | Ploadsymbol_high rd s ofs =>
      Next (nextinstr (rs#rd <- (high_half ge s ofs))) m
  | Ploadli rd i =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vlong i))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vsingle f))) m
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pfence

  | Pfmvxs _ _
  | Pfmvsx _ _
  | Pfmvxd _ _
  | Pfmvdx _ _

  | Pfmins _ _ _
  | Pfmaxs _ _ _
  | Pfsqrts _ _
  | Pfmadds _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmsubs _ _ _ _

  | Pfmind _ _ _
  | Pfmaxd _ _ _
  | Pfsqrtd _ _
  | Pfmaddd _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubd _ _ _ _
  | Pnop
  | _
    => Stuck
  end.


Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs#X31 <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').


End WITHGE.


Definition semantics p :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma semantics_determinate: forall p, determinate (semantics p).
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
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Some Auxilary lemmas *)

Lemma code_size_app:
    forall c1 c2,
      code_size instr_size (c1 ++ c2) = code_size instr_size c1 + code_size instr_size c2.
  Proof.
    induction c1; simpl; intros; eauto. rewrite IHc1. lia.
  Qed.
  
End INSTRSIZE.
