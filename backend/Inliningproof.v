(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** RTL function inlining: semantic preservation *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Inlining Inliningspec.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section INLINING.

Variable fn_stack_requirements : ident -> Z.
Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto.
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. extlia.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Pos.lt_le_trans. apply shiftpos_below. extlia.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star (step fn_stack_requirements) tge (State stk f sp pc1 rs1 m)
               E0 (State stk f sp pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply not_eq_sym. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
  range_private F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. lia. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Z.max sz 0) hi.
Proof.
  intros; red; intros.
  exploit (H ofs). generalize (Z.le_max_r sz 0). lia. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); lia.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
  range_private F m m' sp (base + Z.max sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros.
  destruct (zlt ofs (base + Z.max sz 0)) as [z|z].
  red; split.
  replace ofs with ((ofs - base) + base) by lia.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. lia.

  exploit (H ofs). lia. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (Mem.sup_dec b (Mem.support m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto.
Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (support: sup): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, sup_In b support-> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> sup_In b2 support -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> sup_In b support)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> sup_In b support)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> sup_In b support).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' support,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F support ->
  exists cu fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef (funenv_program cu) fd = OK fd' /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  assert (EQ: rs'#(sreg ctx r) = rs#r).
  { exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: Val.inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd.
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  }
  rewrite EQ. eapply functions_translated; eauto.
- (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

Lemma find_inlined_function:
  forall fenv id rs fd f,
  fenv_compat prog fenv ->
  find_function ge (inr id) rs = Some fd ->
  fenv!id = Some f ->
  fd = Internal f.
Proof.
  intros.
  apply H in H1. apply Genv.find_def_symbol in H1. destruct H1 as (b & A & B).
  simpl in H0. unfold ge, fundef in H0. rewrite A in H0.
  rewrite <- Genv.find_funct_ptr_iff in B.
  congruence.
Qed.

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F support ctx rs rs' sp sp' m m',
  match_globalenvs F support ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add ofs (Ptrofs.repr (dstk ctx)))).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
- econstructor; split. constructor. simpl. econstructor; eauto. rewrite ! Ptrofs.add_zero_l; auto.
- assert (Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  inv MG. econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall F support ctx rs rs' sp sp' m m',
  match_globalenvs F support ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (F: meminj) (m m': mem):
             list nat -> list stackframe -> list stackframe -> sup -> Prop :=
  | match_stacks_nil: forall support1 support
        (MG: match_globalenvs F support1)
        (BELOW: Mem.sup_include support1 support),
      match_stacks F m m' nil nil nil support
  | match_stacks_cons: forall res f sp pc rs stk f' sps' sp' rs' stk' support fenv ctx n l
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Mem.sup_include (sup_incr sps') support),
      match_stacks F m m' (S n::l)
                   (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk')
                   support
  | match_stacks_untailcall: forall stk res f' sps' sp' rpc rs' stk' support ctx n l
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l stk stk' f' ctx sps' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Mem.sup_include (sup_incr sps') support),
      match_stacks F m m' (n::l)
                   stk
                   (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk')
                   support

with match_stacks_inside (F: meminj) (m m': mem):
        nat -> list nat -> list stackframe -> list stackframe -> function -> context -> sup -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sps' rs' l
        (MS: match_stacks F m m' l stk stk' sps')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' 0 l stk stk' f' ctx sps' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sps' sp' rs' ctx' n l
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l stk stk' f' ctx' sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' (S n) l
                          (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                          stk' f' ctx sps' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' support l,
  match_stacks F m m' l stk stk' support -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs' n l,
  match_stacks_inside F m m' n l stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx sp rs' n l,
  match_stacks_inside F m m' n l stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A].
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_support:
  forall stk stk' support support1 l,
  match_stacks F m m' l stk stk' support ->
  Mem.sup_include support support1 ->
  match_stacks F m m' l stk stk' support1.
Proof.
  intros. inv H.
  apply match_stacks_nil with support0. auto. eapply Mem.sup_include_trans; eauto.
  eapply match_stacks_cons; eauto. eapply Mem.sup_include_trans; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply Mem.sup_include_trans; eauto.
Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.
Lemma match_stacks_invariant:
  forall stk stk' support l, match_stacks F m m' l stk stk' support ->
  forall (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> sup_In b2 support -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> sup_In b2 support ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, sup_In b support->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, sup_In b support->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1'  l stk stk' support

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sps' rs1 n l,
  match_stacks_inside F m m' n l stk stk' f' ctx sps' rs1 ->
  forall rs2 sp'
         (SPS: sp' = fresh_block sps')
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> sup_In b2 (sup_incr sps') -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> sup_In b2 (sup_incr sps') ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, sup_In b (sup_incr sps') ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, sup_In b (sup_incr sps') ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' n l stk stk' f' ctx sps' rs2.

Proof.
  induction 1; intros; subst.
  (* nil *)
  apply match_stacks_nil with (support1 := support1).
  inv MG. constructor; auto.
  intros. apply IMAGE with delta. eapply INJ; eauto. auto. eapply Mem.sup_include_trans; eauto. apply Mem.sup_include_refl.
  (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx) (sps' := sps'); auto.
  eapply match_stacks_inside_invariant; eauto.
(*  intros; eapply INJ; eauto. apply BELOW. right. auto.
  intros; eapply PERM1; eauto. apply BELOW. right. auto.
  intros; eapply PERM2; eauto. apply BELOW. right. auto.
  intros; eapply PERM3; eauto. apply BELOW. right. auto. *)
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros. split. eapply INJ; eauto.
  eapply PERM1; eauto.
  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx) (sps' := sps'); auto.
  eapply match_stacks_inside_invariant; eauto.
 (* intros; eapply INJ; eauto. apply BELOW. right. auto.
  intros; eapply PERM1; eauto. apply BELOW. right. auto.
  intros; eapply PERM2; eauto. apply BELOW. right. auto.
  intros; eapply PERM3; eauto. apply BELOW. right. auto. *)
  eapply range_private_invariant; eauto.
  intros. split. eapply INJ; eauto.
  eapply PERM1; eauto.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros; eapply INJ; eauto. apply Mem.sup_incr_in2. auto.
  intros; eapply PERM1; eauto. apply Mem.sup_incr_in2. auto.
  intros; eapply PERM2; eauto. apply Mem.sup_incr_in2. auto.
  intros; eapply PERM3; eauto. apply Mem.sup_incr_in2. auto.
  (* inlined *)
  subst sp'0.
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx') (sp' := sp'); auto.
  apply IHmatch_stacks_inside with (sp':= fresh_block sps'); auto.
  intros. apply RS. red in BELOW. extlia.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. extlia.
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. subst sp'. auto. eapply PERM1; eauto. subst sp'. auto.
    intros. eapply PERM2; eauto. subst sp'. auto.
Qed.

Lemma match_stacks_empty:
  forall stk stk' support l,
  match_stacks F m m' l stk stk' support -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs n l,
  match_stacks_inside F m m' n l stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v n l,
  match_stacks_inside F m m' n l stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' n l stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto.
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' stk stk' f' ctx sp' rs' res v n l,
  match_stacks_inside F m m' n l stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' n l stk stk' f' ctx sp' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1' n l,
  match_stacks_inside F m m' n l stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' n l stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sps' sp' rs' n l,
  match_stacks_inside F m m' n l stk stk' f' ctx sps' rs' ->
  sp' = fresh_block sps' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' n l stk stk' f' ctx sps' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H2 in H5; inv H5. eelim freshness; eauto.
  rewrite H3 in H5; auto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H2 in H5. inv H5. eelim freshness; eauto.
  (* inlined *)
  subst sp'0. subst sp'.
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. lia.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H3 in H0; inv H0. elimtype False; extlia.
  rewrite H4 in H0; auto.
Qed.

Lemma match_stacks_record_frame_left:
  forall F m m' l stk stk' sp',
  match_stacks F m m' l stk stk' sp' ->
  forall f m1,
    Mem.record_frame m f = Some m1 ->
    match_stacks F m1 m' l stk stk' sp'.
Proof.
  intros.
  eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_record_frame; eauto.
Qed.

Lemma match_stacks_inside_record_frame_left:
  forall F m m' n l stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' n l stk stk' f' ctx sp' rs' ->
  forall f m1,
    Mem.record_frame m f = Some m1 ->
    match_stacks_inside F m1 m' n l stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto.
  intros. eapply Mem.perm_record_frame; eauto.
Qed.


(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1 l,
  match_stacks F m m' l stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' l stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sps sp lo hi m1' l,
  match_stacks F m m' l stk stk' sps ->
  sp = fresh_block sps ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' l stk stk' sps.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_1; eauto with ordered_type.
  left.  subst sp. intro. subst b. eapply freshness; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Z.divide_trans with 4; auto. exists 2; auto.
    apply Z.divide_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). auto.
    apply Z.divide_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). extlia.
    auto.
  destruct chunk; simpl in *; auto.
  apply Z.divide_1_l.
  apply Z.divide_1_l.
  apply H2; lia.
  apply H2; lia.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.

Lemma match_stacks_extcall:
  forall stk stk' support l,
  match_stacks F1 m1 m1' l stk stk' support ->
  Mem.sup_include support (Mem.support m1') ->
  match_stacks F2 m2 m2' l stk stk' support
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' sps' rs' n l,
  match_stacks_inside F1 m1 m1' n l stk stk' f' ctx sps' rs' ->
  sp' = fresh_block sps' ->
  Mem.sup_include (sup_incr sps') (Mem.support m1') ->
  match_stacks_inside F2 m2 m2' n l stk stk' f' ctx sps' rs'.
Proof.
  induction 1; intros; subst.
  apply match_stacks_nil with support1; auto.
    inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    exploit SEP; eauto. intros [A B]. elim B. red. auto.
  eapply match_stacks_cons; eauto.
    eapply match_stacks_inside_extcall; eauto. eapply Mem.sup_include_trans; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. red. apply H. apply BELOW. auto.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red. apply H. apply BELOW. auto.
  eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_extcall; eauto. eapply Mem.sup_include_trans; eauto.
    eapply range_private_extcall; eauto. red. apply H. apply BELOW. auto.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red. apply H. apply BELOW. auto.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. eapply Mem.sup_include_trans; eauto.
    subst sp'0. subst sp'.
  eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto.
    apply H1. auto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). lia. lia.
Qed.
Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' n l stk stk' f' ctx sps' sp' rs' ctx' f,
  sp' = fresh_block sps' ->
  match_stacks_inside F m m' n l stk stk' f' ctx sps' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' n l stk stk' f' ctx' sps' rs'.
Proof.
  intros. inv H0.
  (* base *)
  eapply match_stacks_inside_base.  eauto. congruence.
  rewrite H2. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Z.divide_0_r.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H2. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply H4. inv H5. extlia.
  congruence.
  unfold context_below in *. extlia.
  unfold context_stack_call in *. lia.
Qed.

Definition meminj_global (j:meminj) : Prop :=
  forall id b delta, j (Global id) = Some (b,delta) ->
                b = Global id /\ delta = 0.

Inductive inline_depth : list nat -> nat -> nat -> Prop :=
  | depth_nil : inline_depth nil 0 0
  | depth_cons l d1 d2 n:
      inline_depth l (d1 - (S n)) d2 ->
      inline_depth (S n::l) d1 (S d2).

Section TAKEDROP.
  Context {A: Type}.

  Fixpoint take (n: nat) (l: list A) : option (list A) :=
    match n with
    | O => Some nil
    | S m => match l with
            | h::t =>
               match take m t with
                 Some r => Some (h::r)
               | None => None
               end
            | _ => None
            end
    end.

  Fixpoint drop (n: nat) (l: list A) : list A :=
    match n with
    | O => l
    | S m => drop m (tl l)
    end.

  Lemma take_drop:
    forall n l t,
      take n l = Some t ->
      l = t ++ drop n l.
  Proof.
    induction n; simpl; intros; eauto. inv H. reflexivity.
    repeat destr_in H. simpl. f_equal. eauto.
  Qed.

  Lemma take_succeeds:
    forall n l,
      (n <= length l)%nat ->
      exists t, take n l = Some t.
  Proof.
    induction n; simpl; intros; eauto.
    destr; simpl in *. lia.
    edestruct (IHn l0) as (t & EQ). lia.
    rewrite EQ. eauto.
  Qed.

  Lemma take_succeeds_inv:
    forall n l t,
      take n l = Some t ->
      (n <= length l)%nat.
  Proof.
    induction n; simpl; intros; eauto. lia.
    repeat destr_in H.
    apply IHn in Heqo. simpl. lia.
  Qed.

  Lemma drop_length:
    forall n l,
      (n <= length l)%nat ->
      length (drop n l) = (length l - n)%nat.
  Proof.
    induction n; simpl; intros; eauto. lia.
    destruct l; simpl in *; try lia.
    rewrite IHn; lia.
  Qed.

  Lemma take_length:
    forall n l t,
      take n l = Some t ->
      length t = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; auto.
    repeat destr_in H. simpl. erewrite IHn; eauto.
  Qed.

  Variable P: A -> Prop.

  Lemma take_forall:
    forall n l t,
      Forall P l ->
      take n l = Some t ->
      Forall P t.
  Proof.
    intros.
    rewrite (take_drop _ _ _ H0) in H.
    rewrite Forall_forall in H.
    rewrite Forall_forall. intros; apply H. rewrite in_app. auto.
  Qed.

  Lemma drop_forall:
    forall n l,
      Forall P l ->
      Forall P (drop n l).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn. inv H; simpl; auto.
  Qed.

End TAKEDROP.

Section INLINE_SIZES.

Inductive inline_sizes : list nat -> Memory.stackadt -> Memory.stackadt -> Prop :=
| inline_sizes_nil: inline_sizes nil nil nil
| inline_sizes_cons g s1 s2 t1 n t2:
    inline_sizes g (drop (S n) s1) s2 ->
    nth_error s1 n = Some t1 ->
    Memory.size_of_all_frames t2 <= Memory.size_of_all_frames t1 ->
    inline_sizes (S n::g) s1 (t2 :: s2).

Lemma inline_sizes_up:
  forall g s1 s2,
    inline_sizes g s1 s2 ->
    inline_sizes (1%nat :: g) (nil::s1) (nil::s2).
Proof.
  intros. econstructor; simpl; eauto. simpl. lia.
Qed.

Lemma inline_sizes_upstar:
  forall n g s1 s2 ,
    inline_sizes (n :: g) s1 s2 ->
    inline_sizes (S n :: g) ((nil) :: s1) s2.
Proof.
  intros n g s1 s2 SZ.
  inv SZ.
  econstructor; simpl; eauto.
Qed.

Lemma inline_sizes_upright:
  forall g n f1 s1 s2,
    inline_sizes (S (S n) :: g) (f1::s1) s2 ->
    inline_sizes (1%nat :: S n :: g) (f1 :: s1)  (nil::s2).
Proof.
  intros g n f1 s1 s2 IS. inv IS.
  simpl in *. repeat destr_in H2.
  repeat econstructor; eauto. simpl.
  apply Memory.size_of_all_frames_pos.
Qed.

Lemma inline_sizes_record:
  forall g t1 s1 t2 s2 fr
    (SZ: inline_sizes (1%nat::g) (t1 :: s1) (t2 :: s2)),
    inline_sizes (1%nat::g) ((fr::t1) :: s1) ((fr::t2) :: s2).
Proof.
  intros. inv SZ.
  simpl in *. inv H5.
  econstructor; simpl; eauto. simpl.
  lia.
Qed.

Lemma inline_sizes_record':
  forall g t1 s1 t2 s2 fr
    (SZ: inline_sizes (1%nat::g) (t1 :: s1) (t2 :: s2)),
    inline_sizes (1%nat::g) ((fr:: t1) :: s1) ((fr:: t2) :: s2).
Proof.
  intros. inv SZ.
  simpl in *. inv H5.
  econstructor; simpl; eauto. simpl. lia.
Qed.

Lemma inline_sizes_record_left:
  forall g t1 s1 s2 fr
    (SIZES: inline_sizes g (t1 :: s1) s2),
    inline_sizes g ((fr:: t1) :: s1) s2.
Proof.
  intros. inv SIZES.
  destruct n; simpl in *. inv H0.
  econstructor; simpl; auto. etransitivity. apply H1.
  simpl. generalize (Memory.frame_size_a_pos fr). intro. lia.
  econstructor; simpl; eauto.
Qed.

Lemma inline_sizes_down:
  forall g s1 s2,
    inline_sizes (1%nat::g) s1 s2 ->
    inline_sizes g (tl s1) (tl s2).
Proof.
  intros. inv H. simpl in *; auto.
Qed.

Lemma inline_sizes_downstar:
  forall g n s1 s2,
    inline_sizes (S (S n) :: g) s1 s2 ->
    inline_sizes (S n :: g) (tl s1) s2.
Proof.
  intros. inv H. simpl in *. repeat destr_in H3.
  econstructor; simpl; eauto.
Qed.

Lemma nth_error_take:
  forall {A} n n' (s s': list A) t,
    lt n n' ->
    take n' s = Some s' ->
    nth_error s n = Some t ->
    nth_error s' n = Some t.
Proof.
  induction n; simpl; intros; eauto.
  repeat destr_in H1.
  destruct n'; simpl in *. lia. repeat destr_in H0. auto.
  destruct n'. lia. simpl in *. repeat destr_in H0.
  eapply IHn. 2: eauto. lia. auto.
Qed.

Lemma stage_size_le_stack_size:
  forall t s,
    In t s ->
    Memory.size_of_all_frames t <= Memory.stack_size s.
Proof.
  induction s; simpl; intros; eauto. lia.
  destruct H; subst. generalize (Memory.stack_size_pos s); lia.
  generalize (Memory.size_of_all_frames_pos a). apply IHs in H. lia.
Qed.

Lemma inline_sizes_le:
  forall g s1 s2
    (SIZES: inline_sizes g s1 s2),
    Memory.stack_size s2 <= Memory.stack_size s1.
Proof.
  induction 1; simpl; intros; eauto. lia.
  destruct (take_succeeds (S n) s1) as (t & TAKE).
  eapply nth_error_Some; eauto. congruence.
  rewrite (take_drop _ _ _ TAKE).
  rewrite Memory.stack_size_app.
  cut (Memory.size_of_all_frames t2 <= Memory.stack_size t). intros; lia.
  etransitivity. apply H0.
  eapply stage_size_le_stack_size; eauto.
  eapply nth_error_take in H; eauto.
  eapply nth_error_In; eauto.
Qed.

Lemma inline_sizes_tl_le:
  forall g s1 s2,
    inline_sizes (1%nat::g) s1 s2 ->
    Memory.stack_size (tl s2) <= Memory.stack_size (tl s1).
Proof.
  intros g s1 s2 SZ.
  eapply inline_sizes_le.
  apply inline_sizes_down. eauto.
Qed.

End INLINE_SIZES.


(** ** Relating states *)

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sps' sp' rs' m' F fenv ctx n l
        (SPS: sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (GLOB: meminj_global F)
        (MINJ: Mem.inject F m m')
        (STREE: inline_depth (S n::l) ((Mem.sdepth m)) ((Mem.sdepth m')))
        (SIZES: inline_sizes (S n :: l) (Mem.astack (Mem.support m)) (Mem.astack(Mem.support m')))
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (State stk f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')
  | match_call_states: forall stk fd args m stk' fd' args' m' cunit F id l
        (MS: match_stacks F m m' l stk stk' (Mem.support m'))
        (LINK: linkorder cunit prog)
        (FD: transf_fundef (funenv_program cunit) fd = OK fd')
        (VINJ: Val.inject_list F args args')
        (GLOB: meminj_global F)
        (MINJ: Mem.inject F m m')
        (STREE: inline_depth (1%nat::l) (S(Mem.sdepth m)) (S(Mem.sdepth m')))
        (SIZES : inline_sizes (1%nat::l) (Mem.astack(Mem.support m)) (Mem.astack(Mem.support m'))),
      match_states (Callstate stk fd args m id)
                   (Callstate stk' fd' args' m' id)
  | match_call_regular_states: forall stk f vargs m stk' f' sps' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs id n l
        (SPS: sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l  stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (GLOB: meminj_global F)
        (MINJ: Mem.inject F m m')
        (STREE: inline_depth (S n::l) (S(Mem.sdepth m)) ((Mem.sdepth m')))
        (SIZES: inline_sizes (S n :: l)(Mem.astack(Mem.support m)) (Mem.astack(Mem.support m')))
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Callstate stk (Internal f) vargs m id)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F l
        (MS: match_stacks F m m' l stk stk' (Mem.support m'))
        (VINJ: Val.inject F v v')
        (GLOB: meminj_global F)
        (MINJ: Mem.inject F m m')
        (STREE: inline_depth (1%nat::l) (S(Mem.sdepth m)) (S(Mem.sdepth m')))
        (SIZES : inline_sizes (1%nat::l)(Mem.astack(Mem.support m))(Mem.astack(Mem.support m'))),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sps' sp' rs' m' F ctx pc' or rinfo n l
        (SPS' : sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' n l stk stk' f' ctx sps' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (GLOB: meminj_global F)
        (MINJ: Mem.inject F m m')
        (STREE: inline_depth (S n::l) (S(Mem.sdepth m)) (Mem.sdepth m'))
        (SIZES: inline_sizes (S n::l) (Mem.astack(Mem.support m)) (Mem.astack(Mem.support m')))
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m').

(** ** Forward simulation *)

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Lemma astack_alloc_frame_alloc:
  forall m1 m2 m3 id path lo hi b,
    Mem.alloc_frame m1 id = (m2,path) ->
    Mem.alloc m2 lo hi = (m3,b) ->
    Mem.astack (Mem.support m3) = Mem.astack (Mem.support m1).
Proof.
  intros. apply Mem.support_alloc in H0.
  apply Mem.astack_alloc_frame in H.
  rewrite H0. rewrite  H. unfold sup_incr. destr.
Qed.

Lemma ros_is_ident_transf:
  forall ros rs rs' id F ctx bound,
    match_globalenvs F bound ->
    meminj_global F ->
    ros_is_ident ros rs id ->
    agree_regs F ctx rs rs' ->
    ros_is_ident (sros ctx ros) rs' id.
Proof.
  unfold ros_is_ident. intros.
  destr_in H1. simpl.
  generalize (proj1 H2 r) (proj2 H2 r). intros.
  destruct (plt (mreg ctx) r). rewrite H4 in H1; congruence.
  exploit H3. extlia.
  intro. rewrite H1 in H5. inv H5.
  unfold meminj_global in H0. exploit H0; eauto. intros.
  inv H5. auto.
Qed.

Definition incr_without_glob (j j' : meminj) : Prop :=
  forall b b' delta, j b = None -> j' b = Some (b',delta) ->
       is_stack b /\ is_stack b'.

Lemma meminj_global_invariant:
  forall j j',
    meminj_global j -> inject_incr j j' ->
    incr_without_glob j j' -> meminj_global j'.
Proof.
  intros. unfold meminj_global in *.
  intros. destruct (j (Global id)) eqn:H3. destruct p.
  apply H0 in H3 as H4. rewrite H2 in H4. inv H4.
  apply H in H3. auto. exploit H1; eauto.
  intros [A B]. inv A.
Qed.

Lemma match_stacks_push_l:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f (Mem.push_stage m) m' l s s' nb.
Proof.
  intros.
  eapply match_stacks_invariant; eauto.
Qed.

Lemma match_stacks_push_r:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f m (Mem.push_stage m') l s s' nb.
Proof.
  intros.
  eapply match_stacks_invariant; eauto.
Qed.

Lemma match_stacks_push:
  forall f m m' l s s' nb,
    match_stacks f m m' l s s' nb ->
    match_stacks f (Mem.push_stage m) (Mem.push_stage m') l s s' nb.
Proof.
  intros.
  eapply match_stacks_push_l; eauto.
  eapply match_stacks_push_r; eauto.
Qed.

Lemma match_stacks_inside_push_l:
  forall j m m' n l s s' f ctx nb rs,
    match_stacks_inside j m m' n l s s' f ctx nb rs ->
    match_stacks_inside j (Mem.push_stage m) m' n l s s' f ctx nb rs.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto.
Qed.

Lemma match_stacks_inside_push_r:
  forall j m m' n l s s' f ctx nb rs,
    match_stacks_inside j m m' n l s s' f ctx nb rs ->
    match_stacks_inside j m (Mem.push_stage m') n l s s' f ctx nb rs.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto.
Qed.


Lemma match_stacks_inside_push:
  forall j m m' n l s s' f ctx nb rs,
    match_stacks_inside j m m' n l s s' f ctx nb rs ->
    match_stacks_inside j (Mem.push_stage m) (Mem.push_stage m') n l s s' f ctx nb rs.
Proof.
  intros.
  eapply match_stacks_inside_push_l; eauto.
  eapply match_stacks_inside_push_r; eauto.
Qed.

Lemma inline_sizes_same_top:
  forall g f1 f2 s1 s2,
    inline_sizes g (f1::s1) s2 ->
    Memory.size_of_all_frames f1 = Memory.size_of_all_frames f2 ->
    inline_sizes g (f2::s1) s2.
Proof.
  intros g f1 f2 s1 s2 SZ EQ; inv SZ; simpl in *. destruct n; simpl in *. inv H0.
  econstructor; simpl; eauto. lia.
  econstructor; simpl; eauto.
Qed.

Lemma push_pop_unchanged_on : forall m1 m1' m2 m2' m3  m3' F,
    Mem.unchanged_on (loc_out_of_reach F (Mem.push_stage m1))(Mem.push_stage m1') m2' ->
    Mem.pop_stage m2' = Some m3' ->
    Mem.pop_stage m2 = Some m3 ->
    Mem.unchanged_on (loc_out_of_reach F m1) m1' m3'.
Proof.
  intros.
  inv H. constructor.
  - eapply Mem.sup_include_trans; eauto.
    intro. eapply Mem.support_pop_stage_1 in H0. apply H0.
  - intros. exploit unchanged_on_perm; eauto. intro.
    transitivity  (Mem.perm (Mem.push_stage m1') b ofs k p).
    reflexivity.
    etransitivity; eauto.
    eapply Mem.perm_pop_stage; eauto.
  - intros. exploit unchanged_on_contents; eauto. intros.
    etransitivity.
    2:transitivity (ZMap.get ofs (NMap.get (ZMap.t memval) b
                    (Mem.mem_contents (Mem.push_stage m1'))));eauto.
    unfold Mem.pop_stage in H0. destruct (Mem.astack(Mem.support m2')).
    discriminate. inv H0. auto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step fn_stack_requirements ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus (step fn_stack_requirements) tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; eauto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr (fresh_block sps') Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; eauto.
  apply agree_set_reg; auto.

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr (fresh_block sps') Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  apply Mem.support_store in H1 as SF. apply Mem.support_store in U as SF'.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  unfold Mem.sdepth in *. congruence. congruence.
  erewrite Mem.support_store; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.

- (* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [support G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply ros_is_ident_transf; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_push; eauto.
  eapply match_stacks_cons; eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.push_stage_inject; eauto.
  constructor. simpl. rewrite Nat.sub_0_r. auto.
  econstructor; simpl; eauto. simpl. lia.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_push_l; eauto.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. apply PRIV. inv H14. destruct H17. extlia.
  apply agree_val_regs_gen; auto.
  eapply Mem.push_stage_left_inject; eauto.
  inv STREE. constructor. simpl. auto.
  inv SIZES. econstructor; simpl; eauto.
  red; intros; apply PRIV. destruct H17. lia.

- (* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [support G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  assert (PRIV': range_private F m' m'0 (fresh_block sps') (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H7. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 (fresh_block sps') 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto. extlia.
  destruct X as [m1' FREE].
  exploit Mem.free_left_inject; eauto. intro.
  exploit Mem.free_right_inject; eauto.
  intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [P Q].
  eelim Q; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intro.
  exploit Mem.return_frame_parallel_inject; eauto.
  inv STREE. apply Mem.sdepth_active; eauto.
  erewrite Mem.sdepth_free; eauto. congruence.
  intros (m2' & RET' & INJ').
  apply Mem.support_free in H3 as SF. apply Mem.support_free in FREE as SF'.
  apply Mem.astack_return_frame in H4 as ARET. apply Mem.astack_return_frame in RET' as ARET'.
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply ros_is_ident_transf; eauto.
  eapply sig_function_translated; eauto.
  inv SIZES. congruence.
  econstructor; eauto.
  eapply match_stacks_support with (support := sps').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
    intros. erewrite <- Mem.perm_return_frame. 2: eauto.
            eapply Mem.perm_free_1. eauto with ordered_type.
    intros. left. intro. subst b. eapply freshness; eauto. auto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
  eapply Mem.sup_include_trans; eauto. eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto. intro. eapply Mem.support_return_frame_1 in RET'. apply RET'.
  eapply agree_val_regs; eauto.
  erewrite Mem.sdepth_return_frame; eauto.
  erewrite Mem.sdepth_return_frame; eauto.
  unfold Mem.sdepth in *. congruence.
  congruence.
  (* show that no valid location points into the stack block being freed *)
+ (* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply ros_is_ident_transf; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
    eapply range_private_invariant; eauto. intros. split. auto.
    erewrite Mem.perm_return_frame; eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.return_frame_left_inject. 2: eauto.
  eapply Mem.free_left_inject; eauto.
  eapply Mem.push_stage_right_inject; eauto.
  constructor. inv STREE.
  assert (O < n)%nat. {
    inv MS0. congruence. lia.
  } destruct n. extlia. unfold Mem.push_stage. unfold Mem.sup_push_stage.
  simpl. simpl. unfold Mem.sdepth. simpl. unfold Mem.sdepth in H9. rewrite <- H9.
  simpl. econstructor. simpl. erewrite <- Mem.sdepth_free in H8; eauto.
  erewrite <- Mem.sdepth_return_frame in H8; eauto.  simpl in *. unfold Mem.sdepth in H8. simpl in *.
  rewrite Nat.sub_0_r. auto.
  assert (O < n)%nat. {
    inv MS0. congruence. lia.
  }
  destruct n. lia. simpl.
  erewrite <- Mem.support_free in SIZES; eauto.
  erewrite Mem.astack_return_frame in SIZES; eauto.
  destruct (Mem.astack(Mem.support m'')).
  { inv SIZES. simpl in H13. congruence. }
  eapply inline_sizes_upright; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
    eapply range_private_invariant; eauto. intros. split. auto.
    erewrite Mem.perm_return_frame; eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.return_frame_left_inject. 2:eauto.
  eapply Mem.free_left_inject; eauto.
  erewrite Mem.sdepth_return_frame. 2: eauto. erewrite Mem.sdepth_free; eauto.
  erewrite <- Mem.support_free in SIZES. 2: eauto.
  erewrite Mem.astack_return_frame in SIZES; eauto.
  red; intros. exploit PRIV'; eauto. instantiate (1:= ofs).
    assert (dstk ctx <= dstk ctx'). red in H17; rewrite H17. apply align_le. apply min_alignment_pos.
    lia.
    unfold loc_private. intros. inv H6. split. auto. intros.
    rewrite <- Mem.perm_return_frame; eauto.
- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros [support MG].
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  exploit external_call_mem_inject'; eauto.
    eapply match_stacks_inside_globals; eauto.
    eapply Mem.push_stage_inject; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J [K [L M]]]]]]]]]]].
  exploit Mem.pop_stage_parallel_inject; eauto.
  inv SIZES. apply external_call_astack in A. rewrite <- A. simpl. congruence.
  intros [m2' [N O]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto; apply senv_preserved.
  econstructor.
    eauto.
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros. eapply external_call_max_perm in H1. eauto.
    apply H3. erewrite Mem.perm_pop_stage; eauto.
    intros; eapply external_call_max_perm in A. eauto.
    apply H3. erewrite Mem.perm_pop_stage; eauto.
    eapply push_pop_unchanged_on; eauto.
  auto. eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto. eauto.
  eapply meminj_global_invariant; eauto.
  auto. apply external_call_sdepth in A. apply external_call_sdepth in H1.
  apply Mem.sdepth_pop_stage in N. apply Mem.sdepth_pop_stage in H2.
  unfold Mem.sdepth in *. simpl in *. congruence.
  apply Mem.astack_pop_stage in H2. destruct H2 as [hd STK1].
  eapply external_call_astack in H1. rewrite <- H1 in STK1.
  simpl in STK1. inv STK1.
  apply Mem.astack_pop_stage in N. destruct N as [hd' STK2].
  eapply external_call_astack in A. rewrite <- A in STK2.
  simpl in STK2. inv STK2.
  auto.
  eapply Mem.unchanged_on_support in E; eauto.
  eapply Mem.sup_include_trans; eauto.
  eapply Mem.sup_include_trans; eauto.
  eapply Mem.sup_include_pop_stage; eauto.
  eapply range_private_extcall; eauto.
    intros. rewrite <- Mem.perm_pop_stage in H4. 2: apply H2.
    eapply external_call_max_perm in H1; eauto.
  eapply push_pop_unchanged_on; eauto.
  auto. apply VB. auto. auto.
  intros. apply SSZ2.
  intros. rewrite <- Mem.perm_pop_stage in H3. 2: apply N.
  eapply external_call_max_perm in A; eauto.
  apply VB.  auto.

- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 (fresh_block sps') 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); lia.
  destruct X as [m1' FREE].
  exploit Mem.free_left_inject; eauto. intro.
  exploit Mem.free_right_inject; eauto.
  intros. inversion FB; subst.
  assert (PRIV': range_private F m' m'0 (fresh_block sps') (dstk ctx) f'.(fn_stacksize)).
    rewrite H11 in PRIV. eapply range_private_free_left; eauto.
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [A B].
  eelim B; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem. intro.
  exploit Mem.return_frame_parallel_inject; eauto.
  apply Mem.sdepth_active. inv STREE. erewrite Mem.sdepth_free; eauto. congruence.
  intros [m2' [RET' INJ']].
  apply Mem.support_free in H0 as SF. apply Mem.support_free in FREE as SF'.
  apply Mem.astack_return_frame in H1 as ARET. apply Mem.astack_return_frame in RET' as ARET'.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  inv SIZES. congruence.
  econstructor; eauto.
  eapply match_stacks_support with (support := sps').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
    intros. erewrite <- Mem.perm_return_frame. 2: eauto. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. left. intro. subst b. eapply freshness; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
  eapply Mem.sup_include_trans; eauto. eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto. intro. eapply Mem.support_return_frame_1 in RET'. eapply RET'.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  erewrite Mem.sdepth_return_frame; eauto. apply Mem.sdepth_free in H0.
  erewrite Mem.sdepth_return_frame; eauto. apply Mem.sdepth_free in FREE.
  congruence.
  congruence.
+ (* inlined *)
  right. split. simpl. lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. eapply Mem.perm_return_frame; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.return_frame_left_inject. 2: eauto.
  eapply Mem.free_left_inject; eauto.
  erewrite Mem.sdepth_return_frame. 2:eauto. erewrite Mem.sdepth_free; eauto.
  erewrite <- Mem.astack_return_frame. 2: eauto. erewrite Mem.support_free; eauto.
  inv FB. rewrite H6 in PRIV.
  eapply range_private_invariant.
  eapply range_private_free_left; eauto.
  intros. split. auto. rewrite Mem.perm_return_frame; eauto. auto.

- (* internal function, not inlined *)
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_frame_parallel_inject; eauto. intros (m1' & p2 & ALLOCF & INJ).
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl.
    instantiate (1 := fn_stacksize f'). inv H3. extlia.
  intros [F' [m2' [sp' [A [B [C [D E]]]]]]].
  exploit Mem.record_frame_parallel_inject; eauto.
  inv SIZES. apply Mem.support_alloc in A. rewrite A.
  apply Mem.astack_alloc_frame in ALLOCF. unfold sup_incr.
  destr. simpl. congruence.
  apply inline_sizes_le in SIZES.
    erewrite astack_alloc_frame_alloc; eauto.
    erewrite astack_alloc_frame_alloc with (m3:=m''); eauto.
  intros [m3'[RECORD INJ']].
  left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  rewrite H8. econstructor.
  eapply Mem.alloc_result. eauto.
  instantiate (3 := F'). apply match_stacks_inside_base.
  assert (SPS: sp' = fresh_block (Mem.support m1')) by (eapply Mem.alloc_result; eauto).
  exploit match_stacks_support. eauto.
  intro.   eapply Mem.support_alloc_frame_1 in ALLOCF as SAF. eapply SAF.
  intro STK.
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite D in H10; inv H10. eelim freshness; eauto.
    rewrite E in H10; auto.
    intros.
    erewrite Mem.perm_alloc_frame. 2: eauto.
    erewrite <- Mem.perm_record_frame in H12. 2: eauto.
    exploit Mem.perm_alloc_inv. eexact H0. eauto.
    destruct (eq_block b1 stk); intros; auto.
    subst b1. rewrite D in H10; inv H10. eelim freshness; eauto.
    intros.
    erewrite <- Mem.perm_record_frame. 2: eauto.
    eapply Mem.perm_alloc_1; eauto.
    erewrite <- Mem.perm_alloc_frame; eauto.
    intros. erewrite Mem.perm_alloc_frame. 2: eauto.
    erewrite <- Mem.perm_record_frame in H11. 2: eauto.
    exploit Mem.perm_alloc_inv. eexact A. eauto.
    rewrite dec_eq_false; auto with ordered_type.
  intro. subst b. eelim freshness. rewrite SPS in H10. eauto.
  auto. auto. auto. eauto. auto.
  rewrite H7. apply agree_regs_init_regs. eauto. auto. inv H3; auto. congruence.
  eapply meminj_global_invariant; eauto.
  intro. intros. destruct (eq_block b stk).
  subst. rewrite D in H11. inv H11.
  apply Mem.alloc_result_stack in H0. apply Mem.alloc_result_stack in A. auto.
  rewrite E in H11. congruence. auto. auto.
  erewrite Mem.sdepth_record_frame; eauto.
  erewrite Mem.sdepth_alloc; eauto. erewrite Mem.sdepth_alloc_frame; eauto.
  apply Mem.sdepth_record_frame in RECORD.
  apply Mem.sdepth_alloc in A. apply Mem.sdepth_alloc_frame in ALLOCF. congruence.
  apply Mem.astack_record_frame in H1.
  apply Mem.astack_record_frame in RECORD as Y.
  destruct H1 as (hd & tl & Stk1 & Stk2).
  destruct Y as (hd' & tl' & Stk1' & Stk2').
  rewrite Stk2. rewrite Stk2'.
  apply Mem.support_alloc in A. unfold sup_incr in A. destr_in A.
  rewrite A in Stk1'.
  apply Mem.support_alloc in H0. unfold sup_incr in H0. destr_in H0.
  rewrite H0 in Stk1. simpl in *.
  apply Mem.astack_alloc_frame in H. apply Mem.astack_alloc_frame in ALLOCF.
  eapply inline_sizes_record; eauto. congruence.
  rewrite <- Mem.support_alloc with m1' 0 (fn_stacksize f') m2' sp'.
  intro. eapply Mem.support_record_frame_1 in RECORD. apply RECORD. auto.
  red; intros. split.
  erewrite <- Mem.perm_record_frame. 2: eauto.
  eapply Mem.perm_alloc_2; eauto. inv H3; extlia.
  intros; red; intros.
  exploit Mem.perm_alloc_inv. eexact H0.
  eapply Mem.perm_record_frame; eauto.
  destruct (eq_block b stk); intros.
  subst. rewrite D in H11; inv H11. inv H3; extlia.
  rewrite E in H11; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto.
  eapply Mem.perm_record_frame; eauto.
  rewrite dec_eq_true. lia.

- (* internal function, inlined *)
  inversion FB; subst.
  exploit Mem.alloc_frame_left_inject; eauto. intro.
  exploit Mem.alloc_left_mapped_inject.
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := (fresh_block sps')). apply VB. auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Z.le_max_r (fn_stacksize f) 0). lia.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; lia.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. extlia.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by lia.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. extlia.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by lia.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    erewrite Mem.perm_alloc_frame; eauto.
  intros [F' [A [B [C D]]]].
  exploit Mem.record_frame_left_inject; eauto. intro.
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  econstructor. auto.
  eapply match_stacks_inside_record_frame_left; eauto.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  intros. erewrite Mem.perm_alloc_frame; eauto.
  lia.
  eauto. auto.
  apply agree_regs_incr with F; auto.
  auto.
  eapply meminj_global_invariant; eauto.
  intro. intros. destruct (eq_block b stk).
  subst. rewrite C in H11. inv H11.
  apply Mem.alloc_result_stack in H0.
  unfold fresh_block. destr. destr. destr. split. auto.
  constructor. rewrite D in H11. congruence. auto. auto.
  erewrite Mem.sdepth_record_frame; eauto.
  erewrite Mem.sdepth_alloc; eauto. erewrite Mem.sdepth_alloc_frame; eauto.
  apply Mem.astack_record_frame in H1.
  destruct H1 as (hd&tl&Hstk&Hstk').
  rewrite Hstk'. apply Mem.support_alloc in H0. unfold sup_incr in H0.
  destr_in H0. simpl in H0.
  rewrite H0 in Hstk. simpl in Hstk.
  eapply inline_sizes_record_left; eauto.
  apply Mem.astack_alloc_frame in H. congruence.
  auto.
  eapply range_private_invariant. rewrite H4.
  eapply range_private_alloc_left.
  eapply range_private_invariant. eauto.
  3: eauto. all: eauto.
  intros. split. auto. erewrite Mem.perm_alloc_frame; eauto.
  intros. split. auto. erewrite Mem.perm_record_frame; eauto.

- (* external function *)
  exploit match_stacks_globalenvs; eauto. intros [support MG].
  exploit external_call_mem_inject'; eauto.
    eapply match_globalenvs_preserves_globals; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J [K [L M]]]]]]]]]]].
  simpl in FD. inv FD.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor.
    eapply match_stacks_support with (Mem.support m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    apply Mem.sup_include_refl.
    eapply external_call_support; eauto. auto.
    eapply meminj_global_invariant; eauto. auto.
    apply external_call_sdepth in H. apply external_call_sdepth in A. congruence.
    apply external_call_astack in H. apply external_call_astack in A. congruence.
- (* return from noninlined function *)
  inv MS0.
+ (* normal case *)
  exploit Mem.pop_stage_parallel_inject; eauto. inv SIZES. congruence.
  intros [m'1 [A B]].
  generalize (Mem.perm_pop_stage _ _ H). intro P1.
  generalize (Mem.perm_pop_stage _ _ A). intro P2.
  left; econstructor; split.
  eapply plus_one. eapply exec_return. eauto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant. eauto.
  apply match_stacks_inside_set_reg; eauto. all: eauto.
  intros. apply P1. auto.
  intros. apply P2. auto.
  intros. apply P2. auto.
  apply agree_set_reg; auto.
  inv STREE. simpl in H3. rewrite Nat.sub_0_r in H3.
  apply Mem.sdepth_pop_stage in H. apply Mem.sdepth_pop_stage in A. congruence.
  inv SIZES. apply Mem.astack_pop_stage in H. apply Mem.astack_pop_stage in A.
  destruct H. destruct A. rewrite H in H3. rewrite H0 in H2. inv H2.
  simpl in H3. auto.
  eapply Mem.sup_include_trans; eauto. intro.
  eapply Mem.support_pop_stage_1 in A. apply A.
  eapply range_private_invariant; eauto. intros.
  split. auto. apply P1. auto. intros. apply P2. auto.
  intros. apply SSZ2. apply P2. auto.
+ (* untailcall case *)
  exploit Mem.pop_stage_parallel_inject; eauto. inv SIZES. congruence.
  intros [m'1 [A B]].
  generalize (Mem.perm_pop_stage _ _ H). intro P1.
  generalize (Mem.perm_pop_stage _ _ A). intro P2.
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  left; econstructor; split.
  eapply plus_one. eapply exec_return. eauto.
  eapply match_regular_states. auto.
  eapply match_stacks_inside_set_reg; eauto.
  eapply match_stacks_inside_invariant; eauto.
  intros. apply P1. auto. intros. apply P2. auto.
  intros. apply P2. auto.
  eauto. auto.
  apply agree_set_reg; auto.
  auto. auto. auto. inv STREE. simpl in H3. rewrite Nat.sub_0_r in H3.
  apply Mem.sdepth_pop_stage in A. apply Mem.sdepth_pop_stage in H. congruence.
  inv SIZES. apply Mem.astack_pop_stage in H. apply Mem.astack_pop_stage in A.
  destruct H. destruct A. rewrite H in H3. rewrite H0 in H2. inv H2.
  simpl in H3. auto.
  eapply Mem.sup_include_trans; eauto. intro.
  eapply Mem.support_pop_stage_1 in A. apply A.
  eapply range_private_invariant.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply PRIV; lia.
  intros. split. auto. erewrite Mem.perm_pop_stage; eauto.
  intros. erewrite <- Mem.perm_pop_stage; eauto.
  lia.
  intros. apply SSZ2. apply P2. auto.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private F m' m'0 (fresh_block sps') (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
  eapply range_private_invariant.
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. lia. apply PRIV. lia.
    intros. split. auto. erewrite Mem.perm_pop_stage; eauto. auto.
  destruct or.
+ (* with a result *)
  generalize (Mem.perm_pop_stage _ _ H). intro P1.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; eauto.
  eapply match_stacks_inside_invariant; eauto. intros. apply P1. auto.
  apply agree_set_reg; auto.
  eapply Mem.pop_stage_left_inject; eauto.
  apply Mem.sdepth_pop_stage in H.
  inv STREE. constructor. simpl in *. congruence.
  apply Mem.astack_pop_stage in H. destruct H. rewrite H in SIZES. simpl in *.
  inv SIZES. simpl in *. econstructor; eauto.
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto. intros.
  erewrite Mem.perm_pop_stage; eauto.
  subst vres. apply agree_set_reg_undef'; auto.
  eapply Mem.pop_stage_left_inject; eauto.
  apply Mem.sdepth_pop_stage in H.
  inv STREE. constructor. simpl in *. congruence.
  apply Mem.astack_pop_stage in H. destruct H. rewrite H in SIZES. simpl in *.
  inv SIZES. simpl in *. econstructor; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & LINK).
  exists (Callstate nil tf nil (Mem.push_stage m1) (prog_main tprog)); split.
  econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog). auto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. eapply sig_function_translated; eauto.
  replace (prog_main tprog) with (prog_main prog).
  2:  symmetry; eapply match_program_main; eauto.
  exploit Genv.initmem_inject; eauto. intro.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (f' & m2 & b2 & A & B &C & D& F).
  rewrite H4 in A. inv A.
  assert (f' = Mem.flat_inj (Mem.support m2)).
    apply Axioms.extensionality. intro x.
    destruct (eq_block x b2).
    apply Mem.valid_new_block in H4 as H5.
    subst. rewrite D. unfold Mem.flat_inj. destr. apply n in H5. inv H5.
    rewrite F; auto. unfold Mem.flat_inj. destr; destr.
    eapply Mem.valid_block_alloc in H4; eauto. apply n0 in H4. inv H4.
    eapply Mem.valid_block_alloc_inv with (b' := x) in H4 as H5. inv H5. congruence. apply n0 in H6. inv H6.
    auto. subst.
  econstructor; eauto.
  instantiate (2 := Mem.flat_inj (Mem.support m2)).
  apply match_stacks_nil with (Mem.support m2).
  constructor; intros.
    unfold Mem.flat_inj. apply pred_dec_true; auto.
    unfold Mem.flat_inj in H5. destruct (Mem.sup_dec b1 (Mem.support m2)); congruence.
    eapply Mem.valid_block_alloc; eauto.
    eapply Genv.find_symbol_not_fresh; eauto.
    eapply Mem.valid_block_alloc; eauto.
    eapply Genv.find_funct_ptr_not_fresh; eauto.
    eapply Mem.valid_block_alloc; eauto.
    eapply Genv.find_var_info_not_fresh; eauto.
    intro. eapply Mem.valid_block_push_stage_1; eauto.
  intro. unfold Mem.flat_inj. intro. intros. destr_in H5.
  eapply Mem.push_stage_inject; eauto.
  constructor. simpl. rewrite Nat.sub_0_r. erewrite Mem.sdepth_push_stage; eauto.
  erewrite Mem.sdepth_alloc; eauto.
  unfold Mem.sdepth.
  simpl. erewrite Genv.init_mem_stack; eauto. simpl. constructor.
  simpl. erewrite Mem.astack_alloc; eauto.
  econstructor; simpl; eauto. erewrite Genv.init_mem_astack; eauto.
  constructor. simpl. lia.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics fn_stack_requirements prog)
                     (semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End INLINING.
