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

(** Correctness proof for common subexpression elimination. *)

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Builtins Events Globalenvs Smallstep.
Require Import LanguageInterface Invariant InjectFootprint.
Require Import Op Registers RTL.
Require Import ValueDomain ValueAOp ValueAnalysis.
Require Import CSEdomain CombineOp CombineOpproof CSE.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun _ f tf => transf_fundef (romem_for prog) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Soundness of operations over value numberings *)

Remark wf_equation_incr:
  forall next1 next2 e,
  wf_equation next1 e -> Ple next1 next2 -> wf_equation next2 e.
Proof.
  unfold wf_equation; intros; destruct e. destruct H. split.
  apply Pos.lt_le_trans with next1; auto.
  red; intros. apply Pos.lt_le_trans with next1; auto. apply H1; auto.
Qed.

(** Extensionality with respect to valuations. *)

Definition valu_agree (valu1 valu2: valuation) (upto: valnum) :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Section EXTEN.

Variable valu1: valuation.
Variable upto: valnum.
Variable valu2: valuation.
Hypothesis AGREE: valu_agree valu1 valu2 upto.
Variable ge: Genv.symtbl.
Variable sp: val.
Variable rs: regset.
Variable m: mem.

Lemma valnums_val_exten:
  forall vl,
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. auto.
Qed.

Lemma rhs_eval_to_exten:
  forall r v,
  rhs_eval_to valu1 ge sp m r v ->
  (forall v, In v (valnums_rhs r) -> Plt v upto) ->
  rhs_eval_to valu2 ge sp m r v.
Proof.
  intros. inv H; simpl in *.
- constructor. rewrite valnums_val_exten by assumption. auto.
- econstructor; eauto. rewrite valnums_val_exten by assumption. auto.
Qed.

Lemma equation_holds_exten:
  forall e,
  equation_holds valu1 ge sp m e ->
  wf_equation upto e ->
  equation_holds valu2 ge sp m e.
Proof.
  intros. destruct e. destruct H0. inv H.
- constructor. rewrite AGREE by auto. apply rhs_eval_to_exten; auto.
- econstructor. apply rhs_eval_to_exten; eauto. rewrite AGREE by auto. auto.
Qed.

Lemma numbering_holds_exten:
  forall n,
  numbering_holds valu1 ge sp rs m n ->
  Ple n.(num_next) upto ->
  numbering_holds valu2 ge sp rs m n.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply equation_holds_exten. auto.
  eapply wf_equation_incr; eauto with cse.
- rewrite AGREE. eauto. eapply Pos.lt_le_trans; eauto. eapply wf_num_reg; eauto.
Qed.

End EXTEN.

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Lemma valnum_reg_holds:
  forall valu1 ge sp rs m n r n' v,
  numbering_holds valu1 ge sp rs m n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs#r = valu2 v
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ Plt v n'.(num_next)
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  unfold valnum_reg; intros.
  destruct (num_reg n)!r as [v'|] eqn:NR.
- inv H0. exists valu1; splitall.
  + auto.
  + eauto with cse.
  + red; auto.
  + eauto with cse.
  + apply Ple_refl.
- inv H0; simpl.
  set (valu2 := fun vn => if peq vn n.(num_next) then rs#r else valu1 vn).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; splitall.
+ constructor; simpl; intros.
* constructor; simpl; intros.
  apply wf_equation_incr with (num_next n). eauto with cse. extlia.
  rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0; extlia.
  apply Plt_trans_succ; eauto with cse.
  rewrite PMap.gsspec in H0. destruct (peq v (num_next n)).
  replace r0 with r by (simpl in H0; intuition). rewrite PTree.gss. subst; auto.
  exploit wf_num_val; eauto with cse. intro.
  rewrite PTree.gso by congruence. auto.
* eapply equation_holds_exten; eauto with cse.
* unfold valu2. rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0. rewrite peq_true; auto.
  rewrite peq_false. eauto with cse. apply Plt_ne; eauto with cse.
+ unfold valu2. rewrite peq_true; auto.
+ auto.
+ extlia.
+ extlia.
Qed.

Lemma valnum_regs_holds:
  forall rl valu1 ge sp rs m n n' vl,
  numbering_holds valu1 ge sp rs m n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs##rl = map valu2 vl
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ (forall v, In v vl -> Plt v n'.(num_next))
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; simpl; intros.
- inv H0. exists valu1; splitall; auto. red; auto. simpl; tauto. extlia.
- destruct (valnum_reg n a) as [n1 v1] eqn:V1.
  destruct (valnum_regs n1 rl) as [n2 vs] eqn:V2.
  inv H0.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exploit (IHrl valu2); eauto.
  intros (valu3 & P & Q & R & S & T).
  exists valu3; splitall.
  + auto.
  + simpl; f_equal; auto. rewrite R; auto.
  + red; intros. transitivity (valu2 v); auto. apply R. extlia.
  + simpl; intros. destruct H0; auto. subst v1; extlia.
  + extlia.
Qed.

Lemma find_valnum_rhs_charact:
  forall rh v eqs,
  find_valnum_rhs rh eqs = Some v -> In (Eq v true rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && eq_rhs rh r) eqn:T.
  + InvBooleans. inv H. left; auto.
  + right; eauto.
Qed.

Lemma find_valnum_rhs'_charact:
  forall rh v eqs,
  find_valnum_rhs' rh eqs = Some v -> exists strict, In (Eq v strict rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (eq_rhs rh r) eqn:T.
  + inv H. exists strict; auto.
  + exploit IHeqs; eauto. intros [s IN]. exists s; auto.
Qed.

Lemma find_valnum_num_charact:
  forall v r eqs, find_valnum_num v eqs = Some r -> In (Eq v true r) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && peq v v0) eqn:T.
  + InvBooleans. inv H. auto.
  + eauto.
Qed.

Lemma reg_valnum_sound:
  forall n v r valu ge sp rs m,
  reg_valnum n v = Some r ->
  numbering_holds valu ge sp rs m n ->
  rs#r = valu v.
Proof.
  unfold reg_valnum; intros. destruct (num_val n)#v as [ | r1 rl] eqn:E; inv H.
  eapply num_holds_reg; eauto. eapply wf_num_val; eauto with cse.
  rewrite E; auto with coqlib.
Qed.

Lemma regs_valnums_sound:
  forall n valu ge sp rs m,
  numbering_holds valu ge sp rs m n ->
  forall vl rl,
  regs_valnums n vl = Some rl ->
  rs##rl = map valu vl.
Proof.
  induction vl; simpl; intros.
- inv H0; auto.
- destruct (reg_valnum n a) as [r1|] eqn:RV1; try discriminate.
  destruct (regs_valnums n vl) as [rl1|] eqn:RVL; inv H0.
  simpl; f_equal. eapply reg_valnum_sound; eauto. eauto.
Qed.

Lemma find_rhs_sound:
  forall n rh r valu ge sp rs m,
  find_rhs n rh = Some r ->
  numbering_holds valu ge sp rs m n ->
  exists v, rhs_eval_to valu ge sp m rh v /\ Val.lessdef v rs#r.
Proof.
  unfold find_rhs; intros. destruct (find_valnum_rhs' rh (num_eqs n)) as [vres|] eqn:E; try discriminate.
  exploit find_valnum_rhs'_charact; eauto. intros [strict IN].
  erewrite reg_valnum_sound by eauto.
  exploit num_holds_eq; eauto. intros EH. inv EH.
- exists (valu vres); auto.
- exists v; auto.
Qed.

Remark in_remove:
  forall (A: Type) (eq: forall (x y: A), {x=y}+{x<>y}) x y l,
  In y (List.remove eq x l) <-> x <> y /\ In y l.
Proof.
  induction l; simpl.
  tauto.
  destruct (eq x a).
  subst a. rewrite IHl. tauto.
  simpl. rewrite IHl. intuition congruence.
Qed.

Lemma forget_reg_charact:
  forall n rd r v,
  wf_numbering n ->
  In r (PMap.get v (forget_reg n rd)) -> r <> rd /\ In r (PMap.get v n.(num_val)).
Proof.
  unfold forget_reg; intros.
  destruct (PTree.get rd n.(num_reg)) as [vd|] eqn:GET.
- rewrite PMap.gsspec in H0. destruct (peq v vd).
  + subst v. rewrite in_remove in H0. intuition.
  + split; auto. exploit wf_num_val; eauto. congruence.
- split; auto. exploit wf_num_val; eauto. congruence.
Qed.

Lemma update_reg_charact:
  forall n rd vd r v,
  wf_numbering n ->
  In r (PMap.get v (update_reg n rd vd)) ->
  PTree.get r (PTree.set rd vd n.(num_reg)) = Some v.
Proof.
  unfold update_reg; intros.
  rewrite PMap.gsspec in H0.
  destruct (peq v vd).
- subst v. destruct H0.
+ subst r. apply PTree.gss.
+ exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
- exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
Qed.

Lemma rhs_eval_to_inj:
  forall valu ge sp m rh v1 v2,
  rhs_eval_to valu ge sp m rh v1 -> rhs_eval_to valu ge sp m rh v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; congruence.
Qed.

Lemma add_rhs_holds:
  forall valu1 ge sp rs m n rd rh rs',
  numbering_holds valu1 ge sp rs m n ->
  rhs_eval_to valu1 ge sp m rh (rs'#rd) ->
  wf_rhs n.(num_next) rh ->
  (forall r, r <> rd -> rs'#r = rs#r) ->
  exists valu2, numbering_holds valu2 ge sp rs' m (add_rhs n rd rh).
Proof.
  unfold add_rhs; intros.
  destruct (find_valnum_rhs rh n.(num_eqs)) as [vres|] eqn:FIND.

- (* A value number exists already *)
  exploit find_valnum_rhs_charact; eauto. intros IN.
  exploit wf_num_eqs; eauto with cse. intros [A B].
  exploit num_holds_eq; eauto. intros EH. inv EH.
  assert (rs'#rd = valu1 vres) by (eapply rhs_eval_to_inj; eauto).
  exists valu1; constructor; simpl; intros.
+ constructor; simpl; intros.
  * eauto with cse.
  * rewrite PTree.gsspec in H5. destruct (peq r rd).
    inv H5. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H5. destruct (peq r rd).
  congruence.
  rewrite H2 by auto. eauto with cse.

- (* Assigning a new value number *)
  set (valu2 := fun v => if peq v n.(num_next) then rs'#rd else valu1 v).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros.
  * destruct H3. inv H3. simpl; split. extlia.
    red; intros. apply Plt_trans_succ; eauto.
    apply wf_equation_incr with (num_next n). eauto with cse. extlia.
  * rewrite PTree.gsspec in H3. destruct (peq r rd).
    inv H3. extlia.
    apply Plt_trans_succ; eauto with cse.
  * apply update_reg_charact; eauto with cse.
+ destruct H3. inv H3.
  constructor. unfold valu2 at 2; rewrite peq_true.
  eapply rhs_eval_to_exten; eauto.
  eapply equation_holds_exten; eauto with cse.
+ rewrite PTree.gsspec in H3. unfold valu2. destruct (peq r rd).
  inv H3. rewrite peq_true; auto.
  rewrite peq_false. rewrite H2 by auto. eauto with cse.
  apply Plt_ne; eauto with cse.
Qed.

Lemma add_op_holds:
  forall valu1 ge sp rs m n op (args: list reg) v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_operation ge sp op rs##args m = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_op n dst op args).
Proof.
  unfold add_op; intros.
  destruct (is_move_operation op args) as [src|] eqn:ISMOVE.
- (* special case for moves *)
  exploit is_move_operation_correct; eauto. intros [A B]; subst op args.
  simpl in H0. inv H0.
  destruct (valnum_reg n src) as [n1 vsrc] eqn:VN.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  * rewrite PTree.gsspec in H0. destruct (peq r dst).
    inv H0. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H0. rewrite Regmap.gsspec.
  destruct (peq r dst). congruence. eauto with cse.

- (* general case *)
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ constructor. rewrite Regmap.gss. congruence.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma add_load_holds:
  forall valu1 ge sp rs m n addr (args: list reg) a chunk v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_load n dst chunk addr args).
Proof.
  unfold add_load; intros.
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ econstructor. rewrite <- B; eauto. rewrite Regmap.gss; auto.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma set_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (rs#r <- v) m (set_unknown n r).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros.
  + eauto with cse.
  + rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
    discriminate.
    eauto with cse.
  + exploit forget_reg_charact; eauto with cse. intros [A B].
    rewrite PTree.gro; eauto with cse.
- eauto with cse.
- rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
  discriminate.
  rewrite Regmap.gso; eauto with cse.
Qed.

Lemma set_res_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (regmap_setres r v rs) m (set_res_unknown n r).
Proof.
  intros. destruct r; simpl; auto. apply set_unknown_holds; auto.
Qed.

Lemma kill_eqs_charact:
  forall pred l strict r eqs,
  In (Eq l strict r) (kill_eqs pred eqs) ->
  pred r = false /\ In (Eq l strict r) eqs.
Proof.
  induction eqs; simpl; intros.
- tauto.
- destruct a. destruct (pred r0) eqn:PRED.
  tauto.
  inv H. inv H0. auto. tauto.
Qed.

Lemma kill_equations_hold:
  forall valu ge sp rs m n pred m',
  numbering_holds valu ge sp rs m n ->
  (forall r v,
      pred r = false ->
      rhs_eval_to valu ge sp m r v ->
      rhs_eval_to valu ge sp m' r v) ->
  numbering_holds valu ge sp rs m' (kill_equations pred n).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros; eauto with cse.
  destruct e. exploit kill_eqs_charact; eauto. intros [A B]. eauto with cse.
- destruct eq. exploit kill_eqs_charact; eauto. intros [A B].
  exploit num_holds_eq; eauto. intro EH; inv EH; econstructor; eauto.
- eauto with cse.
Qed.

Lemma kill_all_loads_hold:
  forall valu ge sp rs m n m',
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp rs m' (kill_all_loads n).
Proof.
  intros. eapply kill_equations_hold; eauto.
  unfold filter_loads; intros. inv H1.
  constructor. rewrite <- H2. apply op_depends_on_memory_correct; auto.
  discriminate.
Qed.

Lemma kill_loads_after_store_holds:
  forall valu ge sp rs m n addr args a chunk v m' bc approx ae am,
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr rs##args = Some a ->
  Mem.storev chunk m a v = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m'
                           (kill_loads_after_store approx n chunk addr args).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H6; inv H7.
- constructor. rewrite <- H8. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H9.
  destruct a; simpl in H1; try discriminate.
  destruct a0; simpl in H9; try discriminate.
  simpl.
  rewrite negb_false_iff in H6. unfold aaddressing in H6.
  eapply Mem.load_store_other. eauto.
  eapply pdisjoint_sound. eauto.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto with va.
Qed.

Lemma store_normalized_range_sound:
  forall bc chunk v,
  vmatch bc v (store_normalized_range chunk) ->
  Val.lessdef (Val.load_result chunk v) v.
Proof.
  intros. unfold Val.load_result; remember Archi.ptr64 as ptr64.
  destruct chunk; simpl in *; destruct v; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by lia. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by lia. rewrite H4; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by lia. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by lia. rewrite H4; auto.
- destruct ptr64; auto.
- destruct ptr64; auto.
- destruct ptr64; auto.
Qed.

Lemma add_store_result_hold:
  forall valu1 ge sp rs m' n addr args a chunk m src bc ae approx am,
  numbering_holds valu1 ge sp rs m' n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a rs#src = Some m' ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  exists valu2, numbering_holds valu2 ge sp rs m' (add_store_result approx n chunk addr args src).
Proof.
  unfold add_store_result; intros.
  unfold avalue; rewrite H3.
  destruct (vincl (AE.get src ae) (store_normalized_range chunk)) eqn:INCL.
- destruct (valnum_reg n src) as [n1 vsrc] eqn:VR1.
  destruct (valnum_regs n1 args) as [n2 vargs] eqn:VR2.
  exploit valnum_reg_holds; eauto. intros (valu2 & A & B & C & D & E).
  exploit valnum_regs_holds; eauto. intros (valu3 & P & Q & R & S & T).
  exists valu3. constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  destruct H4; eauto with cse. subst e. split.
  eapply Pos.lt_le_trans; eauto.
  red; simpl; intros. auto.
+ destruct H4; eauto with cse. subst eq. apply eq_holds_lessdef with (Val.load_result chunk rs#src).
  apply load_eval_to with a. rewrite <- Q; auto.
  destruct a; try discriminate. simpl. eapply Mem.load_store_same; eauto.
  rewrite B. rewrite R by auto. apply store_normalized_range_sound with bc.
  rewrite <- B. eapply vmatch_ge. apply vincl_ge; eauto. apply H2.
+ eauto with cse.

- exists valu1; auto.
Qed.

Lemma kill_loads_after_storebytes_holds:
  forall valu ge sp rs m n dst b ofs bytes m' bc approx ae am sz,
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n ->
  pmatch bc b ofs dst ->
  Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  length bytes = Z.to_nat sz -> sz >= 0 ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m'
                           (kill_loads_after_storebytes approx n dst sz).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H8; inv H9.
- constructor. rewrite <- H10. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H11.
  destruct a; simpl in H10; try discriminate.
  simpl.
  rewrite negb_false_iff in H8.
  eapply Mem.load_storebytes_other. eauto.
  rewrite H6. rewrite Z2Nat.id by lia.
  eapply pdisjoint_sound. eauto.
  unfold aaddressing. apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  auto.
Qed.

Lemma load_memcpy:
  forall m b1 ofs1 sz bytes b2 ofs2 m' chunk i v,
  Mem.loadbytes m b1 ofs1 sz = Some bytes ->
  Mem.storebytes m b2 ofs2 bytes = Some m' ->
  Mem.load chunk m b1 i = Some v ->
  ofs1 <= i -> i + size_chunk chunk <= ofs1 + sz ->
  (align_chunk chunk | ofs2 - ofs1) ->
  Mem.load chunk m' b2 (i + (ofs2 - ofs1)) = Some v.
Proof.
  intros.
  generalize (size_chunk_pos chunk); intros SPOS.
  set (n1 := i - ofs1).
  set (n2 := size_chunk chunk).
  set (n3 := sz - (n1 + n2)).
  replace sz with (n1 + (n2 + n3)) in H by (unfold n3, n2, n1; lia).
  exploit Mem.loadbytes_split; eauto.
  unfold n1; lia.
  unfold n3, n2, n1; lia.
  intros (bytes1 & bytes23 & LB1 & LB23 & EQ).
  clear H.
  exploit Mem.loadbytes_split; eauto.
  unfold n2; lia.
  unfold n3, n2, n1; lia.
  intros (bytes2 & bytes3 & LB2 & LB3 & EQ').
  subst bytes23; subst bytes.
  exploit Mem.load_loadbytes; eauto. intros (bytes2' & A & B).
  assert (bytes2' = bytes2).
  { replace (ofs1 + n1) with i in LB2 by (unfold n1; lia). unfold n2 in LB2. congruence.  }
  subst bytes2'.
  exploit Mem.storebytes_split; eauto. intros (m1 & SB1 & SB23).
  clear H0.
  exploit Mem.storebytes_split; eauto. intros (m2 & SB2 & SB3).
  clear SB23.
  assert (L1: Z.of_nat (length bytes1) = n1).
  { erewrite Mem.loadbytes_length by eauto. apply Z2Nat.id. unfold n1; lia. }
  assert (L2: Z.of_nat (length bytes2) = n2).
  { erewrite Mem.loadbytes_length by eauto. apply Z2Nat.id. unfold n2; lia. }
  rewrite L1 in *. rewrite L2 in *.
  assert (LB': Mem.loadbytes m2 b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- L2. eapply Mem.loadbytes_storebytes_same; eauto. }
  assert (LB'': Mem.loadbytes m' b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- LB'. eapply Mem.loadbytes_storebytes_other; eauto.
    unfold n2; lia.
    right; left; lia. }
  exploit Mem.load_valid_access; eauto. intros [P Q].
  rewrite B. apply Mem.loadbytes_load.
  replace (i + (ofs2 - ofs1)) with (ofs2 + n1) by (unfold n1; lia).
  exact LB''.
  apply Z.divide_add_r; auto.
Qed.

Lemma shift_memcpy_eq_wf:
  forall src sz delta e e' next,
  shift_memcpy_eq src sz delta e = Some e' ->
  wf_equation next e ->
  wf_equation next e'.
Proof with (try discriminate).
  unfold shift_memcpy_eq; intros.
  destruct e. destruct r... destruct a...
  try (rename i into ofs).
  destruct (zle src (Ptrofs.unsigned ofs) &&
        zle (Ptrofs.unsigned ofs + size_chunk m) (src + sz) &&
        zeq (delta mod align_chunk m) 0 && zle 0 (Ptrofs.unsigned ofs + delta) &&
        zle (Ptrofs.unsigned ofs + delta) Ptrofs.max_unsigned)...
  inv H. destruct H0. split. auto. red; simpl; tauto.
Qed.

Lemma shift_memcpy_eq_holds:
  forall src dst sz e e' m sp bytes m' valu ge,
  shift_memcpy_eq src sz (dst - src) e = Some e' ->
  Mem.loadbytes m sp src sz = Some bytes ->
  Mem.storebytes m sp dst bytes = Some m' ->
  equation_holds valu ge (Vptr sp Ptrofs.zero) m e ->
  equation_holds valu ge (Vptr sp Ptrofs.zero) m' e'.
Proof with (try discriminate).
  intros. set (delta := dst - src) in *. unfold shift_memcpy_eq in H.
  destruct e as [l strict rhs] eqn:E.
  destruct rhs as [op vl | chunk addr vl]...
  destruct addr...
  try (rename i into ofs).
  set (i1 := Ptrofs.unsigned ofs) in *. set (j := i1 + delta) in *.
  destruct (zle src i1)...
  destruct (zle (i1 + size_chunk chunk) (src + sz))...
  destruct (zeq (delta mod align_chunk chunk) 0)...
  destruct (zle 0 j)...
  destruct (zle j Ptrofs.max_unsigned)...
  simpl in H; inv H.
  assert (LD: forall v,
    Mem.loadv chunk m (Vptr sp ofs) = Some v ->
    Mem.loadv chunk m' (Vptr sp (Ptrofs.repr j)) = Some v).
  {
    simpl; intros. rewrite Ptrofs.unsigned_repr by lia.
    unfold j, delta. eapply load_memcpy; eauto.
    apply Zmod_divide; auto. generalize (align_chunk_pos chunk); lia.
  }
  inv H2.
+ inv H3. exploit eval_addressing_Ainstack_inv; eauto. intros [E1 E2].
  simpl in E2; rewrite Ptrofs.add_zero_l in E2. subst a.
  apply eq_holds_strict. econstructor. rewrite eval_addressing_Ainstack.
  simpl. rewrite Ptrofs.add_zero_l. eauto.
  apply LD; auto.
+ inv H4. exploit eval_addressing_Ainstack_inv; eauto. intros [E1 E2].
  simpl in E2; rewrite Ptrofs.add_zero_l in E2. subst a.
  apply eq_holds_lessdef with v; auto.
  econstructor. rewrite eval_addressing_Ainstack. simpl. rewrite Ptrofs.add_zero_l. eauto.
  apply LD; auto.
Qed.

Lemma add_memcpy_eqs_charact:
  forall e' src sz delta eqs2 eqs1,
  In e' (add_memcpy_eqs src sz delta eqs1 eqs2) ->
  In e' eqs2 \/ exists e, In e eqs1 /\ shift_memcpy_eq src sz delta e = Some e'.
Proof.
  induction eqs1; simpl; intros.
- auto.
- destruct (shift_memcpy_eq src sz delta a) as [e''|] eqn:SHIFT.
  + destruct H. subst e''. right; exists a; auto.
    destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
  + destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
Qed.

Lemma add_memcpy_holds:
  forall m bsrc osrc sz bytes bdst odst m' valu ge sp rs n1 n2 bc asrc adst,
  Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes ->
  Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n1 ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m' n2 ->
  pmatch bc bsrc osrc asrc ->
  pmatch bc bdst odst adst ->
  bc sp = BCstack ->
  Ple (num_next n1) (num_next n2) ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m' (add_memcpy n1 n2 asrc adst sz).
Proof.
  intros. unfold add_memcpy.
  destruct asrc; auto; destruct adst; auto.
  assert (A: forall b o i, pmatch bc b o (Stk i) -> b = sp /\ i = o).
  {
    intros. inv H7. split; auto. eapply bc_stack; eauto.
  }
  apply A in H3; destruct H3. subst bsrc ofs.
  apply A in H4; destruct H4. subst bdst ofs0.
  constructor; simpl; intros; eauto with cse.
- constructor; simpl; eauto with cse.
  intros. exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  apply wf_equation_incr with (num_next n1); auto.
  eapply shift_memcpy_eq_wf; eauto with cse.
- exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  eapply shift_memcpy_eq_holds; eauto with cse.
Qed.

(** Correctness of operator reduction *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable V: Type.
Variable ge: genv.
Variable sp: val.
Variable rs: regset.
Variable m: mem.
Variable sem: A -> list val -> option V.
Hypothesis f_sound:
  forall eqs valu op args op' args',
  (forall v rhs, eqs v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v)) ->
  f eqs op args = Some(op', args') ->
  sem op' (map valu args') = sem op (map valu args).
Variable n: numbering.
Variable valu: valnum -> val.
Hypothesis n_holds: numbering_holds valu ge sp rs m n.

Lemma reduce_rec_sound:
  forall niter op args op' rl' res,
  reduce_rec A f n niter op args = Some(op', rl') ->
  sem op (map valu args) = Some res ->
  sem op' (rs##rl') = Some res.
Proof.
  induction niter; simpl; intros.
  discriminate.
  destruct (f (fun v : valnum => find_valnum_num v (num_eqs n)) op args)
           as [[op1 args1] | ] eqn:?.
  assert (sem op1 (map valu args1) = Some res).
    rewrite <- H0. eapply f_sound; eauto.
    simpl; intros.
    exploit num_holds_eq; eauto.
    eapply find_valnum_num_charact; eauto with cse.
    intros EH; inv EH; auto.
  destruct (reduce_rec A f n niter op1 args1) as [[op2 rl2] | ] eqn:?.
  inv H. eapply IHniter; eauto.
  destruct (regs_valnums n args1) as [rl|] eqn:?.
  inv H. erewrite regs_valnums_sound; eauto.
  discriminate.
  discriminate.
Qed.

Lemma reduce_sound:
  forall op rl vl op' rl' res,
  reduce A f n op rl vl = (op', rl') ->
  map valu vl = rs##rl ->
  sem op rs##rl = Some res ->
  sem op' rs##rl' = Some res.
Proof.
  unfold reduce; intros.
  destruct (reduce_rec A f n 4%nat op vl) as [[op1 rl1] | ] eqn:?; inv H.
  eapply reduce_rec_sound; eauto. congruence.
  auto.
Qed.

End REDUCE.

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution
  from [pc] to [pc'], satisfiability at [pc] implies
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs m f vapprox approx pc pc' i,
  analyze f vapprox = Some approx ->
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  (exists valu, numbering_holds valu ge sp rs m (transfer f vapprox pc approx!!pc)) ->
  (exists valu, numbering_holds valu ge sp rs m approx!!pc').
Proof.
  intros.
  assert (Numbering.ge approx!!pc' (transfer f vapprox pc approx!!pc)).
    eapply Solver.fixpoint_solution; eauto.
  destruct H2 as [valu NH]. exists valu; apply H3. auto.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs m f vapprox approx,
  analyze f vapprox = Some approx ->
  exists valu, numbering_holds valu ge sp rs m approx!!(f.(fn_entrypoint)).
Proof.
  intros.
  replace (approx!!(f.(fn_entrypoint))) with Solver.L.top.
  exists (fun v => Vundef). apply empty_numbering_holds.
  symmetry. eapply Solver.fixpoint_entry; eauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Variable w: injp_world.
Hypothesis GE : CKLR.match_stbls injp w se tse.
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse tprog.

Lemma functions_translated (j:meminj):
  forall (v tv: val) (f: RTL.fundef),
  Genv.match_stbls j se tse ->
  Genv.find_funct ge v = Some f ->
  Val.inject j v tv ->
  exists tf, Genv.find_funct tge tv = Some tf /\ transf_fundef (romem_for prog) f = OK tf.
Proof.
  intros. eapply Genv.find_funct_transf_partial; eauto.
Qed.

Lemma sig_preserved:
  forall rm f tf, transf_fundef rm f = OK tf -> funsig tf = funsig f.
Proof.
  unfold transf_fundef; intros. destruct f; monadInv H; auto.
  unfold transf_function in EQ.
  destruct (analyze f (vanalyze rm f)); try discriminate. inv EQ; auto.
Qed.

Definition transf_function' (f: function) (approxs: PMap.t numbering) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

(*Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.
 *)

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto.
Qed.

Lemma ros_address_translated:
  forall j ros rs rs',
  Genv.match_stbls j se tse ->
  regset_inject j rs rs' ->
  Val.inject j (ros_address ge ros rs) (ros_address tge ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct.
  destruct ros; eauto.
  eapply symbol_address_inject; eauto.
Qed.

Lemma tr_builtin_arg:
  forall j rs rs' sp sp' m m',
  Genv.match_stbls j se tse ->
  regset_inject j rs rs' ->
  j sp = Some(sp', 0) ->
  Mem.inject j m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
          /\ Val.inject j v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#x; split. constructor; eauto. eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add Ptrofs.zero ofs)).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  rewrite Ptrofs.add_zero. auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. eauto.
- econstructor; split. constructor. simpl. econstructor; eauto.
  rewrite Ptrofs.add_zero_l; rewrite Ptrofs.add_zero. auto.
- assert (Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs)).
  { unfold Genv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
    edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
    econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
  edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
  econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall j rs rs' sp sp' m m',
  Genv.match_stbls j se tse ->
  regset_inject j rs rs' ->
  j sp = Some(sp', 0) ->
  Mem.inject j m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
          /\ Val.inject_list j vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** The proof of semantic preservation is a simulation argument using
  diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Left: RTL execution in the original program.  Right: RTL execution in
  the optimized program.  Precondition (top) and postcondition (bottom):
  agreement between the states, including the fact that
  the numbering at [pc] (returned by the static analysis) is satisfiable.
*)

Definition analyze (cu: program) (f: function) :=
  CSE.analyze f (vanalyze (romem_for cu) f).

Inductive match_stackframes(j:meminj) : list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes j nil nil
  | match_stackframes_cons:
      forall res sp pc rs f s sp' rs' s' approx
           (ANALYZE: analyze prog f = Some approx)
           (SAT: forall v m, exists valu, numbering_holds valu ge (Vptr sp Ptrofs.zero) (rs#res <- v) m approx!!pc)
           (RLD: regset_inject j rs rs')
           (STACKS: match_stackframes j s s')
           (PC: j sp = Some (sp',0)),
    match_stackframes j
      (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: s)
      (Stackframe res (transf_function' f approx) (Vptr sp' Ptrofs.zero) pc rs' :: s').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f approx sp' j MEM
             (ANALYZE: analyze prog f = Some approx)
             (SAT: exists valu, numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m approx!!pc)
             (REGS: regset_inject j rs rs')
             (INCR: injp_acc w (injpw j m m' MEM))
             (STACKS: match_stackframes j s s')
             (SP: j sp = Some (sp',0)),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function' f approx) (Vptr sp' Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s vf vf' args m s' args' m' j MEM
             (STACKS: match_stackframes j s s')
             (VF: Val.inject j vf vf')
             (ARGS: Val.inject_list j args args')
             (INCR: injp_acc w (injpw j m m' MEM)),
      match_states (Callstate s vf args m)
                   (Callstate s' vf' args' m')
  | match_states_return:
      forall s s' v v' m m' j MEM
             (STACK: match_stackframes j s s')
             (RES: Val.inject j v v')
             (INCR: injp_acc w (injpw j m m' MEM)),
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').


Lemma match_stbls_incr : forall j m1 m2 MEM,
    injp_acc w (injpw j m1 m2 MEM) ->
    Genv.match_stbls j ge tge.
Proof.
  intros.
  exploit CKLR.match_stbls_acc. 2: apply GE.
  simpl. eauto. intro. simpl in H0. inv H0. eauto.
Qed.

Lemma match_stackframes_incr : forall j j' l l',
    match_stackframes j l l' ->
    inject_incr j j' ->
    match_stackframes j' l l'.
Proof.
  induction 1; intros.
  - constructor.
  - constructor; eauto.
    eapply regset_inject_incr; eauto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap;
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation is a case analysis over the transition
  in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (SOUND: sound_state prog se s1),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_inject.
  eapply match_stbls_incr; eauto. 4: eauto. eauto. 2: eauto.
  eapply regs_inject; eauto.
  intros [v' [A B]].
  rewrite eval_shift_stack_operation in A.
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  destruct SAT as [valu NH]. eapply add_op_holds; eauto.
  apply set_reg_inject; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_inject; auto.
  eapply Mem.val_lessdef_inject_compose; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge (Vptr sp0 Ptrofs.zero) op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge (Vptr sp0 Ptrofs.zero) op vl m); eauto.
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_inject. eapply match_stbls_incr; eauto. 4: eauto.
  eauto. eapply regs_inject; eauto. eauto.
  intros [v' [A B]].
  rewrite eval_shift_stack_operation in A. eauto.
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_inject; auto.

- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_inject; auto. eapply Mem.val_lessdef_inject_compose; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge (Vptr sp0 Ptrofs.zero) addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_inject. eapply match_stbls_incr; eauto. 4: eauto. eauto.
  apply regs_inject; eauto. eexact ADDR.
  intros [a' [A B]].
  rewrite eval_shift_stack_addressing in A. eauto.
  exploit Mem.loadv_inject; eauto.
  intros [v' [X Y]].
  econstructor; split.
  eapply exec_Iload; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_inject; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge (Vptr sp0 Ptrofs.zero) addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_inject. eapply match_stbls_incr; eauto. 4: eauto. eauto.
  apply regs_inject; eauto. eexact ADDR.
  intros [a' [A B]].
  rewrite eval_shift_stack_addressing in A.
  exploit Mem.storev_mapped_inject; eauto. intros [m'' [X Y]].
  econstructor; split.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  InvSoundState.
  eapply add_store_result_hold; eauto.
  eapply kill_loads_after_store_holds; eauto.
  instantiate (1:= Y).
  etransitivity. eauto. eapply injp_acc_storev; eauto.

- (* Icall *)
  exploit match_stbls_incr; eauto. intro GE'.
  exploit functions_translated; eauto.
  eapply ros_address_translated; eauto.
  intros (tf & FIND' & TRANSF').
  econstructor; split.
  eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_stackframes_cons; eauto.
  intros. eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  exists (fun _ => Vundef); apply empty_numbering_holds.
  eapply ros_address_translated; eauto.
  apply regs_inject; auto.

- (* Itailcall *)
  exploit match_stbls_incr; eauto. intro GE'.
  exploit functions_translated; eauto. eapply ros_address_translated; eauto.
  intros (tf & FIND' & TRANSF').
  exploit Mem.free_parallel_inject; eauto. intros [m'' [A B]].
  simpl in A. rewrite Z.add_0_r in A.
  econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply ros_address_translated; eauto.
  apply regs_inject; auto.
  etransitivity. eauto. instantiate (1:= B).
  eapply injp_acc_free with (lo1 := 0); cbn; eauto.
  rewrite Z.add_0_r. eauto.

- (* Ibuiltin *)
  exploit match_stbls_incr; eauto. intro GE'.
  exploit tr_builtin_args; eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_inject; eauto.
  intros (j' & v' & m1' & P & Q & R & S & T & U & V).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  econstructor. 5: eapply match_stackframes_incr; eauto. all: eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
* unfold transfer; rewrite H.
  destruct SAT as [valu NH].
  assert (CASE1: exists valu, numbering_holds valu ge (Vptr sp0 Ptrofs.zero) (regmap_setres res vres rs) m' empty_numbering).
  { exists valu; apply empty_numbering_holds. }
  assert (CASE2: m' = m -> exists valu, numbering_holds valu ge (Vptr sp0 Ptrofs.zero) (regmap_setres res vres rs) m' (set_res_unknown approx#pc res)).
  { intros. subst m'. exists valu. apply set_res_unknown_holds; auto. }
  assert (CASE3: exists valu, numbering_holds valu ge (Vptr sp0 Ptrofs.zero) (regmap_setres res vres rs) m'
                         (set_res_unknown (kill_all_loads approx#pc) res)).
  { exists valu. apply set_res_unknown_holds. eapply kill_all_loads_hold; eauto. }
  destruct ef.
  + apply CASE1.
  + destruct (lookup_builtin_function name sg) as [bf|] eqn:LK.
    ++ apply CASE2. simpl in H1; red in H1; rewrite LK in H1; inv H1. auto.
    ++ apply CASE3.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
  + apply CASE3.
  + apply CASE1.
  + apply CASE1.
  + inv H0; auto. inv H3; auto. inv H4; auto.
    simpl in H1. inv H1.
    exists valu.
    apply set_res_unknown_holds.
    InvSoundState. unfold vanalyze; rewrite AN.
    assert (pmatch bc bsrc osrc (aaddr_arg (VA.State ae am) a0))
    by (eapply aaddr_arg_sound_1; eauto).
    assert (pmatch bc bdst odst (aaddr_arg (VA.State ae am) a1))
    by (eapply aaddr_arg_sound_1; eauto).
    eapply add_memcpy_holds; eauto.
    eapply kill_loads_after_storebytes_holds; eauto.
    eapply Mem.loadbytes_length; eauto.
    simpl. apply Ple_refl.
  + apply CASE2; inv H1; auto.
  + apply CASE2; inv H1; auto.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
    * eapply set_res_inject; eauto. eapply regset_inject_incr; eauto.
    * etransitivity. eauto. instantiate (1:= R). constructor; eauto.
      red. eauto using external_call_readonly.
      red. eauto using external_call_readonly.
      red. intros. eapply external_call_max_perm; eauto.
      red. intros. eapply external_call_max_perm; eauto.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto.
    intros; eapply combine_cond_sound; eauto. }
  econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_inject; eauto. apply regs_inject; auto.
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (REGS arg); rewrite H0; intro LD; inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_inject; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Ireturn; eauto. simpl in A. rewrite Z.add_0_r in A.
  simpl. eauto.
  econstructor; eauto.
  destruct or; simpl; auto. instantiate (1:= B).
  etransitivity. eauto. eapply injp_acc_free with (lo1 := 0); cbn; eauto.

- (* internal function *)
  exploit match_stbls_incr; eauto. intro GE'.
  exploit functions_translated; eauto. cbn. intros (tf & FIND' & TFD).
  monadInv TFD. unfold transf_function in EQ. fold (analyze prog f) in EQ.
  destruct (analyze prog f) as [approx|] eqn:?; inv EQ.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (j' & m'' & b2 & A & B & C & D & E).
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor. 5: eapply match_stackframes_incr; eauto. all: eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_inject; auto.
  eapply val_inject_list_incr; eauto. instantiate (1:= B).
  etransitivity. eauto. eapply injp_acc_alloc; eauto.

- (* external function *)
  exploit match_stbls_incr; eauto. intro GE'.
  exploit functions_translated; eauto. cbn. intros (tf & FIND' & TFD).
  monadInv TFD.
  exploit external_call_mem_inject; eauto.
  intros (j' & v' & m1' & P & Q & R & S & U & V & W).
  econstructor; split.
  eapply exec_function_external; eauto.
  econstructor. eapply match_stackframes_incr; eauto. all: eauto.
  etransitivity. eauto. instantiate (1:=R). constructor; eauto.
  red. eauto using external_call_readonly.
  red. eauto using external_call_readonly.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  
- (* return *)
  inv STACK.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_inject; auto.
Qed.

Definition m01 := match w with
                 | injpw f m1 m2 Hm => m1
                  end.

Definition ro_w := (se, (row ge m01), w).

Lemma transf_initial_states:
  forall q1 q2 st1, match_query  (ro @ cc_c injp) ro_w q1 q2 -> initial_state ge q1 st1 ->
  exists st2, initial_state tge q2 st2 /\ match_states st1 st2 /\ sound_state prog ge st1.
Proof.
  intros. destruct H as [x [H1 H2]]. inv H0. inv H1. inv H2. cbn in *. inv H0. inv H9.
  cbn in *. clear Hm1 Hm0.
  exploit functions_translated; eauto. inversion GE. eauto.
  intros (tf & FIND & TFD).
  exists (Callstate nil vf2 vargs2 m2); repeat apply conj.
  - setoid_rewrite <- (sig_preserved (romem_for prog) (Internal f)); eauto.
    monadInv TFD. constructor; auto. rewrite H3. eauto.
  - cbn in *. econstructor; eauto. constructor.  rewrite H0. reflexivity.
  - eapply sound_memory_ro_sound_state; eauto. inversion GE. eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r1,
  match_states st1 st2 -> final_state st1 r1 ->
  exists r2, final_state st2 r2 /\ match_reply (ro @ cc_c injp) ro_w r1 r2.
Proof.
  intros. inv H0. inv H. inv STACK. inv INCR.
  exists (cr v' m'). split. constructor; eauto.  
  eexists; split. constructor; eauto.
  constructor; eauto. unfold m01. rewrite <- H7. constructor; eauto.
  inversion H6. eauto.
  exists (injpw j m m' Hm'0).
  split; eauto. rewrite <- H7. econstructor; eauto.
  econstructor; eauto. constructor.
Qed.

Lemma transf_external_states:
  forall st1 st2 q1, match_states st1 st2 -> sound_state prog ge st1 -> at_external ge st1 q1 ->
  exists w' q2, at_external tge st2 q2 /\ match_query (ro @ cc_c injp) w' q1 q2 /\ match_senv (ro @ cc_c injp) w' se tse /\
  forall r1 r2 st1', match_reply (ro @ cc_c injp) w' r1 r2 -> after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states st1' st2' /\ sound_state prog ge st1'.
Proof.
  intros st1 st2 q1 Hst Hs Hq1. destruct Hq1. inv Hst.
  exploit match_stbls_incr; eauto. intro MSTB.
  exploit functions_translated; eauto. simpl.
  intros (tf & FIND & TFD). monadInv  TFD.
  inv Hs. exploit mmatch_inj; eauto. eapply mmatch_below; eauto.
  intro.
  exploit Mem.inject_compose. apply H0. apply MEM.
  intro MEM'.
  set (jbc := fun b => match bc b with
                    | BCinvalid => None
                    | _ => j b end).
  assert (JBC_COMPOSE: forall b, compose_meminj (inj_of_bc bc) j b = jbc b).
  {
    intro b. unfold compose_meminj,inj_of_bc, jbc.
    destruct (bc b); simpl; eauto;
    destruct (j b) as [[x y]|]; eauto.
  }
  eexists (se,(row se m),(injpw _ _ _ MEM')). eexists. cbn. intuition idtac.
  - econstructor; eauto.
  - assert (sound_memory_ro ge m).
    {
      red. split. eapply romatch_exten; eauto.
      intros.
      clear -RO GE0. destruct GE0.
      unfold ValueAnalysis.bc_of_symtbl. simpl.
      destruct (Genv.invert_symbol se b) eqn:Hinv.
      apply Genv.invert_find_symbol in Hinv. split.
      intro. inv H1. eapply H; eauto.
      intro. apply  H in Hinv. congruence.
      split. intro. congruence. intro. apply H in H1.
      apply Genv.find_invert_symbol in H1. cbn in *. congruence.
      inv GE. inversion INCR. inversion H14. eauto.
    }
    
    eexists. split. constructor. constructor; eauto.
    econstructor; eauto.
    + cbn. destruct VF; try discriminate. cbn.
      eapply val_inject_compose.
      exploit vmatch_inj; eauto. eauto.
    + cbn.
      eapply CKLRAlgebra.val_inject_list_compose.
      econstructor; eauto. split; eauto.
      revert ARGS0. generalize vargs.
      induction vargs0; simpl; intros; constructor.
      eapply vmatch_inj; eauto. auto.
    + constructor; eauto.
    + unfold Genv.find_funct in H. destruct vf; try congruence; eauto.
  - constructor; eauto.
  - inv GE. inversion INCR. constructor.
    eapply Genv.match_stbls_compose.
    eapply inj_of_bc_preserves_globals; eauto.
    apply MSTB. inversion H14. eauto. inversion H15. eauto.
  - inv H2. destruct H1 as (r3 & Hr1& Hr2). inv Hr1. inv H1. rename H3 into ROACC.
    destruct Hr2 as ([j' s1 s2 MEM''] & Hw' & Hr).
    inv Hw'.
    inv Hr. cbn in *. inv H5. simpl in *.
    eexists (Returnstate s' vres2 m2'); split.
    econstructor; eauto. split.
    + (*match_states*)
      set (j'' := fun b => match bc b with
                        |BCinvalid =>
                           if j b then j b else j' b
                        |_ => j' b
                        end
          ).
      assert (INCR1 : inject_incr j j'').
      { red. intros. destruct (block_class_eq (bc b) BCinvalid).
        unfold j''; rewrite e; eauto. rewrite H1.
        reflexivity.
        unfold j''. destruct (bc b) eqn:BC; try congruence; apply H13;
        unfold compose_meminj, inj_of_bc;
        rewrite BC, H1; reflexivity.
      }
      assert (INCR2: inject_incr j' j'').
      { red. intros.
        destruct (bc b) eqn:BC;
          unfold j''; rewrite BC; eauto.
        destruct (j b) as [[b'' d']|] eqn :Hj.
        exploit H14; eauto. unfold compose_meminj, inj_of_bc.
        rewrite BC. reflexivity. intros [A B].
        inversion MEM. exploit mi_freeblocks; eauto. intro. congruence.
        eauto.
      }
      assert(MEM''' : Mem.inject j'' m'0 m2').
      {
       clear - JBC_COMPOSE MEM MEM'' INCR1 INCR2 H7 H8 H9 H10 H11 H12 H13 H14.
        assert (j''_INV: forall b b' d, j'' b = Some (b',d) -> (j' b = Some (b',d)) \/
                                                           (j b = Some (b',d) /\ bc b = BCinvalid)).
        {
          intros. unfold j'' in H. destruct (bc b) eqn:BC; eauto.
             destruct (j b) as [[bb dd]|] eqn:Hj; eauto.
        }
        assert (j'_INV: forall b b' d, j' b = Some (b',d) -> (~Mem.valid_block m' b') \/
                                                         (j b = Some (b',d) /\ bc b <> BCinvalid)).
        {
          intros. destruct (jbc b) as [[b'' d']|] eqn:Hjbc.
          right.
          rewrite <- JBC_COMPOSE in Hjbc. erewrite H13 in H; eauto. inv H.
          rewrite JBC_COMPOSE in Hjbc.  unfold jbc in Hjbc.
          destruct (bc b); try congruence; split; try congruence; eauto.
          left. exploit H14; eauto. rewrite JBC_COMPOSE. eauto.
          intros [A B]. eauto.
        }
        inv MEM''.
        assert (RANGE1 : forall b ofs, bc b = BCinvalid -> loc_unmapped (compose_meminj (inj_of_bc bc) j) b ofs).
        {
          intros. red. unfold compose_meminj, inj_of_bc. rewrite H. reflexivity.
        }
        assert (RANGE2: forall b1 b2 delta ofs k p,
                   bc b1 = BCinvalid -> j b1 = Some (b2, delta) ->
                   Mem.perm m b1 ofs k p ->
                   loc_out_of_reach (compose_meminj (inj_of_bc bc) j) m b2 (ofs + delta)).          
        {
          intros. red. intros b1' delta' MAP P'.
          assert (b1 <> b1' /\ j b1' = Some (b2, delta')).
          {
            rewrite JBC_COMPOSE in MAP. unfold jbc in MAP.
            destruct (bc b1') eqn: BC'; simpl in MAP; try congruence; split; try congruence;
              eauto.
          }
          destruct H2 as [A B]. inv MEM. exploit mi_no_overlap0; eauto with mem.
          intros [C|C]. congruence. extlia.
        }
        constructor; eauto.
        -- inv mi_inj. constructor; eauto.
           ++ intros. destruct (bc b1) eqn:BC;
              unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              assert (P1: Mem.perm m b1 ofs k p).
              {
                inversion H11. apply unchanged_on_perm; eauto.
                inv MEM. destruct (Mem.sup_dec b1 (Mem.support m)).
                eauto. exploit mi_freeblocks0; eauto. congruence.
              }
              inv H. inversion H12. eapply unchanged_on_perm; eauto.
              inv MEM. eauto.
              eapply Mem.perm_inject; eauto.
           ++ intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H; eauto.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H. inversion MEM. inv mi_inj. eapply mi_align0; eauto.
              red. intros. exploit H0; eauto.
              intro. inv H11. eapply unchanged_on_perm; eauto with mem.
              eapply Mem.valid_block_inject_1; eauto.
           ++ intros. destruct (bc b1) eqn:BC; unfold j'' in H; rewrite BC in H.
              destruct (j b1) as [[b2' d']|] eqn:Hjb1; eauto.
              inv H.
              assert (P1: Mem.perm m b1 ofs Cur Readable).
              {
                inversion H11. apply unchanged_on_perm; eauto.
                inv MEM. destruct (Mem.sup_dec b1 (Mem.support m)).
                eauto. exploit mi_freeblocks0; eauto. congruence.
              }
              erewrite Mem.unchanged_on_contents; eauto.
              inv H12.
              rewrite unchanged_on_contents; eauto.
              2: eapply Mem.perm_inject; eauto. inv MEM. inv mi_inj.
              all: (eapply memval_inject_incr; eauto).
        -- (* source_range *)
          intros. unfold j''. destruct (bc b); eauto.
          destruct (j b) as [[b' d']|] eqn:Hjb; eauto.
          inv H11. exploit Mem.valid_block_inject_1; eauto. intro.
          exfalso. apply H. eapply unchanged_on_support; eauto.
        -- intros. unfold j'' in H. destruct (bc b); eauto.
           destruct (j b) as [[b'' d']|] eqn:Hjb; eauto. inv H.
           inv H12. exploit Mem.valid_block_inject_2; eauto. intro.
           eapply unchanged_on_support; eauto.
        -- red. intros.
           destruct (j''_INV _ _ _ H0) as [A|[A1 A2]];
             destruct (j''_INV _ _ _ H1) as [B|[B1 B2]]; eauto.
           ++ destruct (j'_INV _ _ _ A) as [C|[C1 C2]]; eauto.
              left. exploit Mem.valid_block_inject_2; eauto. intro. congruence.
              inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ destruct (j'_INV _ _ _ B) as [C|[C1 C2]]; eauto.
              left. exploit Mem.valid_block_inject_2. apply A1. eauto. intro. congruence.
              inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           ++ inversion MEM. eapply mi_no_overlap0; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
              eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           inversion MEM. eapply mi_representable0; eauto.
           destruct H0. left. eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
           right. eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        -- intros. destruct (j''_INV _ _ _ H) as [A|[A1 A2]]; eauto.
           destruct (Mem.perm_dec m'0 b1 ofs Max Nonempty); eauto.
           apply H9 in p0. left.
           inversion MEM. exploit mi_perm_inv0; eauto.
           inv H12. eapply unchanged_on_perm; eauto.
           intros [A|B].
           inv H11. eapply unchanged_on_perm; eauto with mem. congruence.
           eapply Mem.valid_block_inject_1; eauto. 
      }
      econstructor.
      instantiate (1:= j'').
      * eapply match_stackframes_incr; eauto.
      * eauto.
      * etransitivity; eauto. instantiate (1:= MEM'''). econstructor; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. unfold compose_meminj, inj_of_bc.
        destruct (bc b); simpl; try (rewrite H1); eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. intros. eapply H1; eauto.
        unfold compose_meminj,inj_of_bc in H4.
        destruct (bc b0); simpl in H4; try congruence;
        destruct (j b0) as [[b1 d1]|]; eauto.
        red. intros.
        eapply H14; eauto. unfold compose_meminj, inj_of_bc.
        destruct (bc b1) eqn:BC; try (rewrite H1; reflexivity). reflexivity.
        unfold j'' in H2.
        destruct (bc b1) eqn:BC; eauto. rewrite H1 in H2. eauto.
    + (* sound_state *)
      (* Part 2: constructing bc' from j' *)
      assert (JBELOW: forall b, sup_In b (Mem.support m) -> j' b = jbc b).
      {
        intros. destruct (jbc b) as [[b' delta] | ] eqn:EQ.
        rewrite <- JBC_COMPOSE in EQ.
        eapply H13; eauto.
        destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
        exploit H14; eauto. rewrite JBC_COMPOSE. eauto.
        intros [A B]. exfalso. eauto.
      }
      set (f := fun b => if Mem.sup_dec b (Mem.support m)
                      then bc b
                      else match j' b with None => BCinvalid | Some _ => BCother end).
      assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
      {
        assert (forall b, f b = BCstack -> bc b = BCstack).
        { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
        intros. apply (bc_stack bc); auto.
      }
      assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
      {
        assert (forall b id, f b = BCglob id -> bc b = BCglob id).
        { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
        intros. eapply (bc_glob bc); eauto.
      }
      set (bc' := BC f F_stack F_glob). unfold f in bc'.
      assert (BCINCR: bc_incr bc bc').
      {
        red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
      }
      assert (BC'INV: forall b, bc' b <> BCinvalid -> (exists b' delta, j' b = Some(b', delta)) \/
                                                 (bc b <> BCinvalid /\ j b = None /\ Mem.valid_block m b)).
      {
        simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        rewrite JBELOW by auto. unfold jbc.
        destruct (j b) as [[b' delta]|] eqn : Hjb.
        left.
        exists b', delta. destruct (bc b); try congruence.
        right. eauto.
        destruct (j' b) as [[b' delta] | ]. left.
        exists b', delta; auto.
        congruence.
      }
  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f.
    destruct (Mem.sup_dec b (Mem.support m)).
    rewrite JBELOW in H1 by auto.
    unfold jbc in H1. destruct (bc b); try congruence; eauto.
    rewrite H1; congruence.
  }
  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H1; constructor. eapply PMTOP; eauto.
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m'0 b Ptop).
  {
    intros; split; intros.
    - 
      exploit BC'INV; eauto. intros [(b' & delta & J') | [A [B C]]].
      exploit Mem.load_inject. eexact Hm3. eauto. eauto. intros (v' & A & B).
      eapply VMTOP; eauto.
      eapply vmatch_incr; eauto.
      eapply vmatch_top.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply D; eauto.
      erewrite Mem.load_unchanged_on_1 in H2; eauto.
      intros. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity.
    - exploit BC'INV; eauto. intros [(b'' & delta & J') | [A [B C]]].
      exploit Mem.loadbytes_inject. eexact Hm3. eauto. eauto. intros (bytes & A & B).
      inv B. inv H6. inv H18. eapply PMTOP; eauto.
      eapply pmatch_incr; eauto.
      inv MM. exploit mmatch_top. eauto.
      intros [D E]. eapply E; eauto.
      erewrite Mem.loadbytes_unchanged_on_1 in H2; eauto.
      intros. red. unfold compose_meminj, inj_of_bc.
      destruct (bc b); try congruence. rewrite B. reflexivity.
      rewrite B. reflexivity. rewrite B. reflexivity.
  }
      econstructor; eauto.
      * (*sound_stack*)
        eapply sound_stack_new_bound.
        2: inversion H11; eauto.
        eapply sound_stack_exten.
        instantiate (1:= bc).
        eapply sound_stack_inv; eauto. intros.
        eapply Mem.loadbytes_unchanged_on_1; eauto.
        intros. red. rewrite JBC_COMPOSE.
        unfold jbc. rewrite H2. reflexivity.
        intros.
        unfold bc'.  simpl. rewrite pred_dec_true; eauto.
      * (*romatch*)
        red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        -- 
        exploit RO; eauto. intros (R & P & Q).
        split; auto.
        split.
        (*bmatch*)
        apply bmatch_incr with bc; auto. apply bmatch_ext with m; auto.
        intros. inv ROACC. intro. eapply Q; eauto.
        -- destruct (j' b); congruence.
      * (*mmatch*)
        constructor; simpl; intros.
        -- apply ablock_init_sound. apply SMTOP. simpl; congruence.
        -- rewrite PTree.gempty in H2; discriminate.
        -- apply SMTOP; auto.
        -- apply SMTOP; auto.
        -- red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
           inv H11. eauto.
           destruct (j' b) as [[bx deltax] | ] eqn:J'.
           eapply Mem.valid_block_inject_1; eauto.
           congruence.
      * (*genv_match*)
        apply genv_match_exten with bc; auto.
        simpl; intros; split; intros.
        rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
        destruct (Mem.sup_dec b (Mem.support m)). auto. destruct (j' b); congruence.
        simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
      * (*bc_nostack*)
        red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
        apply NOSTK; auto.
        destruct (j' b); congruence.
Qed.

End PRESERVATION.

(** The preservation of the observable behavior of the program then
  follows. *)


Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (ro @ cc_c injp) (ro @ cc_c injp)
    (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  fsim (eapply forward_simulation_step with
                                          (match_states := fun s1 s2 => match_states prog (fst (fst w))(snd w) s1 s2
                                                                       /\ sound_state prog se1 s1
                                                                       /\ ro_mem (snd (fst w)) = m01 (snd w) )).
- destruct w as [[se rw] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser. inv Hse. 
  destruct 1. cbn in *. destruct H3. inv H3. destruct rw. inv H4. cbn in *. inv H7.
  destruct H3; try congruence; eauto.
  eapply (Genv.is_internal_match MATCH); eauto.
  unfold transf_fundef, transf_partial_fundef.
  intros ? [|] [|]; cbn -[transf_function]; inversion 1; auto.
  monadInv  H9.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros q1' q2 s1 [q1 [Hqr Hq]] Hs1. inv Hqr. inv Hq. cbn in *. inv H2.
  inv H. cbn in *. inv Hse. cbn in *. clear Hm Hm1.
  exploit transf_initial_states; eauto.
  instantiate (2:= injpw f m1 m2 Hm0).
  econstructor; eauto.
  eexists. split.
  econstructor; eauto. econstructor. eauto.
  econstructor; eauto. econstructor; eauto.
  intros (st2 & A & B & C).
  exists st2. repeat apply conj; eauto.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros s1 s2 r1 (Hs & SOUND & M0) Hr1.
  exploit transf_final_states; eauto.
  intros [r2 [Hf [r3 [Ha Hb]]]].
  exists r2. split; eauto. exists r3. split; eauto. inv Ha.
  inv H. econstructor; eauto. constructor; eauto.
- destruct w as [[se [se' rwm]] w]. destruct Hse as [Hser Hse].
  inv Hser.
  intros s1 s2 q1 (Hs & SOUND & M0) Hq1.
  edestruct transf_external_states as (w' & q2 & Hq2 & Hq & Hse' & Hk); eauto.
  exists w', q2. repeat apply conj; eauto.
  intros. exploit Hk; eauto. intros (st2 & A & B & C).
  exists st2. repeat apply conj; eauto.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros s1 t s1' STEP s2 (Hs & SOUND & M0). subst. cbn in *.
  exploit transf_step_correct; eauto.
  intros [s2' [A B]].
  exists s2'; split; auto. split; auto. split; auto. eapply sound_step; eauto.
Qed.
