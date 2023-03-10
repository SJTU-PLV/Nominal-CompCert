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

(** Elimination of unneeded computations over RTL: correctness proof. *)

Require Import FunInd.
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import LanguageInterface Invariant Inject InjectFootprint.
Require Import Registers Op RTL.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp Deadcode.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun _ f tf => transf_fundef (romem_for prog) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Relating the memory states *)

(** The [magree] predicate is a variant of [Mem.inject] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [inject] relation. *)

Definition locset := block -> Z -> Prop.

Record magree (f:meminj) (m1 m2: mem) (P: locset) : Prop := mk_magree {
  ma_perm:
    forall b1 b2 ofs delta k p,
      f b1 = Some (b2,delta) -> Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p;
  ma_align:
    forall b1 b2 delta ofs chunk p,                                                  
      f b1 = Some (b2, delta) ->
     Mem.range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p -> (align_chunk chunk | delta);
  ma_perm_inv:
    forall b1 b2 delta ofs k p, f b1 = Some (b2, delta) ->
    Mem.perm m2 b2 (ofs + delta) k p -> Mem.perm m1 b1 ofs k p \/ ~Mem.perm m1 b1 ofs Max Nonempty;
  ma_memval:
    forall b1 b2 delta ofs, f b1 = Some (b2, delta) ->
    Mem.perm m1 b1 ofs Cur Readable ->
    P b1 ofs ->
    memval_inject f (ZMap.get ofs (NMap.get _ b1 (Mem.mem_contents m1)))
      (ZMap.get (ofs + delta) (NMap.get _ b2 (Mem.mem_contents m2)));
  ma_freeblocks:
    forall b, ~ Mem.valid_block m1 b -> f b = None;
  ma_mappedblocks:                                                           
    forall b b' delta, f b = Some (b', delta) -> Mem.valid_block m2 b';
  ma_no_overlap : Mem.meminj_no_overlap f m1;
 ma_representable : forall b b' delta ofs, f b = Some (b', delta) ->
                                      Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
                                        Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
                                      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
                                                           }.

Lemma magree_monotone:
  forall m1 m2 j (P Q: locset),
  magree j m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree j m1 m2 Q.
Proof.
  intros. destruct H. constructor; eauto.
Qed.

Lemma minject_agree:
  forall j m1 m2 P, Mem.inject j m1 m2 -> magree j m1 m2 P.
Proof.
  intros. destruct H. destruct mi_inj. constructor; intros; eauto.
Qed.

Lemma magree_inject:
  forall j m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree j m1 m2 P -> Mem.inject j m1 m2.
Proof.
  intros. destruct H0. constructor; eauto. constructor; eauto.
Qed.

Lemma magree_loadbytes:
  forall j m1 m2 P b1 b2 delta ofs n bytes,
  magree j m1 m2 P ->
  Mem.loadbytes m1 b1 ofs n = Some bytes ->
  j b1 = Some (b2,delta) ->
  (forall i, ofs <= i < ofs + n -> P b1 i) ->
  exists bytes', Mem.loadbytes m2 b2 (ofs + delta) n = Some bytes' /\ list_forall2 (memval_inject j) bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs j delta,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_inject j (ZMap.get i c1) (ZMap.get (i + delta) c2)) ->
    list_forall2 (memval_inject j) (Mem.getN n ofs c1) (Mem.getN n (ofs + delta) c2)).
  {
    induction n; intros; simpl.
    constructor.
    rewrite Nat2Z.inj_succ in H. constructor.
    apply H. lia.
    replace (ofs + delta + 1) with (ofs + 1 + delta) by lia.
    apply IHn. intros; apply H; lia.
  }
Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes; intros. destruct H.
  destruct (Mem.range_perm_dec m1 b1 ofs (ofs + n) Cur Readable); inv H0.
  rewrite pred_dec_true. econstructor; split; eauto.
  apply GETN. intros. rewrite Z_to_nat_max in H.
  assert (ofs <= i < ofs + n) by extlia.
  apply ma_memval0; auto.
  red; intros; eauto.
  red in r. replace (ofs0) with ((ofs0 - delta) + delta) by lia.
  eapply ma_perm0; eauto. eapply r. lia.
Qed.

Lemma magree_load:
  forall j m1 m2 P chunk b1 b2 delta ofs v,
  magree j m1 m2 P ->
  Mem.load chunk m1 b1 ofs = Some v ->
  j b1 = Some (b2, delta) ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b1 i) ->
  exists v', Mem.load chunk m2 b2 (ofs + delta) = Some v' /\ Val.inject j v v'.
Proof.
  intros. exploit Mem.load_valid_access; eauto. intros [A B].
  exploit Mem.load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split.
  apply Mem.loadbytes_load; auto.
  apply Z.divide_add_r; eauto.
  inv H. eapply ma_align0; eauto with mem.
  subst v. apply decode_val_inject; auto.
Qed.

Lemma magree_storebytes_parallel:
  forall j m1 m2 (P Q: locset) b1 b2 delta ofs bytes1 m1' bytes2,
  magree j m1 m2 P ->
  Mem.storebytes m1 b1 ofs bytes1 = Some m1' ->
  j b1 = Some (b2,delta) ->
  (forall b' i, Q b' i ->
                b' <> b1 \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 (memval_inject j) bytes1 bytes2 ->
  exists m2', Mem.storebytes m2 b2 (ofs + delta) bytes2 = Some m2' /\ magree j m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) j bytes1 bytes2 delta,
    list_forall2 (memval_inject j) bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_inject j (ZMap.get i c1) (ZMap.get (i + delta) c2)) ->
    forall q, access q ->
    memval_inject j (ZMap.get q (Mem.setN bytes1 p c1))
                   (ZMap.get (q + delta) (Mem.setN bytes2 (p + delta) c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. lia.
  - simpl length in H1; rewrite Nat2Z.inj_succ in H1.
    replace (p + delta + 1) with (p + 1 + delta) by lia.
    apply IHlist_forall2; auto.
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p).
    rewrite pred_dec_true. auto. lia. rewrite pred_dec_false.
    eapply H1; auto. unfold ZIndexed.t in *; lia. lia.
  }
  intros.
  destruct (Mem.range_perm_storebytes m2 b2 (ofs + delta) bytes2) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    replace (ofs0) with ((ofs0 - delta) + delta) by lia.
    eapply ma_perm; eauto.
    eapply Mem.storebytes_range_perm; eauto. lia. }
  exists m2'; split; auto.
  constructor; intros.
- eapply Mem.perm_storebytes_1; eauto. eapply ma_perm; eauto.
  eapply Mem.perm_storebytes_2; eauto.
- exploit ma_align; eauto. red. eauto using Mem.perm_storebytes_2.
- exploit ma_perm_inv; eauto using Mem.perm_storebytes_2.
  intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST2).
  rewrite ! NMap.gsspec. destruct (NMap.elt_eq b0 b1).
+ subst b0. rewrite H1 in H4. inv H4. rewrite pred_dec_true; auto.
  apply SETN with (access := fun ofs => Mem.perm m1' b1 ofs Cur Readable /\ Q b1 ofs); auto.
  intros. destruct H4. eapply ma_memval; eauto.
  eapply Mem.perm_storebytes_2; eauto.
+ destruct (NMap.elt_eq b3 b2).
  * subst. rewrite Mem.setN_other. eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
    intros.  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply ma_no_overlap; eauto 6 with mem.
    exploit Mem.storebytes_range_perm. eexact H0. instantiate (1:= r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto with mem. destruct H8. congruence. lia.
  * eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
- eapply ma_freeblocks; eauto with mem.
- eapply Mem.storebytes_valid_block_1; eauto with mem. eapply ma_mappedblocks; eauto.
- red. intros. eapply ma_no_overlap; eauto with mem.
- eapply ma_representable; eauto with mem.
  destruct H5. left. eapply Mem.perm_storebytes_2; eauto.
  right. eapply Mem.perm_storebytes_2; eauto.
Qed.

Lemma magree_store_parallel:
  forall j m1 m2 (P Q: locset) chunk b1 b2 delta ofs v1 m1' v2,
  magree j m1 m2 P ->
  Mem.store chunk m1 b1 ofs v1 = Some m1' ->
  vagree j v1 v2 (store_argument chunk) ->
  j b1 = Some (b2, delta) ->
  (forall b' i, Q b' i ->
                b' <> b1 \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Mem.store chunk m2 b2 (ofs + delta) v2 = Some m2' /\ magree j m1' m2' Q.
Proof.
  intros.
  exploit Mem.store_valid_access_3; eauto. intros [A B].
  exploit Mem.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto. eauto.
  instantiate (1 := Q). intros. rewrite encode_val_length in H5.
  rewrite <- size_chunk_conv in H5. apply H3; auto.
  eapply store_argument_sound; eauto.
  intros [m2' [SB2 AG]].
  exists m2'; split; auto.
  apply Mem.storebytes_store; auto.
  eapply Z.divide_add_r; eauto. eapply ma_align; eauto.
  red. intros.
  eapply Mem.perm_store_1; eauto.
  exploit A; eauto with mem.
Qed.

Lemma magree_storebytes_left:
  forall j m1 m2 P b1 ofs bytes1 m1',
  magree j m1 m2 P ->
  Mem.storebytes m1 b1 ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes1) -> ~(P b1 i)) ->
  magree j m1' m2 P.
Proof.
  intros. constructor; intros.
  - eapply ma_perm; eauto. eapply Mem.perm_storebytes_2; eauto.
  - eapply ma_align; eauto. red. intros. eauto using Mem.perm_storebytes_2.
  - exploit ma_perm_inv; eauto.
    intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
  - rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
    rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b1).
    + subst b0. rewrite Mem.setN_outside. eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
      destruct (zlt ofs0 ofs); auto. destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try lia.
      assert(ofs <= ofs0 < ofs + Z.of_nat(Datatypes.length bytes1)) by lia.
      apply H1 in H5. congruence.
    + eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
  - eapply ma_freeblocks; eauto with mem.
  - eapply ma_mappedblocks; eauto with mem.
  - red. intros. eapply ma_no_overlap; eauto with mem.
  - eapply ma_representable; eauto with mem.
    destruct H3. left. eauto with mem. right. eauto with mem.
Qed.

Lemma magree_store_left:
  forall j m1 m2 P chunk b1 ofs v1 m1',
  magree j m1 m2 P ->
  Mem.store chunk m1 b1 ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b1 i)) ->
  magree j m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply Mem.store_storebytes; eauto.
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto.
Qed.

Lemma magree_free:
  forall j m1 m2 (P Q: locset) b1 b2 delta lo hi m1',
  magree j m1 m2 P ->
  Mem.free m1 b1 lo hi = Some m1' ->
  j b1 = Some (b2, delta) ->
  (forall b' i, Q b' i ->
                b' <> b1 \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', Mem.free m2 b2 (lo + delta) (hi + delta) = Some m2' /\ magree j m1' m2' Q.
Proof.
  intros.
  destruct (Mem.range_perm_free m2 b2 (lo + delta) (hi + delta)) as [m2' FREE].
  red; intros. replace (ofs) with ((ofs - delta) + delta) by lia.
  eapply ma_perm; eauto. eapply Mem.free_range_perm; eauto. lia.
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  assert (Mem.perm m2 b3 (ofs + delta0) k p). { eapply ma_perm; eauto. eapply Mem.perm_free_3; eauto. }
  exploit Mem.perm_free_inv; eauto. intros [[A B] | A]; auto.
  subst b3. exfalso. destruct (eq_block b0 b1). subst.
  rewrite H1 in H3. inv H3.
  eelim Mem.perm_free_2. eexact H0. 2: eauto. lia.
  exploit ma_no_overlap; eauto. eapply Mem.perm_free_3; eauto with mem.
  instantiate (1:= ofs + delta0 - delta).
  apply Mem.free_range_perm in H0. red in H0. exploit H0; eauto with mem. lia.
  intros [|]. eauto. extlia.
- eapply ma_align; eauto. red. eauto using Mem.perm_free_3; eauto.
- (* inverse permissions *)
  exploit ma_perm_inv; eauto using Mem.perm_free_3. intros [A|A].
  eapply Mem.perm_free_inv in A; eauto. destruct A as [[A B] | A]; auto.
  subst b0; right; eapply Mem.perm_free_2; eauto.
  right; intuition eauto using Mem.perm_free_3.
- (* contents *)
  rewrite (Mem.free_result _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ FREE).
  simpl. eapply ma_memval; eauto. eapply Mem.perm_free_3; eauto.
  apply H2; auto. destruct (eq_block b0 b1); auto.
  subst b0. right. red; intros. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
- eapply ma_freeblocks; eauto with mem.
- eapply Mem.valid_block_free_1; eauto with mem. eapply ma_mappedblocks; eauto.
- red. intros. eapply ma_no_overlap; eauto with mem.
- eapply ma_representable; eauto with mem.
  destruct H4; eauto with mem.
Qed.

Lemma magree_valid_access:
  forall j m1 m2 (P: locset) chunk b1 b2 delta ofs p,
  magree j m1 m2 P ->
  j b1 = Some (b2, delta) ->
  Mem.valid_access m1 chunk b1 ofs p ->
  Mem.valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1; split; auto.
  red; intros. replace ofs0 with ((ofs0 - delta) + delta) by lia.
  eapply ma_perm; eauto. eapply H1; eauto. lia.
  apply Z.divide_add_r; eauto.
  eapply ma_align; eauto. red. intros. eauto with mem.
Qed.

(** * Properties of the need environment *)

Lemma add_need_all_eagree:
  forall j e e' r ne,
  eagree j e e' (add_need_all r ne) -> eagree j e e' ne.
Proof.
  intros; red; intros. generalize (H r0). unfold add_need_all.
  rewrite NE.gsspec. destruct (peq r0 r); auto with na.
Qed.

Lemma add_need_all_inject:
  forall j e e' r ne,
  eagree j e e' (add_need_all r ne) -> Val.inject j e#r e'#r.
Proof.
  intros. generalize (H r); unfold add_need_all.
  rewrite NE.gsspec, peq_true. auto with na.
Qed.

Lemma add_need_eagree:
  forall j e e' r nv ne,
  eagree j e e' (add_need r nv ne) -> eagree j e e' ne.
Proof.
  intros; red; intros. generalize (H r0); unfold add_need.
  rewrite NE.gsspec. destruct (peq r0 r); auto.
  subst r0. intros. eapply nge_agree; eauto. apply nge_lub_r.
Qed.

Lemma add_need_vagree:
  forall j e e' r nv ne,
  eagree j e e' (add_need r nv ne) -> vagree j e#r e'#r nv.
Proof.
  intros. generalize (H r); unfold add_need.
  rewrite NE.gsspec, peq_true. intros. eapply nge_agree; eauto. apply nge_lub_l.
Qed.

Lemma add_needs_all_eagree:
  forall j rl e e' ne,
  eagree j e e' (add_needs_all rl ne) -> eagree j e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_all_inject:
  forall j rl e e' ne,
  eagree j e e' (add_needs_all rl ne) -> Val.inject_list j e##rl e'##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. eapply add_need_all_inject; eauto.
  eapply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_eagree:
  forall j rl nvl e e' ne,
  eagree j e e' (add_needs rl nvl ne) -> eagree j e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  destruct nvl. apply add_needs_all_eagree with (a :: rl); auto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_needs_vagree:
  forall j rl nvl e e' ne,
  eagree j e e' (add_needs rl nvl ne) -> vagree_list j e##rl e'##rl nvl.
Proof.
  induction rl; simpl; intros.
  constructor.
  destruct nvl.
  apply vagree_inject_list. eapply add_needs_all_inject with (rl := a :: rl); eauto.
  constructor. eapply add_need_vagree; eauto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_ros_need_eagree:
  forall j e e' ros ne, eagree j e e' (add_ros_need_all ros ne) -> eagree j e e' ne.
Proof.
  intros. destruct ros; simpl in *. eapply add_need_all_eagree; eauto. auto.
Qed.

Global Hint Resolve add_need_all_eagree add_need_all_inject
             add_need_eagree add_need_vagree
             add_needs_all_eagree add_needs_all_inject
             add_needs_eagree add_needs_vagree
             add_ros_need_eagree: na.

Lemma eagree_init_regs:
  forall j rl vl1 vl2 ne,
  Val.inject_list j vl1 vl2 ->
  eagree j (init_regs vl1 rl) (init_regs vl2 rl) ne.
Proof.
  induction rl; intros until ne; intros LD; simpl.
- red; auto with na.
- inv LD.
  + red; auto with na.
  + apply eagree_update; auto with na.
Qed.

(** * Basic properties of the translation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variables se tse: Genv.symtbl.
Variable m0: mem.
Variable w : inj_world.

Hypothesis SUPm0: injw_sup_l w = Mem.support m0.
Hypothesis GE: inj_stbls w se tse.
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse tprog.
(*
Lemma match_stbls_incr: forall w',
    inj_incr w w' -> inj_stbls w' se tse.
Proof.
  intros.
  exploit inj_stbls_subrel; eauto.
Qed.
*)
Lemma functions_translated:
  forall (j: meminj) (v tv: val) (f: RTL.fundef),
  Genv.match_stbls j se tse ->
  Genv.find_funct ge v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct tge tv = Some tf /\ transf_fundef (romem_for prog) f = OK tf.
Proof.
  intros. eapply Genv.find_funct_transf_partial; eauto.
Qed.

Lemma sig_function_translated:
  forall rm f tf,
  transf_fundef rm f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros; destruct f; monadInv H.
  unfold transf_function in EQ.
  destruct (analyze (ValueAnalysis.analyze rm f) f); inv EQ; auto.
  auto.
Qed.

Lemma stacksize_translated:
  forall rm f tf,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (ValueAnalysis.analyze rm f) f); inv H; auto.
Qed.

Definition vanalyze (cu: program) (f: function) :=
  ValueAnalysis.analyze (romem_for cu) f.

Lemma transf_function_at:
  forall cu f tf an pc instr,
  transf_function (romem_for cu) f = OK tf ->
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze cu f) an pc instr).
Proof.
  intros. unfold transf_function in H. unfold vanalyze in H0. rewrite H0 in H. inv H; simpl.
  rewrite PTree.gmap. rewrite H1; auto.
Qed.

Lemma is_dead_sound_1:
  forall nv, is_dead nv = true -> nv = Nothing.
Proof.
  destruct nv; simpl; congruence.
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead nv = false -> nv <> Nothing.
Proof.
  intros; red; intros. subst nv; discriminate.
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma is_int_zero_sound:
  forall nv, is_int_zero nv = true -> nv = I Int.zero.
Proof.
  unfold is_int_zero; destruct nv; try discriminate.
  predSpec Int.eq Int.eq_spec m Int.zero; congruence.
Qed.

Lemma ros_address_translated:
  forall j ros rs trs ne,
    Genv.match_stbls j se tse ->
  eagree j rs trs (add_ros_need_all ros ne) ->
  Val.inject j (ros_address ge ros rs) (ros_address tge ros trs).
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
  specialize (H0 r). unfold NE.get in H0. cbn in H0. rewrite PTree.gss in H0. auto.
  eapply symbol_address_inject; eauto.
Qed.

(** * Semantic invariant *)

Inductive match_stackframes (j:meminj): stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp sp' pc e tf te an
        (FUN: transf_function (romem_for prog) f = OK tf)
        (ANL: analyze (vanalyze prog f) f = Some an)
        (RES: forall v tv,
              Val.inject j v tv ->
              eagree j (e#res <- v) (te#res<- tv)
                (fst (transfer f (vanalyze prog f) pc an!!pc)))
        (PC: j sp = Some (sp',0)),
      match_stackframes j (Stackframe res f (Vptr sp Ptrofs.zero) pc e)
                          (Stackframe res tf (Vptr sp' Ptrofs.zero) pc te).


Lemma vagree_incr: forall j j' v w x, vagree j v w x -> inject_incr j j' -> vagree j' v w x.
Proof.
  intros. destruct x; simpl in *; eauto.
Qed.

Lemma eagree_incr : forall j j' rs rs' x,
    eagree j rs rs' x -> inject_incr j j' -> eagree j' rs rs' x.
Proof.
  intros. red. intros.
  eapply vagree_incr; eauto.
Qed.

Lemma match_stackframes_incr : forall j j' s s',
    list_forall2 (match_stackframes j) s s' ->
    inject_incr j j' ->
    list_forall2 (match_stackframes j') s s'.
Proof.
  induction 1; intros.
  - constructor.
  - constructor; eauto. inv H.
    econstructor; eauto. intros. red.
    intros. simpl. destruct (peq r res).
    + subst. rewrite !Regmap.gss. eapply vagree_inject; eauto.
    + rewrite !Regmap.gso; eauto.
      eapply vagree_incr; eauto.
      assert (Val.inject j Vundef Vundef). constructor.
      apply RES in H2. red in H2. generalize (H2 r).
      rewrite !Regmap.gso; eauto.
Qed.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm an j sp'
        (STACKS: list_forall2 (match_stackframes j) s ts)
        (FUN: transf_function (romem_for prog) f = OK tf)
        (ANL: analyze (vanalyze prog f) f = Some an)
        (ENV: eagree j e te (fst (transfer f (vanalyze prog f) pc an!!pc)))
        (MEM: magree j m tm (nlive ge sp (snd (transfer f (vanalyze prog f) pc an!!pc))))
        (SP: j sp = Some (sp',0))
        (RO: ro_acc m0 m)
        (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc e m)
                   (State ts tf (Vptr sp' Ptrofs.zero) pc te tm)
  | match_call_states:
      forall s vf args m ts tvf targs tm j
        (STACKS: list_forall2 (match_stackframes j) s ts)
        (VF: Val.inject j vf tvf)
        (ARGS: Val.inject_list j args targs)
        (MEM: Mem.inject j m tm)
        (RO: ro_acc m0 m)
        (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
      match_states (Callstate s vf args m)
                   (Callstate ts tvf targs tm)
  | match_return_states:
      forall s v m ts tv tm j
        (STACKS: list_forall2 (match_stackframes j) s ts)
        (RES: Val.inject j v tv)
        (MEM: Mem.inject j m tm)
        (RO: ro_acc m0 m)
        (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
      match_states (Returnstate s v m)
                   (Returnstate ts tv tm).

(** [match_states] and CFG successors *)

Lemma analyze_successors:
  forall cu f an pc instr pc',
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze cu f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall s f sp pc e m ts tf te tm an pc' instr ne nm j sp'
    (STACKS: list_forall2 (match_stackframes j) s ts)
    (FUN: transf_function (romem_for prog) f = OK tf)
    (ANL: analyze (vanalyze prog f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree j e te ne)
    (MEM: magree j m tm (nlive ge sp nm))
    (SP: j sp = Some (sp',0))
    (RO: ro_acc m0 m)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
  match_states (State s f (Vptr sp Ptrofs.zero) pc' e m)
               (State ts tf (Vptr sp' Ptrofs.zero) pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B].
  econstructor; eauto.
  eapply eagree_ge; eauto.
  eapply magree_monotone; eauto.
Qed.

(** Builtin arguments and results *)

Lemma eagree_set_res:
  forall j e1 e2 v1 v2 res ne,
  Val.inject j v1 v2 ->
  eagree j e1 e2 (kill_builtin_res res ne) ->
  eagree j (regmap_setres res v1 e1) (regmap_setres res v2 e2) ne.
Proof.
  intros. destruct res; simpl in *; auto.
  apply eagree_update; eauto. apply vagree_inject; auto.
Qed.

Lemma transfer_builtin_arg_sound:
  forall bc e e' sp m m' a v j sp',
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  forall nv ne1 nm1 ne2 nm2,
  transfer_builtin_arg nv (ne1, nm1) a = (ne2, nm2) ->
  eagree j e e' ne2 ->
  magree j m m' (nlive ge sp nm2) ->
  Genv.match_stbls j se tse ->
  genv_match bc ge ->
  bc sp = BCstack ->
  j sp = Some (sp',0) ->
  exists v',
     eval_builtin_arg tge (fun r => e'#r) (Vptr sp' Ptrofs.zero) m' a  v'
  /\ vagree j v v' nv
  /\ eagree j e e' ne1
  /\ magree j m m' (nlive ge sp nm1).
Proof.
  induction 1; simpl; intros until nm2; intros TR EA MA MSTB GM SPM SPJ; inv TR.
- exists e'#x; intuition auto. constructor. eauto 2 with na. eauto 2 with na.
- exists (Vint n); intuition auto. constructor. apply vagree_inject. constructor.
- exists (Vlong n); intuition auto. constructor. apply vagree_inject. constructor.
- exists (Vfloat n); intuition auto. constructor. apply vagree_inject. constructor.
- exists (Vsingle n); intuition auto. constructor. apply vagree_inject. constructor.
- simpl in H. exploit magree_load; eauto.
  intros. eapply nlive_add; eauto with va. rewrite Ptrofs.add_zero_l in H0; auto.
  intros (v' & A & B). rewrite Z.add_0_r in A.
  exists v'; intuition auto. constructor; auto. apply vagree_inject; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Vptr sp' (Ptrofs.add Ptrofs.zero ofs)); intuition auto with na. constructor.
  eapply vagree_inject. econstructor; eauto. rewrite Ptrofs.add_zero. reflexivity.
- unfold Genv.symbol_address in H; simpl in H.
  destruct (Genv.find_symbol se id) as [b|] eqn:FS; simpl in H; try discriminate.
  eapply Genv.find_symbol_match in FS as FS'; eauto. destruct FS' as [tb [MAP FS']].
  exploit magree_load; eauto.
  intros. eapply nlive_add; eauto. constructor. apply GM; auto.
  intros (v' & A & B). rewrite Z.add_0_r in A.
  exists v'; intuition auto.
  constructor. simpl. unfold Genv.symbol_address. rewrite FS'; auto.
  apply vagree_inject; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Genv.symbol_address tse id ofs); intuition auto with na. constructor.
  eapply vagree_inject. apply symbol_address_inject; eauto.
- destruct (transfer_builtin_arg All (ne1, nm1) hi) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (vlo' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (vhi' & P & Q & R & S).
  exists (Val.longofwords vhi' vlo'); intuition auto.
  constructor; auto.
  apply vagree_inject.
  apply Val.longofwords_inject; apply inject_vagree; auto.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (v2' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (v1' & P & Q & R & S).
  econstructor; intuition auto.
  econstructor; eauto.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject, vagree_inject, inject_vagree.
Qed.

Lemma transfer_builtin_args_sound:
  forall e sp m e' m' bc al vl j sp',
  eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
  forall ne1 nm1 ne2 nm2,
  transfer_builtin_args (ne1, nm1) al = (ne2, nm2) ->
  eagree j e e' ne2 ->
  magree j m m' (nlive ge sp nm2) ->
  Genv.match_stbls j se tse ->
  genv_match bc ge ->
  bc sp = BCstack ->
  j sp = Some (sp',0) ->
  exists vl',
     eval_builtin_args tge (fun r => e'#r) (Vptr sp' Ptrofs.zero) m' al vl'
  /\ Val.inject_list j vl vl'
  /\ eagree j e e' ne1
  /\ magree j m m' (nlive ge sp nm1).
Proof.
Local Opaque transfer_builtin_arg.
  induction 1; simpl; intros.
- inv H. exists (@nil val); intuition auto. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHlist_forall2; eauto. intros (vs' & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound; eauto. intros (v1' & A2 & B2 & C2 & D2).
  exists (v1' :: vs'); intuition auto. constructor; auto.
Qed.

Lemma address_inject:
  forall j m1 m2 b1 ofs1 b2 delta p P,
  magree j m1 m2 P ->
  Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  j b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit ma_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma can_eval_builtin_arg:
  forall j sp e m e' m' P sp',
  magree j m m' P ->
  j sp = Some (sp',0)  ->
  Genv.match_stbls j se tse ->
  forall a v,
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => e'#r) (Vptr sp' Ptrofs.zero) m' a v'.
Proof.
  intros until sp'; intros MA JSP MSTB.
  assert (LD: forall chunk addr v addr',
             Mem.loadv chunk m addr = Some v ->
             Val.inject j addr addr' ->
              exists v', Mem.loadv chunk m' addr' = Some v').
  {
    intros. destruct addr; simpl in H; try discriminate. inv H0. simpl.
    eapply Mem.valid_access_load. erewrite address_inject; eauto with mem.
    eapply magree_valid_access; eauto.
    eapply Mem.load_valid_access; eauto. }
  induction 1; try (econstructor; now constructor).
  - exploit LD; eauto. econstructor; eauto.
    intros (v' & A). rewrite Ptrofs.add_zero in A. exists v'; constructor; auto.
  - exploit LD; eauto. eapply symbol_address_inject; eauto.
    intros (v' & A). exists v'; constructor; auto.
  - destruct IHeval_builtin_arg1 as (v1' & A1).
    destruct IHeval_builtin_arg2 as (v2' & A2).
    exists (Val.longofwords v1' v2'); constructor; auto.
  - destruct IHeval_builtin_arg1 as (v1' & A1).
    destruct IHeval_builtin_arg2 as (v2' & A2).
    econstructor; econstructor; eauto.
Qed.

Lemma can_eval_builtin_args:
  forall sp e m e' m' P j sp',
    magree j m m' P ->
    j sp = Some (sp',0)  ->
    Genv.match_stbls j se tse ->
    forall al vl,
      eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
      exists vl', eval_builtin_args tge (fun r => e'#r) (Vptr sp' Ptrofs.zero) m' al vl'.
Proof.
  induction 4.
- exists (@nil val); constructor.
- exploit can_eval_builtin_arg; eauto. intros (v' & A).
  destruct IHlist_forall2 as (vl' & B).
  exists (v' :: vl'); constructor; eauto.
Qed.

(** Properties of volatile memory accesses *)

Lemma match_symbols_inject:
  forall j, Genv.match_stbls j se tse -> symbols_inject j se tse.
Proof.
  intros. inv H. constructor.
  - eauto.
  - repeat apply conj.
    + intros. exploit mge_dom; eauto. eapply Genv.genv_symb_range.
      eauto. intros [x A]. rewrite H in A. inv A. split. reflexivity.
      eapply mge_symb in H0; eauto.
    + intros. exploit mge_dom; eauto. eapply Genv.genv_symb_range; eauto.
      intros [b2 A]. exists b2. split; eauto.
        eapply mge_symb in H0; eauto.
    + intros. unfold Genv.block_is_volatile. erewrite mge_info; eauto.
Qed.
  
Lemma transf_volatile_store:
  forall j v1 v2 v1' v2' m tm chunk sp nm t v m',
  volatile_store_sem chunk ge (v1::v2::nil) m t v m' ->
  Val.inject j v1 v1' ->
  vagree j v2 v2' (store_argument chunk) ->
  magree j m tm (nlive ge sp nm) ->
  Genv.match_stbls j se tse ->
  v = Vundef /\
  exists tm', volatile_store_sem chunk tge (v1'::v2'::nil) tm t Vundef tm'
           /\ magree j m' tm' (nlive ge sp nm).
Proof.
  intros. inv H. split; auto.
  inv H0. inv H10.
- (* volatile *)
  exists tm; split; auto. econstructor.
  eapply Genv.find_symbol_match in H0 as FS'; eauto. destruct FS' as [tb [MAP FS']].
  rewrite H5 in MAP. inv MAP. rewrite Ptrofs.add_zero.
  econstructor; eauto. unfold Genv.block_is_volatile in *.
  inv H3. erewrite <- mge_info; eauto.
  eapply eventval_match_inject; eauto.
  eapply match_symbols_inject; eauto.
  apply store_argument_load_result; auto.
- (* not volatile *)
  exploit magree_store_parallel. eauto. eauto. eauto. eauto.
  instantiate (1 := nlive ge sp nm). auto.
  intros (tm' & P & Q).
  exists tm'; split. econstructor. econstructor; eauto.
  unfold Genv.block_is_volatile in *. inv H3. erewrite <- mge_info; eauto.
  erewrite address_inject; eauto with mem. auto.
Qed.

Lemma eagree_set_undef:
  forall j e1 e2 ne r, eagree j e1 e2 ne -> eagree j (e1#r <- Vundef) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. destruct (peq r0 r); auto with na.
Qed.

Theorem disjoint_or_equal_inject:
  forall f m b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  Mem.meminj_no_overlap f m ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  Mem.range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  Mem.range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try lia.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit H; eauto.
  instantiate (1 := x - delta1). apply H2. lia.
  instantiate (1 := x - delta2). apply H3. lia.
  intuition.
Qed.

Lemma valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p x,
  f b1 = Some(b2, delta) ->
  magree f m1 m2 x ->
  Mem.valid_access m1 chunk b1 ofs p ->
  Mem.valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. red. red in H1. destruct H1.
  split. red. intros. replace (ofs0) with (ofs0 - delta + delta) by lia.
  eapply ma_perm; eauto. eapply H1. lia.
  apply Z.divide_add_r. eauto. eapply ma_align; eauto.
  eapply Mem.range_perm_max; eauto.
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta x,
  magree f m m' x ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by lia.
  assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
  rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (Mem.valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. lia. congruence.
  exploit valid_access_inject; eauto. intros [C D].
  congruence.
Qed.

(** * The simulation diagram *)

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' -> sound_state prog se S1 ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.

Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ _ FUN ANL INSTR);
       let TI := fresh "TI" in
       intro TI; unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.

  induction 1; intros S1' MS SS; inv MS.

- (* nop *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.

- (* op *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *. exploit inj_stbls_subrel; eauto. intro GE'. inv GE'.  
  exploit needs_of_operation_sound; eauto.
  eapply symbol_address_inject; eauto.
  intros. eapply ma_perm; eauto. eapply ma_representable; eauto. eapply ma_no_overlap; eauto.
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v := tv); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree j v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; reflexivity.
  eapply match_succ_states; eauto. simpl; auto.
  eapply eagree_update; eauto 2 with na.
+ (* preserved operation *)
  simpl in *.  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'.
  exploit needs_of_operation_sound; eauto.
  eapply symbol_address_inject; eauto.
  intros. eapply ma_perm; eauto. eapply ma_representable; eauto. eapply ma_no_overlap; eauto.
  eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v := tv); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.

- (* load *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne dst)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
  simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* preserved *)
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. cbn in *.
  exploit eval_addressing_inject. eauto. eauto. 2: eauto.
  eapply add_needs_all_inject; eauto.
  intros (ta & U & V). inv V; try discriminate.
  exploit magree_load; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_add; eauto.
  intros (tv & P & Q).
  econstructor; split.
  erewrite <- address_inject in P; eauto with mem.
  rewrite eval_shift_stack_addressing in U.
  eapply exec_Iload with (a := Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.

- (* store *)
  TransfInstr; UseTransfer.
  destruct (nmem_contains nm (aaddressing (vanalyze prog f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. simpl in *.
  exploit eval_addressing_inject. eauto. eauto. 2: eauto. eapply add_needs_all_inject; eauto.
  intros (ta & U & V). inv V; try discriminate.
  rewrite eval_shift_stack_addressing in U.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na. eauto.
  instantiate (1 := nlive ge sp0 nm).
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_remove; eauto.
  intros (tm' & P & Q).
  econstructor; split. erewrite <- address_inject in P; eauto with mem.
  eapply exec_Istore with (a := Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))). eauto.
  eauto.
  eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eauto 3 with na.
  eapply ro_acc_trans. eauto. eapply ro_acc_store; eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  erewrite <- Mem.support_store; eauto.
  erewrite <- Mem.support_store; eauto.
  
+ (* dead instruction, turned into a nop *)
  destruct a; simpl in H1; try discriminate.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  eapply ro_acc_trans. eauto. eapply ro_acc_store; eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  erewrite <- Mem.support_store; eauto.

- (* call *)
  TransfInstr; UseTransfer.
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. simpl in *.
  exploit functions_translated; eauto.
  eapply ros_address_translated; eauto 2 with na.
  intros (tfd & A & B).
  econstructor; split.
  eapply exec_Icall; eauto. eapply sig_function_translated; eauto.
  eapply match_call_states; eauto.
  constructor; auto. eapply match_stackframes_intro; eauto.
  intros.
  edestruct analyze_successors; eauto. simpl; eauto.
  eapply eagree_ge; eauto. rewrite ANPC. simpl.
  apply eagree_update; eauto with na.
  eapply ros_address_translated; eauto 2 with na.
  eauto 2 with na.
  eapply magree_inject; eauto. apply nlive_all.

- (* tailcall *)
  TransfInstr; UseTransfer.   exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. simpl in *.
  exploit functions_translated. eauto. eauto.
  eapply ros_address_translated; eauto 2 with na.
  intros (tfd & A & B).
  exploit magree_free. eauto. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & C & D).
  econstructor; split.
  eapply exec_Itailcall; eauto. eapply sig_function_translated; eauto.
  erewrite stacksize_translated by eauto. rewrite !Z.add_0_r in C. eexact C.
  eapply match_call_states; eauto 2 with na.
  eapply ros_address_translated; eauto 2 with na.
  eapply magree_inject; eauto. apply nlive_all.
  eapply ro_acc_trans. eauto. eapply ro_acc_free; eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  erewrite <- Mem.support_free; eauto.   erewrite <- Mem.support_free; eauto.

- (* builtin *)
  TransfInstr; UseTransfer. revert ENV MEM TI.
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. simpl in *.
  functional induction (transfer_builtin (vanalyze prog f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  inv H0. inv H6. rename b1 into v1.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
              nmem_add nm (aaddr_arg (vanalyze prog f) # pc a1)
                (size_chunk chunk)) a1) as (ne1, nm1) eqn: TR.
  InvSoundState. exploit transfer_builtin_arg_sound; eauto.
  intros (tv1 & A & B & C & D).
  inv H1. simpl in B. destruct tv1 eqn: Htv1. inv B. inv B. inv B. inv B. inv B.
  assert (X: exists tvres, volatile_load tge chunk tm b0 i t tvres /\ Val.inject j vres tvres).
  {
    inv H2.
    * inv B. subst. assert (delta = 0).
      inv inj_stbls_match. exploit mge_dom. eapply Genv.genv_symb_range; eauto.
      intros [b3 X]. rewrite H7 in X. inv X. reflexivity. subst.
      exploit match_symbols_inject; eauto. intro SINJ.
      exploit eventval_match_inject_2; eauto. intros (tv & X & Y).
      rewrite Ptrofs.add_zero.
      exists (Val.load_result chunk tv); split; auto. constructor; eauto.
    + simpl. unfold Genv.block_is_volatile in *. inv inj_stbls_match. erewrite <- mge_info; eauto.
    + inv inj_stbls_match. eapply mge_symb; eauto.
    + apply Val.load_result_inject. auto.
  * inv B. exploit magree_load; eauto.
    exploit aaddr_arg_sound_1; eauto. rewrite <- AN. intros.
    intros. eapply nlive_add; eassumption.
    intros (tv & P & Q).
    exists tv; split; auto. constructor; auto.
    unfold Genv.block_is_volatile in *. inv inj_stbls_match.
    erewrite <- mge_info; eauto. erewrite address_inject; eauto with mem.
  }
  destruct X as (tvres & P & Q).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  constructor. eauto. constructor.
  constructor. simpl. eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.
+ (* volatile store *)
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  destruct (transfer_builtin_arg (store_argument chunk)
              (kill_builtin_res res ne, nm) a2) as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) a1) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H3. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  exploit transf_volatile_store; eauto.
  intros (EQ & tm' & P & Q). subst vres.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  constructor. eauto. constructor. eauto. constructor.
  simpl; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply ro_acc_trans. eauto. eapply ro_acc_external with (ef := EF_vstore chunk ) ; eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  eapply external_call_support with (ef := EF_vstore chunk ). simpl. eauto.
  eapply external_call_support with (ef := EF_vstore chunk ). simpl. eauto.

+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze prog f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze prog f) # pc src) in *.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
               nmem_add (nmem_remove nm adst sz) asrc sz) dst)
           as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) src) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H3. all: eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H4. all: eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  inv H1. eapply inject_vagree in B1 as MAP1. inv MAP1.
  eapply inject_vagree in B2 as MAP2. inv MAP2.
  (*
  destruct (zeq sz 0).
  *
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m bsrc (Ptrofs.unsigned osrc) sz). lia. congruence. }
  subst.
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge (fresh_block sps) (nmem_remove nm adst 0)).
  intros. apply incl_nmem_add; auto.
  eauto. eauto.
  instantiate (1 := nlive ge (fresh_block sps) nm).
  intros. eapply nlive_remove; eauto.
  unfold adst, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  constructor.
  intros (tm' & A & B).
  eexists. split.
  eapply exec_Ibuiltin; eauto. constructor; eauto. constructor. eauto. constructor. eauto.
  simpl. econstructor; eauto. intros; extlia. intros; extlia. right. lia.
  apply Mem.loadbytes_empty. lia. erewrite address_inject. 2:apply D2. eauto.
  apply Mem.storebytes_range_perm in H16. red in H16. eapply H16. simpl. lia.
  eauto with mem.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge (fresh_block sps) (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  split. auto.
  split. eapply Mem.storebytes_empty_inject; eauto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros; extlia.
  split. apply inject_incr_refl.
  red; intros; congruence.
  *)
  exploit magree_loadbytes. eauto. eauto.  eauto.
  intros. eapply nlive_add; eauto.
  unfold asrc, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge (fresh_block sps) (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  eauto. eauto.
  instantiate (1 := nlive ge (fresh_block sps) nm).
  intros. eapply nlive_remove; eauto.
  unfold adst, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  erewrite Mem.loadbytes_length in H1 by eauto.
  rewrite Z2Nat.id in H1 by lia. auto.
  eauto.
  intros (tm' & A & B).
  destruct (zeq sz 0).
  *
    assert (bytes = nil).
    { exploit (Mem.loadbytes_empty m bsrc (Ptrofs.unsigned osrc) sz). lia. congruence. }
    inv Q.
    subst. exploit Mem.storebytes_empty; eauto. intro. subst.
    exploit Mem.storebytes_empty; eauto. intro. subst.
    econstructor; split.
    destruct (Mem.range_perm_storebytes tm' b0 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta0))) nil)
      as [m2' SB]. simpl. red. intros; extlia.
    exploit Mem.storebytes_empty; eauto. intro. subst m2'.
    eapply exec_Ibuiltin; eauto.
    constructor. eauto. constructor. eauto. constructor.
    simpl. econstructor; eauto. intros; extlia. intros; extlia. right. lia.
    eapply Mem.loadbytes_empty; eauto. lia.
    eapply match_succ_states; eauto. simpl; auto.
    apply eagree_set_res; auto. inv H14.
  *
    exploit Mem.loadbytes_length. apply H11. intros LEN.
    assert (RPSRC: Mem.range_perm m bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia.
  assert (PSRC: Mem.perm m bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
  assert (PDST: Mem.perm m bdst (Ptrofs.unsigned odst) Cur Nonempty).
  apply RPDST. lia.
  exploit address_inject. apply D2. eexact PSRC. eauto. intros EQ1.
  exploit address_inject. apply D2. eexact PDST. eauto. intros EQ2.
    econstructor; split.
    eapply exec_Ibuiltin; eauto.
    constructor. eauto. constructor. eauto. constructor.
    simpl. econstructor; eauto.
    rewrite EQ1. intros. eapply aligned_area_inject. apply D1. all: eauto.
    rewrite EQ2. intros. eapply aligned_area_inject. apply D1. all: eauto.
    rewrite EQ1. rewrite EQ2.
    eapply disjoint_or_equal_inject; eauto. eapply ma_no_overlap. apply D1.
    eapply Mem.range_perm_max with Cur; eauto.
    eapply Mem.range_perm_max with Cur; eauto. lia.
    rewrite EQ1. eauto. rewrite EQ2. eauto.
    eapply match_succ_states; eauto. simpl; auto.
    apply eagree_set_res; auto.
    eapply ro_acc_trans. eauto.
    eapply ro_acc_external with (ef := EF_memcpy sz al) (ge:= ge) ; simpl; eauto.
    econstructor. 7: eauto. 7: eauto. all: eauto.
    etransitivity. eauto. econstructor; eauto. red. intros. congruence.
    erewrite <- Mem.support_storebytes; eauto.
    erewrite <- Mem.support_storebytes; eauto.

+ (* memcpy eliminated *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze prog f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze prog f) # pc src) in *.
  inv H1.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  destruct res; auto. apply eagree_set_undef; auto.
  eapply magree_storebytes_left; eauto.
  clear H3.
  exploit aaddr_arg_sound; eauto.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto.
  rewrite Z2Nat.id in H0 by lia. auto.
  eapply ro_acc_trans. eauto.
    eapply ro_acc_external with (ef := EF_memcpy sz al) (ge:=ge) ; simpl; eauto.
    econstructor. 7: eauto. 7: eauto. all: eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  erewrite <- Mem.support_storebytes; eauto.
+ (* annot *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x2) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  constructor. eapply eventval_list_match_inject; eauto 2 with na.
  eapply match_symbols_inject; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* annot val *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x2) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1. inv B. inv H6.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  constructor.
  eapply eventval_match_inject; eauto 2 with na.
  eapply match_symbols_inject; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* debug *)
  inv H1.
  exploit can_eval_builtin_args; eauto. intros (vargs' & A).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. constructor.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction.
  }
  clear y TI.
  destruct (transfer_builtin_args (kill_builtin_res res ne, nmem_all) _x0) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  exploit external_call_mem_inject; eauto 2 with na.
  eapply magree_inject; eauto. intros. apply nlive_all.
  intros (j' & v' & tm' & P & Q & R & S & T & U & V).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply match_succ_states. instantiate (1:= j').
  eapply match_stackframes_incr; eauto.
  all: eauto.
  eauto. simpl; auto.
  apply eagree_set_res; auto. eapply eagree_incr; eauto.
  eapply minject_agree; eauto.
  eapply ro_acc_trans. eauto. eapply ro_acc_external; eauto.
  etransitivity. eauto. constructor; eauto. inv S. eauto. inv T. eauto.

- (* conditional *)
  TransfInstr; UseTransfer. destruct (peq ifso ifnot).
+ replace (if b then ifso else ifnot) with ifso by (destruct b; congruence).
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
+ econstructor; split.
  eapply exec_Icond; eauto.
  eapply needs_of_condition_sound. intros. eapply ma_perm; eauto.
  eapply ma_representable; eauto. eapply ma_no_overlap; eauto.
  eauto. eauto with na.
  eapply match_succ_states; eauto 2 with na.
  simpl; destruct b; auto.

- (* jumptable *)
  TransfInstr; UseTransfer.
  assert (INJ: Val.inject j rs#arg te#arg) by eauto 2 with na.
  rewrite H0 in INJ. inv INJ.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  eapply match_succ_states; eauto 2 with na.
  simpl. eapply list_nth_z_in; eauto.

- (* return *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & A & B). simpl in A. rewrite Z.add_0_r in A.
  econstructor; split.
  eapply exec_Ireturn; eauto.
  erewrite stacksize_translated by eauto. eexact A.
  econstructor; eauto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_inject; eauto. apply nlive_all.
  eapply ro_acc_trans. eauto. eapply ro_acc_free; eauto.
  etransitivity. eauto. constructor; eauto. red. intros. congruence.
  erewrite <- Mem.support_free; eauto.
  erewrite <- Mem.support_free; eauto.

- (* internal function *)
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'.
  exploit functions_translated; eauto. intros (tf & FIND' & FUN).
  monadInv FUN. generalize EQ. unfold transf_function. fold (vanalyze prog f). intros EQ'.
  destruct (analyze (vanalyze prog f) f) as [an|] eqn:AN; inv EQ'.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (j' & tm' & A & B & C & D & E & F).
  econstructor; split.
  econstructor; simpl; eauto.
  simpl. econstructor. instantiate (1:= j'). all: eauto.
  eapply match_stackframes_incr; eauto.
  apply eagree_init_regs; auto. eauto with mem.
  apply minject_agree; auto.
  eapply ro_acc_trans. eauto. eapply ro_acc_alloc; eauto.
  etransitivity. eauto. constructor; eauto. red. intros.
  destruct (eq_block b stk). subst. rewrite E in H1. inv H1.
  split.
  apply Mem.fresh_block_alloc in H. eauto.
  apply Mem.fresh_block_alloc in B. eauto.
  rewrite F in H1; eauto. congruence.
  apply Mem.alloc_unchanged_on with (P:= fun _ _ => True) in H. inv H. eauto.
  apply Mem.alloc_unchanged_on with (P:= fun _ _ => True) in B. inv B. eauto.
  
- (* external function *)
  exploit inj_stbls_subrel; eauto. intro GE'. inv GE'. simpl in *.
  exploit functions_translated; eauto. intros (tf & FIND' & FUN).
  exploit external_call_mem_inject; eauto.
  intros (j' & res' & tm' & A & B & C & D & E & F & G).
  simpl in FUN. inv FUN.
  econstructor; split.
  econstructor; eauto.
  econstructor. instantiate (1:= j'). all: eauto.
  eapply match_stackframes_incr; eauto.
  eapply ro_acc_trans. eauto. eapply ro_acc_external; eauto.
  etransitivity. eauto. constructor; eauto.
  eapply external_call_support; eauto.
  eapply external_call_support; eauto.

- (* return *)
  inv STACKS. inv H1.
  econstructor; split.
  constructor.
  econstructor; eauto. apply minject_agree. auto.
Qed.

Definition ro_w := (se,(row se m0),w).
Lemma transf_initial_states:
  forall q1 q2 st1, match_query  (ro @ cc_c inj) ro_w q1 q2 -> initial_state ge q1 st1 ->
  exists st2, initial_state tge q2 st2 /\ match_states st1 st2 /\ sound_state prog ge st1.
Proof.
  intros. destruct H as [x [H1 H2]]. inv H0. inv H1. inv H2. cbn in *. inv H0.
  exploit functions_translated; eauto. inversion GE. eauto.
  intros (tf & FIND & TFD).
  exists (Callstate nil vf2 vargs2 m2); repeat apply conj.
  - setoid_rewrite <- (sig_function_translated (romem_for prog) (Internal f)); eauto.
    monadInv TFD. constructor; auto.
  - cbn in *. econstructor; eauto.
    constructor.  rewrite H5. eapply ro_acc_refl.
    destruct w. simpl. cbn in *. inv H9. reflexivity.
  - eapply sound_memory_ro_sound_state; eauto. inversion GE. eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r1, match_states st1 st2 -> final_state st1 r1 ->
  exists r2, final_state st2 r2 /\ match_reply (ro @ cc_c inj) ro_w r1 r2.
Proof.
  intros. inv H0. inv H. inv STACKS.
  exists (cr tv tm). split. constructor.
  exists (cr r m). split. cbn. constructor. constructor. eauto.
  (*we can provide in match_state*)
  exists (injw j (Mem.support m) (Mem.support tm)). split; auto.
  constructor; eauto. constructor; eauto.
Qed.

Lemma transf_external_states:
  forall st1 st2 q1, match_states st1 st2 -> sound_state prog ge st1 -> at_external ge st1 q1 ->
  exists w' q2, at_external tge st2 q2 /\ match_query (ro @ cc_c injp) w' q1 q2 /\ match_senv (ro @ cc_c injp) w' se tse /\
  forall r1 r2 st1', match_reply (ro @ cc_c injp) w' r1 r2 -> after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states st1' st2' /\ sound_state prog ge st1'.
Proof.
  intros st1 st2 q1 Hst Hs Hq1. destruct Hq1. inv Hst.
  exploit inj_stbls_subrel; eauto. intros [MSTB SUP1 SUP2]. simpl in MSTB,SUP1,SUP2.
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
      inv GE. inversion INCR. eauto.
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
    apply MSTB. eauto. eauto.
  - inv H2. destruct H1 as (r3 & Hr1& Hr2). inv Hr1. inv H1. rename H3 into ROACC.
    destruct Hr2 as ([j' s1 s2 MEM''] & Hw' & Hr).
    inv Hw'.
    inv Hr. cbn in *. inv H5. simpl in *.
    eexists (Returnstate ts vres2 m2'); split.
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
      assert(MEM''' : Mem.inject j'' m' m2').
      {
       clear - JBC_COMPOSE MEM MEM'' INCR1 INCR2 H7 H8 H9 H10 H11 H12 H13 H14.
        assert (j''_INV: forall b b' d, j'' b = Some (b',d) -> (j' b = Some (b',d)) \/
                                                           (j b = Some (b',d) /\ bc b = BCinvalid)).
        {
          intros. unfold j'' in H. destruct (bc b) eqn:BC; eauto.
             destruct (j b) as [[bb dd]|] eqn:Hj; eauto.
        }
        assert (j'_INV: forall b b' d, j' b = Some (b',d) -> (~Mem.valid_block tm b') \/
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
           destruct (Mem.perm_dec m' b1 ofs Max Nonempty); eauto.
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
      * eauto.
      * eapply ro_acc_trans; eauto.
      * etransitivity; eauto. constructor; eauto.
(*        instantiate (1:= MEM'''). econstructor; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. unfold compose_meminj, inj_of_bc.
        destruct (bc b); simpl; try (rewrite H1); eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros. red. red in H1. intros. eapply H1; eauto.
        unfold compose_meminj,inj_of_bc in H4.
        red. intros.
        destruct (bc b); simpl in H4; try congruence;
          destruct (j b) as [[b1 d1]|]; eauto.
 *)
        red. intros.
        eapply H14; eauto. unfold compose_meminj, inj_of_bc.
        destruct (bc b) eqn:BC; try (rewrite H1; reflexivity). reflexivity.
        unfold j'' in H2.
        destruct (bc b) eqn:BC; eauto. rewrite H1 in H2. eauto.
        inv H11. eauto. inv H12. eauto.
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
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
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
        exploit RO0; eauto. intros (R & P & Q).
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

(** * Semantic preservation *)


Theorem transf_program_correct' prog tprog:
  match_prog prog tprog ->
  forward_simulation (ro @ cc_c injp) (ro @ cc_c inj)
    (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  fsim (eapply forward_simulation_step with
                                          (match_states := fun s1 s2 => match_states prog (fst (fst w)) (ro_mem (snd (fst w))) (snd w) s1 s2
                                                                       /\ sound_state prog se1 s1
                                                                       /\ Mem.support (ro_mem (snd (fst w))) = injw_sup_l (snd w) )).
- destruct w as [[se rw] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser. inv Hse. 
  destruct 1. cbn in *. destruct H0. inv H0. destruct rw. inv H2. cbn in *. inv H1. cbn in *.
  inv H8. cbn in *.
  destruct H5; try congruence; eauto.
  eapply (Genv.is_internal_match MATCH); eauto.
  unfold transf_fundef, transf_partial_fundef.
  intros ? [|] [|]; cbn -[transf_function]; inversion 1; auto.
  monadInv  H3.
- destruct w as [[se [se' rwm]] w]. cbn in *. destruct Hse as [Hser Hse].
  inv Hser.
  intros q1' q2 s1 [q1 [Hqr Hq]] Hs1. inv Hqr. inv Hq. cbn in *. inv H2.
  inv H. cbn in *. inv Hse. cbn in *.
  exploit transf_initial_states; eauto.
  instantiate (2:= injw f (Mem.support m1) (Mem.support m2)). instantiate (1:= m1).
  reflexivity.
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
  exploit step_simulation; eauto.
  intros [s2' [A B]].
  exists s2'; split; auto. split; auto. split; auto. eapply sound_step; eauto.
Qed.

Require Import CallconvAlgebra CKLRAlgebra.
Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (ro @ cc_c injp) (ro @ cc_c injp) (RTL.semantics prog) (RTL.semantics tprog).
Proof.
Abort.

(*
Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (vamatch @ cc_c ext) (vamatch @ cc_c ext) (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros MATCH. eapply source_invariant_fsim; eauto using rtl_vamatch. revert MATCH.
  fsim eapply forward_simulation_step with (match_states := match_states prog se1);
    cbn in *; subst.
- destruct 1. cbn. CKLR.uncklr. destruct H as [vf|]; try congruence.
  eapply (Genv.is_internal_transf_partial_id MATCH).
  intros [|] [|] TFD; monadInv TFD; auto.
- intros q1 q2 s1 Hq (Hs1 & _).
  eapply transf_initial_states; eauto.
- intros s1 s2 r1 Hs (Hr1 & _).
  eapply transf_final_states; eauto.
- intros s1 s2 q1 Hs (Hq1 & _).
  edestruct transf_external_states as (q2 & Hq2 & Hq & _ & Hk); eauto.
  exists tt, q2. repeat apply conj; eauto.
  intros r1 r2 s1' Hr (Hs1' & _). eauto.
- intros s1 t s1' (STEP & [se bc0 m0] & Hse & Hs1 & Hs1') s2 Hs. subst. cbn in *.
  eapply step_simulation; eauto.
Qed.
*)
