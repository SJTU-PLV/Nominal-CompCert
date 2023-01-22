(** * Properties about Injections at the Asm Level *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm (* AsmFacts *).
Require Import LocalLib.
Import ListNotations.

Open Scope Z_scope.

(** ** Definition of injection between register sets *)
Definition regset_inject (j:meminj) (rs rs' : regset) : Prop :=
  forall r, Val.inject j (rs r) (rs' r).


Lemma Pregmap_gsspec_alt : forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
    (m # j <- x) i  = (if Pregmap.elt_eq i j then x else m i).
Proof.
  intros. apply Pregmap.gsspec.
Qed.


Lemma regset_inject_incr : forall j j' rs rs',
    regset_inject j rs rs' ->
    inject_incr j j' ->
    regset_inject j' rs rs'.
Proof.
  unfold inject_incr, regset_inject. intros.
  specialize (H r).
  destruct (rs r); inversion H; subst; auto.
  eapply Val.inject_ptr. apply H0. eauto. auto.
Qed.

(* copy from AsmFacts.v in ccelf *)
Lemma val_inject_set:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      v v' (VINJ: Val.inject j v v') r1 r,
      Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
  Proof.
    intros.
    destruct (PregEq.eq r1 r); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr sz rs1 r) (nextinstr sz rs2 r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto.
    apply Val.offset_ptr_inject; auto.
  Qed.
  
Lemma undef_regs_pres_inject : forall j rs rs' regs,
  regset_inject j rs rs' ->
  regset_inject j (Asm.undef_regs regs rs) (Asm.undef_regs regs rs').
Proof.
  unfold regset_inject. intros. apply val_inject_undef_regs.
  auto.
Qed.    

Lemma regset_inject_expand : forall j rs1 rs2 v1 v2 r,
  regset_inject j rs1 rs2 ->
  Val.inject j v1 v2 ->
  regset_inject j (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  intros. unfold regset_inject. intros.
  repeat rewrite Pregmap_gsspec_alt. 
  destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma regset_inject_expand_vundef_left : forall j rs1 rs2 r,
  regset_inject j rs1 rs2 ->
  regset_inject j (rs1 # r <- Vundef) rs2.
Proof.
  intros. unfold regset_inject. intros.
  rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma set_res_pres_inject : forall res j rs1 rs2,
    regset_inject j rs1 rs2 ->
    forall vres1 vres2,
    Val.inject j vres1 vres2 ->
    regset_inject j (set_res res vres1 rs1) (set_res res vres2 rs2).
Proof.
  induction res; auto; simpl; unfold regset_inject; intros.
  - rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r x); subst.
    + rewrite Pregmap.gss. auto.
    + rewrite Pregmap.gso; auto.
  - exploit (Val.hiword_inject j vres1 vres2); eauto. intros. 
    exploit (Val.loword_inject j vres1 vres2); eauto. intros.
    apply IHres2; auto.
Qed.


Lemma nextinstr_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr sz rs1) (nextinstr sz rs2).
Proof.
  unfold nextinstr. intros. apply regset_inject_expand; auto.
  apply Val.offset_ptr_inject. auto.
Qed.  


Lemma set_pair_pres_inject : forall j rs1 rs2 v1 v2 loc,
    regset_inject j rs1 rs2 ->
    Val.inject j v1 v2 ->
    regset_inject j (set_pair loc v1 rs1) (set_pair loc v2 rs2).
Proof.
  intros. unfold set_pair, Asm.set_pair. destruct loc; simpl.
  - apply regset_inject_expand; auto.
  - apply regset_inject_expand; auto.
    apply regset_inject_expand; auto.
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
Qed.


Ltac solve_val_inject :=
  match goal with
  (* | [ H : Val.inject _ (Vint _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vsingle _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vptr _ _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vsingle _) |- _] => inversion H *)
  | [ H : Val.inject _ (Vfloat _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vsingle _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vfloat _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vsingle _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vfloat _) |- _] => inversion H
  | [ |- Val.inject _ (Val.of_bool ?v) (Val.of_bool ?v) ] => apply Val.vofbool_inject
  | [ |- Val.inject _ Vundef _ ] => auto
  end.

Ltac solve_regset_inject :=
  match goal with
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j (Asm.undef_regs ?uregs ?rs1) (Asm.undef_regs ?uregs ?rs2)] =>
    apply undef_regs_pres_inject; auto
  | [ |- regset_inject _ (Asm.undef_regs _ _) _ ] =>
    unfold Asm.undef_regs; solve_regset_inject
  | [ |- regset_inject _ _ (Asm.undef_regs _ _) ] =>
    unfold Asm.undef_regs; simpl; solve_regset_inject
  | [ |- regset_inject _ (?rs1 # ?r <- ?v1) (?rs2 # ?r <- ?v2) ] =>
    apply regset_inject_expand; [solve_regset_inject | solve_val_inject]
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j ?rs1 ?rs2 ] =>
    auto
  end.

Ltac solve_opt_lessdef := 
  match goal with
  | [ |- Val.opt_lessdef (match ?rs1 ?r with
                     | _ => _
                     end) _ ] =>
    let EQ := fresh "EQ" in (destruct (rs1 r) eqn:EQ; solve_opt_lessdef)
  | [ |- Val.opt_lessdef None _ ] => constructor
  | [ |- Val.opt_lessdef (Some _) (match ?rs2 ?r with
                              | _ => _
                              end) ] =>
    let EQ := fresh "EQ" in (destruct (rs2 r) eqn:EQ; solve_opt_lessdef)
  | [ H1: regset_inject _ ?rs1 ?rs2, H2: ?rs1 ?r = _, H3: ?rs2 ?r = _ |- _ ] =>
    generalize (H1 r); rewrite H2, H3; clear H2 H3; inversion 1; subst; solve_opt_lessdef
  | [ |- Val.opt_lessdef (Some ?v) (Some ?v) ] => constructor
  end.

(* copy from SSAsmproof *)
(** Injection for cmpu_bool and cmplu_bool *)
Lemma valid_ptr_inj : forall j m m',
    Mem.inject j m m' ->
    forall b i b' delta,                                  
      j b = Some (b', delta) ->
      Mem.valid_pointer m b (Ptrofs.unsigned i) = true ->
      Mem.valid_pointer m' b' (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.valid_pointer_inject_val; eauto.
Qed.


Lemma weak_valid_ptr_inj: forall j m m',
  Mem.inject j m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  Mem.inject j m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  Mem.inject j m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply Mem.different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j m m' ->
    Val.opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j m m' ->
    Val.opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.


Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j  m m' ->
    Val.opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply Val.vofbool_inject.
Qed.
(* end of copy *)

