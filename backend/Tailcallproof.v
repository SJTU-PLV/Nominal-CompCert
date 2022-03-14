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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    lia.
    destruct (f!pc); try lia.
    destruct i; try lia.
    generalize (IHn n0). lia.
    generalize (IHn n0). lia.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  lia.
  destruct n2. extlia. assert (n1 <= n2)%nat by lia.
  simpl. destruct f!pc; try lia. destruct i; try lia.
  generalize (IHn1 n2 n H0). lia.
  generalize (IHn1 n2 n H0). lia.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. extlia. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. lia.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. lia.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. lia. lia.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. lia. lia.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  destruct (is_return niter f n r && tailcall_is_possible s &&
            rettype_eq (sig_res s) (sig_res (fn_sig f))) eqn:B.
- InvBooleans. eapply transf_instr_tailcall; eauto. eapply is_return_charact; eauto.
- constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable fn_stack_requirements : ident -> Z.
Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Definition regset_inject (f: meminj) (rs rs': regset): Prop :=
  forall r, Val.inject f rs#r rs'#r.

Lemma regs_inject:
  forall f rs rs', regset_inject f rs rs' -> forall l, Val.inject_list f rs##l rs'##l.
Proof.
  induction l; simpl. constructor. constructor; auto.
Qed.

Lemma set_reg_inject:
  forall f rs rs' r v v',
  regset_inject f rs rs' -> Val.inject f v v' ->
  regset_inject f (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma set_res_inject:
  forall f rs rs' res v v',
  regset_inject f rs rs' -> Val.inject f v v' ->
  regset_inject f (regmap_setres res v rs) (regmap_setres res v' rs').
Proof.
  intros. destruct res; auto. apply set_reg_inject; auto.
Qed.

Lemma regset_inject_incr:
  forall f f' rs rs', regset_inject f rs rs' -> inject_incr f f' -> regset_inject f' rs rs'.
Proof.
  intros; red; intros. apply val_inject_incr with f; auto.
Qed.

Lemma regset_undef_inject:
  forall f, regset_inject f (Regmap.init Vundef) (Regmap.init Vundef).
Proof.
  intros; red; intros. rewrite Regmap.gi. auto.
Qed.

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto.
Qed.

Definition meminj_global (j:meminj) : Prop :=
  forall id b delta, j (Global id) = Some (b,delta) ->
                b = Global id /\ delta = 0.

Lemma find_function_translated:
  forall ros rs rs' f j,
  find_function ge ros rs = Some f ->
  meminj_preserves_globals ge j ->
  meminj_global j ->
  regset_inject j rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until j; destruct ros; simpl.
  intros. inversion H0.
  assert (rs'#r = rs#r).
    generalize (H2 r). intro LD.
    unfold Genv.find_funct in H. repeat destr_in H.
    unfold Genv.find_funct_ptr in H6. repeat destr_in H6.
    apply Genv.genv_defs_range in Heqo. apply Genv.genv_sup_glob in Heqo.
    destruct Heqo. subst. inv LD. apply H1 in H7. inv H7. auto.
    rewrite H5. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma ros_is_ident_translated:
  forall ros rs rs' j id,
    ros_is_ident ros rs id ->
    regset_inject j rs rs' ->
    meminj_global j ->
    ros_is_ident ros rs' id.
Proof.
  intros. destruct ros; simpl in *.
  generalize (H0 r). intro. inv H2; (try congruence).
  rewrite H in H3. inv H3. apply H1 in H5. inv H5. auto. auto.
Qed.


Lemma eval_builtin_arg_inject:
  forall rs sp m j rs' sp' m' a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals ge j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  exists v',
     eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
  /\ Val.inject j v v'.
Proof.
  induction 1; intros SP GL RS MI.
- exists rs'#x; split; auto. constructor.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- simpl in H. exploit Mem.load_inject; eauto. rewrite Z.add_0_r.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. simpl. econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- {assert (Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    rewrite symbols_preserved. rewrite FS. inv GL. apply H0 in FS.
    econstructor; eauto. rewrite Ptrofs.add_zero. auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; auto with barg. }
- econstructor; split; eauto with barg.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destr. inv GL.
  apply H in Heqo. econstructor; eauto. rewrite Ptrofs.add_zero. auto. constructor.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  exists (Val.longofwords v1' v2'); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  econstructor; split; eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma eval_builtin_args_inject:
  forall rs sp m j rs' sp' m' al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals ge j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  exists vl',
     eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; intros.
- exists (@nil val); split; constructor.
- simpl in H4.
  exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app.
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes (j:meminj):
  nat -> list nat -> list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      meminj_preserves_globals ge j ->
      meminj_global j ->
      match_stackframes j 0 nil nil nil
  | match_stackframes_normal: forall n l stk stk' res sp sp' pc rs rs' f,
      match_stackframes j n l stk stk' ->
      regset_inject j rs rs' ->
      j sp = Some (sp',0) ->
      match_stackframes j 0 ((S n)::l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp' Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall n l stk stk' res sp pc rs f,
      match_stackframes j n l stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes j (S n) l
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

Lemma match_stackframes_global : forall j n l stk stk',
    match_stackframes j n l stk stk' ->
    meminj_preserves_globals ge j /\ meminj_global j.
Proof.
  intros. induction H; auto.
Qed.

Lemma match_stackframes_incr : forall j j' stk stk' n l,
    match_stackframes j n l stk stk' ->
    inject_incr j j' ->
    incr_without_glob j j' ->
    match_stackframes j' n l stk stk'.
Proof.
  intros.
  induction H; constructor; auto.
  - inversion H. inv H4.
    split. eauto.
    split. intros.
    apply Genv.find_var_info_iff in H4 as A. apply Genv.genv_defs_range in A.
    apply Genv.genv_sup_glob in A. destruct A. subst. eauto.
    intros.
    destruct (j b1) eqn:?.
    + destruct p. apply H0 in Heqo as H8. rewrite H7 in H8.
      inv H8.
      exploit H6. eauto. eauto. auto.
    + exploit H1; eauto.
    apply Genv.find_var_info_iff in H4 as A. apply Genv.genv_defs_range in A.
    apply Genv.genv_sup_glob in A. destruct A. subst.
    intros [A B]. inv B.
  - unfold meminj_global in *. intros.
    destruct (j (Global id)) eqn:?. destruct p.
    apply H0 in Heqo as H4. rewrite H3 in H4. inv H4.
    apply H2 in Heqo. inv Heqo. auto.
    exploit H1; eauto. intros [A B]. inv A.
  - eapply regset_inject_incr; eauto.
Qed.
(*
Inductive match_depth :
  nat -> list nat -> nat -> nat -> Prop :=
  | match_depth_nil : match_depth 0 nil 0 0
  | match_depth_left : forall l d1 d2 n,
      match_depth n l d1 d2 ->
      match_depth (S n) l (S d1) d2
  | match_depth_cons : forall l d1 d2 n,
      match_depth n l d1 d2 ->
      match_depth 0 ((S n)::l) (S d1) (S d2).
*)

Inductive tc_depth : list nat -> nat -> nat -> Prop :=
  | depth_nil : tc_depth nil 0 0
  | depth_cons l d1 d2 n:
      tc_depth l (d1 - (S n)) d2 ->
      tc_depth (S n::l) d1 (S d2).

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

Inductive tc_sizes : list nat -> Memory.stackadt -> Memory.stackadt -> Prop :=
| sizes_nil: tc_sizes nil nil nil
| sizes_cons l s1 s2 t1 n t2:
    tc_sizes l (drop (S n) s1) s2 ->
    take (S n) s1 = Some t1 ->
    Memory.stack_size t1 = Memory.size_of_all_frames t2 ->
    tc_sizes (S n::l) s1 (t2 :: s2).

Lemma tc_sizes_upstar:
  forall n g s1 s2,
    tc_sizes (n :: g) s1 s2 ->
    tc_sizes (S n :: g) ((nil) :: s1) s2.
Proof.
  intros n g s1 s2 SZ.
  inv SZ. simpl in *. repeat destr_in H2.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  auto.
Qed.

Lemma tc_sizes_upstar':
  forall n g s1 s2 t f,
    tc_sizes (n :: g) s1 (t::s2) ->
    tc_sizes (S n :: g) ((f::nil) :: s1) ((f::t)::s2).
Proof.
  intros n g s1 s2 f l SZ.
  inv SZ. simpl in *. repeat destr_in H5.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  simpl in *. lia.
Qed.

Lemma tc_sizes_up:
  forall g s1 s2,
    tc_sizes g s1 s2 ->
    tc_sizes (1%nat :: g) ((nil) :: s1) ((nil) :: s2).
Proof.
  intros g s1 s2 SZ. econstructor; simpl; eauto.
Qed.

Lemma tc_sizes_record:
  forall g t1 s1 t2 s2 f
    (SZ: tc_sizes g (t1 :: s1) (t2 :: s2)),
    tc_sizes g ((f::t1):: s1) ((f::t2) :: s2).
Proof.
  intros. inv SZ.
  simpl in *. repeat destr_in H4.
  econstructor; simpl; auto. rewrite Heqo. eauto.
  simpl in *. lia.
Qed.

Theorem stack_tc_size_vm: forall l stk stk',
    tc_sizes l stk stk' -> Memory.stack_size stk = Memory.stack_size stk'.
Proof.
  intros. induction H. auto.
  simpl. apply take_drop in H0. rewrite H0.
  rewrite Memory.stack_size_app. lia.
Qed.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f j sp' n l
             (STACKS: match_stackframes j n l s s')
             (STREE: tc_depth ((S n)::l) (Mem.sdepth m) (Mem.sdepth m'))
             (ASTK: tc_sizes ((S n)::l)(Mem.astack (Mem.support m)) (Mem.astack(Mem.support m')))
             (RINJ: regset_inject j rs rs')
             (MINJ: Mem.inject j m m')
             (SP: j sp = Some (sp',0)),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' id j n l,
      match_stackframes j n l s s' ->
      tc_depth ((S n)::l)(S (Mem.sdepth m))(S (Mem.sdepth m')) ->
      tc_sizes ((S n)::l)(Mem.astack (Mem.support m)) (Mem.astack(Mem.support m')) ->
      Val.inject_list j args args' ->
      Mem.inject j m m' ->
      match_states (Callstate s f args m id)
                   (Callstate s' (transf_fundef f) args' m' id)
  | match_states_return:
      forall s v m s' v' m' j n l,
      match_stackframes j n l s s' ->
      tc_depth (S n::l) (S(Mem.sdepth m)) (S(Mem.sdepth m')) ->
      tc_sizes l (drop (S n)(Mem.astack (Mem.support m)))(tl (Mem.astack(Mem.support m'))) ->
      Val.inject j v v' ->
      Mem.inject j m m' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' j n l
             (STACKS: match_stackframes j n l s s')
             (STREE: tc_depth (S n::l)
                              (Mem.sdepth m)
                              (S(Mem.sdepth m')))
             (STK: tc_sizes l (drop (S n)(Mem.astack (Mem.support m)))
                            (tl (Mem.astack(Mem.support m'))))
             (MLD: Mem.inject j m m'),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.inject j (rs#r) v' ->
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m').

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m id => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, step fn_stack_requirements ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step fn_stack_requirements tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. econstructor; eauto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. lia. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
  exploit eval_operation_inject; eauto. eapply match_stackframes_global; eauto.
  intros [v' [EVAL' VINJ]].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.
  rewrite eval_shift_stack_operation in EVAL'.
  erewrite eval_operation_preserved in EVAL'; eauto. symmetry. apply symbols_preserved.
  econstructor; eauto. apply set_reg_inject; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. lia. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
  exploit eval_addressing_inject; eauto. eapply match_stackframes_global; eauto.
  intros [a' [ADDR' AINJ]].
  exploit Mem.loadv_inject; eauto.
  intros [v' [LOAD' VINJ]].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.
  rewrite eval_shift_stack_addressing in ADDR'. rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  TransfInstr.
  assert (Val.inject_list j (rs##args) (rs'##args)). apply regs_inject; auto.
  exploit eval_addressing_inject; eauto. eapply match_stackframes_global; eauto.
  intros [a' [ADDR' AINJ]].
  exploit Mem.storev_mapped_inject. 2: eexact H1. eauto. eauto. apply RINJ.
  intros [m'1 [STORE' MINJ']].
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.
  rewrite eval_shift_stack_addressing in ADDR'. rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  apply Mem.support_store in H1 as S.
  apply Mem.support_storev in STORE' as S'.
  econstructor; eauto. unfold Mem.sdepth in *. congruence. congruence.

- (* call *)
  apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp' 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H10.
    red; intros; extlia.
  destruct X as [m'' FREE].
  assert ({ m''' | Mem.return_frame m'' = Some m'''}).
  apply Mem.active_return_frame. inv STREE.
  apply Mem.sdepth_active. unfold Mem.sdepth in *.
  erewrite Mem.support_free; eauto. congruence.
  destruct X as [m''' RETURN].
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m''' id); split.
  eapply exec_Itailcall; eauto.
  eapply ros_is_ident_translated; eauto.
  apply sig_preserved.
  inv ASTK. erewrite <- Mem.astack_return_frame. 2: eauto.
  erewrite Mem.support_free; eauto. congruence.
  econstructor. eapply match_stackframes_tail; eauto.
  inv STREE. simpl. constructor. simpl.
  erewrite <- Mem.sdepth_free in H8; eauto.
  erewrite <- Mem.sdepth_return_frame in H8; eauto.
  unfold Mem.sdepth in *. simpl in *.  congruence.
  simpl. apply tc_sizes_upstar. apply Mem.astack_return_frame in RETURN.
  apply Mem.support_free in FREE. congruence.
  apply regs_inject; auto.
  eapply Mem.return_frame_right_inject. 2: eauto.
  eapply Mem.free_right_inject; eauto.
  eapply Mem.push_stage_left_inject; eauto.
  rewrite stacksize_preserved. rewrite H10. intros. extlia.
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp' Ptrofs.zero) pc' rs' :: s')(transf_fundef fd) (rs'##args) (Mem.push_stage m') id); split.
  eapply exec_Icall; eauto. eapply ros_is_ident_translated; eauto.
  apply sig_preserved.
  econstructor. constructor; eauto.
  constructor. simpl. rewrite Nat.sub_0_r. auto.
  apply tc_sizes_up. auto.
  apply regs_inject; auto. eapply Mem.push_stage_inject; eauto.

- (* tailcall *)
  apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE INJ]].
  exploit Mem.return_frame_parallel_inject; eauto.
  inv STREE. apply Mem.sdepth_active. unfold Mem.sdepth in *.
  erewrite Mem.support_free; eauto. congruence.
  intros [m'2 [RET INJ']].
  apply Mem.support_free in H3 as SF. apply Mem.support_free in FREE as SF'.
  apply Mem.astack_return_frame in H4 as ARET.
  apply Mem.astack_return_frame in RET as ARET'.
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'2 id); split.
  eapply exec_Itailcall; eauto. eapply ros_is_ident_translated; eauto.
  apply sig_preserved.
  rewrite stacksize_preserved; eauto. simpl in FREE.
  rewrite Z.add_0_r in FREE. auto. inv ASTK. congruence.
  econstructor. eauto.
  erewrite Mem.sdepth_return_frame; eauto.
  erewrite Mem.sdepth_return_frame; eauto.
  unfold Mem.sdepth in *. congruence. congruence.
  apply regs_inject; auto. auto.

- (* builtin *)
  apply match_stackframes_global in STACKS as GLOB. destruct GLOB.
  TransfInstr. exploit eval_builtin_args_inject; eauto.
  intros (vargs' & P & Q).
  exploit Mem.push_stage_inject; eauto. intro.
  exploit external_call_mem_inject'; eauto.
  intros [f' [v' [m'1 [A [B [C [D [E [F [G I]]]]]]]]]].
  exploit Mem.pop_stage_parallel_inject; eauto.
  erewrite <- external_call_astack; eauto.
  simpl. congruence.
  intros (m'2 & Y & EXT').
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' (regmap_setres res v' rs') m'2); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor. 5 : eauto. all: eauto.
  eapply match_stackframes_incr; eauto.
  apply external_call_sdepth in A. apply external_call_sdepth in H1.
  unfold Mem.sdepth in *. simpl in *. apply Mem.stack_pop_stage in Y.
  apply Mem.stack_pop_stage in H2. congruence.
  apply external_call_astack in A. apply external_call_astack in H1.
  apply Mem.astack_pop_stage in H2. apply Mem.astack_pop_stage in Y.
  destruct H2. destruct Y. simpl in *. congruence.
  apply set_res_inject; eauto. eapply regset_inject_incr; eauto.

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_inject with j (rs##args) m; auto. apply regs_inject; auto.
  econstructor; eauto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp' Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RINJ arg). rewrite H0. intro. inv H2. auto.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE INJ]].
  exploit Mem.return_frame_parallel_inject; eauto.
  inv STREE.
  apply Mem.sdepth_active. unfold Mem.sdepth in *.
  erewrite Mem.support_free; eauto. congruence.
  intros [m'2 [RET INJ']].
  apply Mem.support_free in H0 as SF. apply Mem.support_free in FREE as SF'.
  apply Mem.astack_return_frame in H1 as ARET.
  apply Mem.astack_return_frame in RET as ARET'.
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'2); split.
  eapply exec_Ireturn; auto. rewrite stacksize_preserved; eauto. simpl in FREE.
  rewrite Z.add_0_r in FREE. eauto. eauto. inv ASTK. congruence.
  econstructor. eauto.
  erewrite <- Mem.sdepth_free in STREE; eauto.
  erewrite <-(Mem.sdepth_free m'0 _ _ _ _ FREE) in STREE.
  rewrite <- (Mem.sdepth_return_frame _ _ RET) in STREE.
  rewrite <- (Mem.sdepth_return_frame _ _ H1) in STREE. auto.
  inv ASTK. rewrite <- ARET'. rewrite SF'. rewrite <- H5. simpl.
  rewrite <- ARET. rewrite SF. auto.
  destruct or; simpl. apply RINJ. constructor. auto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  econstructor. eauto. erewrite <- Mem.sdepth_free in STREE; eauto.
  erewrite <- Mem.sdepth_return_frame in STREE; eauto.
  erewrite <- Mem.astack_return_frame. 2: eauto. apply Mem.support_free in H0.
  congruence. simpl. constructor.
  eapply Mem.return_frame_left_inject. 2: eauto.
  eapply Mem.free_left_inject; eauto.

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  econstructor. eauto. erewrite <- Mem.sdepth_free in STREE; eauto.
  erewrite <- Mem.sdepth_return_frame in STREE; eauto.
  erewrite <- Mem.astack_return_frame. 2: eauto. apply Mem.support_free in H0.
  congruence. simpl. auto.
  eapply Mem.return_frame_left_inject. 2: eauto.
  eapply Mem.free_left_inject; eauto.

- (* internal call *)
  exploit Mem.alloc_frame_parallel_inject; eauto. intros [m'1 [path' [ALLOCF INJ]]].
  exploit Mem.alloc_parallel_inject; eauto.
    instantiate (1 := 0). lia.
    instantiate (1 := fn_stacksize f). lia.
  intros (f' & m'2 & b2 & ALLOC & INJ' & INCR & TSP & INC).
  apply Mem.astack_alloc_frame in H as AAF.
  apply Mem.astack_alloc_frame in ALLOCF as AAF'.
  exploit Mem.record_frame_parallel_inject; eauto.
  inv H10. erewrite Mem.support_alloc; eauto. unfold sup_incr. destr.
  simpl. congruence.
  apply stack_tc_size_vm in H10.
  erewrite Mem.support_alloc; eauto. apply Mem.support_alloc in H0.
  unfold sup_incr in *. destr. destr_in H0. simpl in *. rewrite <- AAF'.
  rewrite H0. simpl. rewrite <- AAF. lia.
  intros (m'3 & RECORD & INJ'').
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H2 as [EQ1 [EQ2 EQ3]].
  left. econstructor; split.
  simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. econstructor. 3: eauto.
  eapply match_stackframes_incr; eauto.
  intro. intros. destruct (eq_block b stk).
  subst. rewrite TSP in H3. inv H3.
  apply Mem.alloc_result_stack in H0.
  apply Mem.alloc_result_stack in ALLOC. auto.
  apply INC in n0. congruence.
  erewrite Mem.sdepth_record_frame; eauto.
  erewrite Mem.sdepth_alloc; eauto. erewrite Mem.sdepth_alloc_frame; eauto.
  erewrite (Mem.sdepth_record_frame _ _ _ RECORD); eauto.
  erewrite (Mem.sdepth_alloc _ _ _ _ _ ALLOC); eauto.
  erewrite (Mem.sdepth_alloc_frame _ _ _ _ ALLOCF); eauto.
  apply Mem.astack_alloc_frame in H. apply Mem.astack_alloc_frame in ALLOCF.
  apply Mem.support_alloc in H0. apply Mem.support_alloc in ALLOC.
  apply Mem.astack_record_frame in H1. apply Mem.astack_record_frame in RECORD.
  destruct H1 as (a&b&c&d). destruct RECORD as (w&x&y&z).
  rewrite z. rewrite d.  apply tc_sizes_record. rewrite H in H10.
  rewrite H0 in c. unfold sup_incr in c. destr_in c. simpl in c.
  rewrite c in H10. rewrite AAF' in H10. unfold sup_incr in ALLOC.
  destr_in ALLOC. simpl in ALLOC. rewrite <- y. rewrite ALLOC.
  simpl. congruence.
  apply init_regs_inject.
  eapply val_inject_list_incr; eauto. auto. auto.

- (* external call *)
  apply match_stackframes_global in H5 as GLOB. destruct GLOB.
  exploit external_call_mem_inject'; eauto.
  intros (f' & res' & m2' & A & B & C & D & E & F & G & I).
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor. eapply match_stackframes_incr; eauto.
  apply external_call_sdepth in A. apply external_call_sdepth in H.
  simpl in *. congruence.
  inv H8. erewrite <- external_call_astack; eauto.
  apply external_call_astack in A. rewrite <- A. rewrite <- H4. simpl.
  auto. eauto. eauto.

- (* returnstate *)
  inv H3.
+ (* synchronous return in both programs *)
  exploit Mem.pop_stage_parallel_inject; eauto. inv H5.
  destruct (Mem.astack (Mem.support m'0)). inv H2. congruence.
  intros (m'1 & POP & INJ).
  left. econstructor; split.
  apply exec_return. eauto.
  econstructor; eauto.
  inv H4. simpl in *. rewrite Nat.sub_0_r in H3.
  apply Mem.sdepth_pop_stage in H. apply Mem.sdepth_pop_stage in POP.
  congruence. apply Mem.astack_pop_stage in H. apply Mem.astack_pop_stage in POP.
  destruct H. destruct POP. rewrite H in H5. rewrite H0 in H5. auto.
  apply set_reg_inject; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). lia.
  split. auto.
  econstructor; eauto.
  inv H4. simpl in *. constructor. erewrite Mem.sdepth_pop_stage; eauto.
  apply Mem.astack_pop_stage in H. destruct H. rewrite H in H5.
  simpl in *. auto. eapply Mem.pop_stage_left_inject; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil (Mem.push_stage m1) (prog_main tprog)); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto. eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved. eauto.
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
  4 : eapply Mem.push_stage_inject; eauto.
  constructor.
  split. intros. unfold Mem.flat_inj.
  exploit Genv.find_symbol_not_fresh; eauto. intro. destr.
  eapply Mem.valid_block_alloc in H4; eauto.
  apply n in H4. inv H4.
  split. intros. unfold Mem.flat_inj.
  exploit Genv.find_var_info_not_fresh; eauto. intro. destr.
  eapply Mem.valid_block_alloc in H4; eauto.
  apply n in H4. inv H4.
  intros. unfold Mem.flat_inj in H6. destr_in H6.
  unfold Mem.flat_inj. intro. intros. destr_in H5.
  constructor. simpl. erewrite Mem.sdepth_push_stage; eauto. erewrite Mem.sdepth_alloc; eauto.
  unfold Mem.sdepth. simpl.
  erewrite Genv.init_mem_stack; eauto. simpl. constructor.
  simpl. erewrite Mem.astack_alloc; eauto.
  erewrite Genv.init_mem_astack; eauto. econstructor; constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H7. inv H3. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog)
                     (RTL.semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.
