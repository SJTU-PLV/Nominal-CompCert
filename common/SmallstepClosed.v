Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Require Import Compiler.
Import Values Maps Memory Ctypes AST.

Set Implicit Arguments.

Lemma E0_split : forall x y, E0 = x ** y -> x = E0 /\ y = E0.
Proof.
  unfold E0, Eapp. intros. split.
  destruct x; auto. simpl in H. discriminate.
  destruct y; auto. exfalso. apply (app_cons_not_nil _ _ _ H).
Qed.

Lemma open_bsim_simulation' {index state1 state2 liA1 liB1 liA2 liB2}:
  forall
    {L1 : lts liA1 liB1 state1} {L2 : lts liA2 liB2 state2}
    {match_states: index -> state1 -> state2 -> Prop} {order},
  (forall s2 t s2', Step L2 s2 t s2' ->
   forall i s1, match_states i s1 s2 -> safe L1 s1 ->
   exists i', exists s1',
      (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
   /\ match_states i' s1' s2') ->
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 E0 s1'
  /\ match_states i' s1' s2'.
Proof.
  intros until i. revert i. remember E0 as t. induction H0; simpl; intros.
  exists i, s1. split; eauto. constructor.
  subst t.
  specialize (H _ _ _ H0 _ _ H3 H4) as (i'' & s & ST & MS).
  apply E0_split in H2 as []. subst.
  assert (Star L1 s0 E0 s). {
    destruct ST.
    inv H. apply E0_split in H6 as []. subst. eapply star_trans; eauto.
    econstructor. exact H2.
    econstructor. unfold E0, Eapp. rewrite app_nil_r. reflexivity.
    tauto. tauto.
  } clear ST.
  eapply star_safe in H4; eauto.
  specialize (IHstar ltac:(auto) _ _ MS H4) as (i' & s1' & ST & MS').
  exists i', s1'. split; auto. eapply star_trans; eauto.
Qed.

Lemma open_progress' {index state1 state2 liA1 liB1 liA2 liB2}:
  forall
    {L1 : lts liA1 liB1 state1} {L2 : lts liA2 liB2 state2}
    {match_states: index -> state1 -> state2 -> Prop} {order},
  (forall i s1 s2,
   match_states i s1 s2 -> safe L1 s1 ->
   (exists r, final_state L2 s2 r) \/
   (exists q, at_external L2 s2 q) \/
   (exists t, exists s2', Step L2 s2 t s2')) ->
  (forall s2 t s2', Step L2 s2 t s2' ->
   forall i s1, match_states i s1 s2 -> safe L1 s1 ->
   exists i', exists s1',
      (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
   /\ match_states i' s1' s2') ->
  forall i s1 s2,
  match_states i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros. unfold safe. intros. revert i s1 H1 H2.
  remember E0 as t.
  induction H3; simpl; intros. eauto. subst t.
  apply E0_split in H2 as []. subst.
  exploit H0; eauto. intros (i' & s1' & ST & MS).
  eapply IHstar. auto. exact MS.
  assert (Star L1 s0 E0 s1'). {
    destruct ST.
    inv H2. apply E0_split in H8 as []. subst. eapply star_trans; eauto.
    econstructor. exact H6.
    econstructor. assert (E0 = E0 ** E0) by auto. exact H2. auto.
    tauto.
  } clear ST.
  eapply star_safe; eauto.
Qed.

Module Closed.

(* Definitions. *)

Record semantics := ClosedSemantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> int -> Prop;
  globalenv: genvtype;
  symbolenv: Genv.symtbl
}.

Declare Scope closed_smallstep_scope.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Eventually' L " := (eventually (step L) (at_external L) (final_state L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Open Scope closed_smallstep_scope.


Record fsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    fsim_order_wf: well_founded order;
    fsim_match_initial_states:
      forall s1, initial_state L1 s1 ->
      exists i, exists s2, initial_state L2 s2 /\ match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
    (* fsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id *)
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: index -> state L1 -> state L2 -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.


Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    (* bsim_public_preserved:
      forall id, Genv.public_symbol (symbolenv L2) id = Genv.public_symbol (symbolenv L1) id *)
  }.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Arguments Backward_simulation {L1 L2 index} order match_states props.


(* Closing open semantics. *)

Section CLOSE_SEMANTICS.

Variable liA liB : language_interface.
Variable query : query liB.
Variable reply : int -> reply liB -> Prop.
Variable s : Smallstep.semantics liA liB.
Variable se : Genv.symtbl.

Definition close_semantics :=
  let lts := Smallstep.activate s se in
  {|
    state := Smallstep.state s;
    genvtype := Smallstep.genvtype lts;
    step := Smallstep.step lts;
    initial_state := Smallstep.initial_state lts query;
    final_state := fun state retval => exists r, reply retval r /\ Smallstep.final_state lts state r;
    globalenv := Smallstep.globalenv lts;
    symbolenv := se;
  |}.

End CLOSE_SEMANTICS.

Section CLOSE_SOUND.

Variable liA1 liB1 : language_interface.
Variable query1 : query liB1.
Variable reply1 : int -> reply liB1 -> Prop.
Variable s1 : Smallstep.semantics liA1 liB1.
Variable se1 : Genv.symtbl.
Definition lts1 := (Smallstep.activate s1 se1).
Definition L1 := close_semantics query1 reply1 s1 se1.
(* Hypothesis closed1 : forall s q, Smallstep.safe lts1 s -> ~ at_external lts1 s q. *)
(* Hypothesis reply_sound1: forall r, exists i, reply1 i r. *)

Variable liA2 liB2 : language_interface.
Variable query2 : query liB2.
Variable reply2 : int -> reply liB2 -> Prop.
Variable s2 : Smallstep.semantics liA2 liB2.
Variable se2 : Genv.symtbl.
Definition lts2 := (Smallstep.activate s2 se2).
Definition L2 := close_semantics query2 reply2 s2 se2.
Hypothesis closed2 : forall s q, Smallstep.safe lts2 s -> ~ at_external lts2 s q.
Hypothesis reply_sound2: forall s r, Smallstep.final_state lts2 s r -> exists i, reply2 i r.

Variable ccA : callconv liA1 liA2.
Variable ccB : callconv liB1 liB2.

Hypothesis Hvalid : Genv.valid_for (skel s1) se1.

Variable wB : ccworld ccB.

Hypothesis Hmatch_query : match_query ccB wB query1 query2.
Hypothesis Hmatch_reply : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply1 r r1 <-> reply2 r r2.

Hypothesis Hmatch_senv : match_senv ccB wB se1 se2.

Lemma close_sound_forward :
  Smallstep.forward_simulation ccA ccB s1 s2 -> forward_simulation L1 L2.
Proof.
  (* pose proof (Hmatch_query := Hmatch_query).
  pose proof (Hmatch_reply := Hmatch_reply).
  pose proof (open_simulation := open_simulation).
  pose proof (Hvalid := Hvalid). *)
  intro open_simulation.
  unfold Smallstep.forward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (fsim_lts se1 se2 wB Hmatch_senv Hvalid). inv fsim_lts.
  unfold L1, L2, close_semantics.
  do 2 econstructor; simpl; eauto.

  (* match final state *)
  intros i s1' s2' r MS (r1 & R1 & FINAL).
  exploit fsim_match_final_states0; eauto. intros (r2 & FINAL' & MATCH_REPLY).
  eexists. split; eauto. eapply Hmatch_reply; eauto.
Qed.

Lemma safe_sound_1:
  forall s, safe L1 s -> Smallstep.safe lts1 s.
Proof.
  unfold safe, Smallstep.safe, L1, lts1, close_semantics. simpl. intros.
  specialize (H _ H0) as [(r & r0 & REPLY & FS)|(t & s'' & STEP)]; eauto.
Qed.

Lemma close_sound_backward:
  Smallstep.backward_simulation ccA ccB s1 s2 -> backward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.backward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (bsim_lts se1 se2 wB Hmatch_senv Hvalid).
  inv bsim_lts.
  unfold L1, L2, close_semantics.
  specialize (bsim_match_initial_states0 _ _ Hmatch_query).
  inv bsim_match_initial_states0.
  do 2 econstructor; simpl; simpl; eauto.

  intros. specialize (bsim_match_cont_match _ _ H H0) as (s1' & IS & []).
  exists x, s1'. eauto.

  intros. apply safe_sound_1 in H0. destruct H1 as (r0 & REPLY & FS).
  specialize (bsim_match_final_states0 _ _ _ _ H H0 FS) as (s1' & r1 & STAR & FS' & MS).
  exists s1'. split; eauto. eexists. split; eauto. eapply Hmatch_reply; eauto.

  intros. apply safe_sound_1 in H0.
  pose proof (progress := bsim_progress0).
  specialize (bsim_progress0 _ _ _ H H0) as [(r & FS)|[|]].
  left. destruct (reply_sound2 _ _ FS) as (ri & REPLY). eauto.
  destruct H1. exfalso. eapply closed2; eauto. eapply open_progress'; eauto.
  auto.

  intros. apply safe_sound_1 in H1.
  eapply bsim_simulation0; eauto.
Qed.

End CLOSE_SOUND.

Section CLOSE_COMPCERT.

Variable p : Csyntax.program.
Variable tp : Asm.program.
Hypothesis transf : transf_c_program p = OK tp.
Let se := Genv.symboltbl (erase_program p).

Variable main_block_c : block.
Variable m0_c : mem.

Let liA1 := li_c.
Let liB1 := li_c.
Let sg := AST.mksignature nil (AST.Tret AST.Tint) AST.cc_default.
Let main_function_value_c := Vptr main_block_c Ptrofs.zero.
Let query1 := cq main_function_value_c sg nil m0_c.
Inductive reply1 : int -> c_reply -> Prop :=
  | reply1_intro: forall r m,
      reply1 r (cr (Vint r) m).
Let s1 := Csem.semantics p.
Let se1 := se.
Let lts1' := (Smallstep.activate s1 se1).

Let ge_c' := Smallstep.globalenv (s1 se).
Let ge_c := Csem.genv_genv ge_c'.
Variable main_c : Csyntax.fundef.
Hypothesis Hinitial_state_c :
  Genv.init_mem (erase_program p) = Some m0_c /\
  Genv.find_symbol se p.(prog_main) = Some main_block_c /\
  Genv.find_funct_ptr ge_c main_block_c = Some main_c.

Import Asm.

Let s2 := Asm.semantics tp.
Let ge_asm := Smallstep.globalenv (s2 se).
Variable m0_asm : mem.
Hypothesis Hinitial_state_asm :
  Genv.init_mem (erase_program tp) = Some m0_asm.

Let liA2 := li_asm.
Let liB2 := li_asm.
Let rs0 :=
    (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge_asm tp.(prog_main) Ptrofs.zero)
    # RA <- Vnullptr
    # RSP <- Vnullptr.
Let query2 := (rs0, m0_asm).
Inductive reply2: int -> (regset * mem) -> Prop :=
  | reply2_intro: forall r rs m,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      reply2 r (rs, m).
Let se2 := se.
Let lts2' := (Smallstep.activate s2 se2).

Ltac clean_destr :=
  match goal with
  | H: _ = left _ |- _ => clear H
  | H: _ = right _ |- _ => clear H
  end.

Ltac destr :=
  match goal with
    |- context [match ?a with _ => _ end] => destruct a eqn:?; try intuition congruence
  end; repeat clean_destr.

Ltac destr_in H :=
  match type of H with
    context [match ?a with _ => _ end] => destruct a eqn:?; try intuition congruence
  | _ => inv H
  end; repeat clean_destr.

Lemma erase_same: erase_program p = erase_program tp.
Proof.
  exploit transf_c_program_match; eauto. intro MATCH.
  unfold match_c_prog in MATCH. simpl in MATCH. repeat destruct MATCH as (? & MATCH).
  fold Csyntax.fundef. remember p as xx.
  rename xx into p', p into xx. rename p' into p.
  match goal with
  | H: ?P p ?p2 |- _ => rewrite Heqxx in H
  end.
  rewrite Heqxx. clear Heqxx.
  Ltac mp H p1 p2 :=
    unfold Linking.match_program in H;
    match type of H with
    | Linking.match_program_gen _ _ _ _ _ =>
        apply Linking.match_program_skel in H;
        try fold CminorSel.fundef in H;
        try fold RTL.fundef in H;
        rewrite H; clear H p1;
        rename p2 into p1
    | Linking.match_program_gen _ _ _ _ _ /\ _ =>
        let H' := fresh "H" in
        let garbage := fresh "H" in
        destruct H as (H' & garbage);
        clear garbage;
        mp H' p1 p2
    end.
  Ltac try_rewrite xx := match goal with
  | H: ?P xx ?p2 |- _ =>
    unfold P in H; mp H xx p2
  | H: match_if ?cond ?P xx ?p2 |- _ =>
    unfold match_if, P in H;
    let H' := fresh "H" in
    assert (H' : erase_program xx = erase_program p2) by (destr_in H; mp H xx p2; auto);
    rewrite H';
    clear H' H xx;
    rename p2 into xx
  end.
  repeat try_rewrite xx.
  unfold Unusedglobproof.match_prog in H12.
  destruct H12 as (u & VALID & MATCH').
  inv MATCH'. rewrite <- match_prog_skel.
  clear match_prog_main match_prog_public match_prog_def match_prog_skel VALID xx u.
  rename x12 into xx.
  repeat try_rewrite xx.
  auto.
Qed.

Lemma m0_same: m0_c = m0_asm.
Proof.
  rewrite erase_same, Hinitial_state_asm in Hinitial_state_c.
  destruct Hinitial_state_c. inv H. auto.
Qed.

Let ccA : callconv liA1 liA2 := cc_compcert.
Let ccB : callconv liB1 liB2 := cc_compcert.

Lemma Hvalid: Genv.valid_for (erase_program p) se1.
Proof.
  red. intros. rewrite Genv.find_info_symbol in H. destruct H as (b & []).
  exists b, g. unfold se1, se. split; auto. split; auto.
  destruct g; constructor. constructor.
  destruct v. constructor; constructor.
Qed.

Lemma m0_inject: Mem.inject (Mem.flat_inj (Mem.support m0_c)) m0_c m0_asm.
Proof.
  rewrite <- m0_same.
  apply (Genv.initmem_inject (erase_program p)).
  destruct Hinitial_state_c. auto.
Qed.

Let wB : ccworld ccB.
  unfold ccB, cc_compcert, CA.cc_c_asm_injp. simpl.
  (* ro *)
  split. split. exact se. split. exact se. exact m0_asm.
  (* wt_c *)
  split. split. exact se. split. exact se. exact sg.
  (* cc_c_asm_injp *)
  split. split. exact se. split.
  simpl. econstructor. exact m0_inject. exact sg. exact rs0.
  (* cc_asm injp *)
  econstructor. exact m0_inject.
Defined.

Hypothesis closed:
  forall v id sg, Genv.find_funct (Genv.globalenv se tp) v <> Some (External (EF_external id sg)).

Lemma closed2 : forall s q, Smallstep.safe lts2' s -> ~ Smallstep.at_external lts2' s q.
Proof.
  unfold lts2', s2, se2, semantics. simpl. intros. intro.
  destruct s. inv H0.
  eapply closed; eauto.
Qed.

Lemma reply_sound2: forall s r, Smallstep.final_state lts2' s r -> exists i, reply2 i r.
Proof.
  unfold lts2', s2, se2. simpl. intros. destruct s.
  inversion H.
  give_up.
Admitted.

Lemma romem_for_symtbl_sound:
  ValueAnalysis.romem_for_symtbl se = ValueAnalysis.romem_for p.
Proof.
  unfold ValueAnalysis.romem_for, ValueAnalysis.romem_for_symtbl. unfold se.
  unfold Genv.symboltbl.
  destruct Hinitial_state_c as (INIT & SYM & FPTR).
Abort.

Lemma sound_memory_ro: ValueAnalysis.sound_memory_ro se m0_c.
Proof.
  unfold se. destruct Hinitial_state_c. clear H0.
  constructor.
  apply ValueAnalysis.initial_mem_matches' in H as (? & ? & ? & ROM & ?).
  2:intros; inv H0; auto.
  specialize (ROM p ltac:(apply Linking.linkorder_refl)).
  admit.
  erewrite Genv.init_mem_genv_sup; eauto.
Admitted.

Lemma main_block_genv: Genv.find_symbol se (prog_main tp) = Some main_block_c.
Proof.
  destruct Hinitial_state_c as [? []].
  pose proof erase_same. inv H2. simpl in H0. rewrite H0. auto.
Qed.

Lemma has_main_block: sup_In main_block_c (Mem.support m0_c).
Proof.
  destruct Hinitial_state_c as [? []].
  eapply Genv.find_symbol_not_fresh; eauto.
Qed.

Lemma Hmatch_query : match_query ccB wB query1 query2.
Proof.
  simpl.
  exists query1. split.
  constructor. rewrite <- m0_same. constructor. exact sound_memory_ro.
  exists query1. split.
  constructor. split. reflexivity. simpl. auto.
  exists query2. split.
  unfold query1, query2. econstructor; simpl.
  unfold Conventions1.loc_arguments. cbn.
  destruct Archi.ptr64, Archi.win64; simpl; constructor.
  unfold rs0. simpl.
  unfold main_function_value_c, Genv.symbol_address.
  rewrite main_block_genv.
  econstructor. unfold Mem.flat_inj. pose proof has_main_block. destr.
  rewrite Ptrofs.add_zero. auto.
  intros. inv H.
  cbn. unfold Vnullptr, Tptr. destruct Archi.ptr64; simpl; auto.
  cbn. unfold Vnullptr, Tptr. destruct Archi.ptr64; simpl; auto.
  give_up. (* rs0 RSP = Vnullptr *)
  econstructor.
  unfold Conventions.tailcall_possible, Conventions.size_arguments, Conventions1.loc_arguments. simpl.
  destruct Archi.ptr64, Archi.win64; simpl; auto.
  unfold main_function_value_c. discriminate.
  discriminate.
  unfold cc_asm_match'. simpl. split; [|split].
  intros. unfold rs0.
  destruct (PregEq.eq r RSP); [subst; rewrite Pregmap.gss|
  rewrite Pregmap.gso; auto; destruct (PregEq.eq r RA); [subst; rewrite Pregmap.gss|
  rewrite Pregmap.gso; auto; destruct (PregEq.eq r PC); [subst; rewrite Pregmap.gss|
  rewrite Pregmap.gso; auto]]].
  unfold Vnullptr. destr; constructor.
  unfold Vnullptr. destr; constructor.
  unfold Genv.symbol_address. destr; econstructor.
  unfold ge_asm in Heqo. simpl in Heqo. rewrite main_block_genv in Heqo. inv Heqo.
  unfold Mem.flat_inj. pose proof has_main_block. destr.
  rewrite Ptrofs.add_zero. auto.
  unfold rs0.
  rewrite Pregmap.gso; [|discriminate].
  rewrite Pregmap.gso; [|discriminate].
  rewrite Pregmap.gss.
  unfold ge_asm. simpl. unfold Genv.symbol_address. rewrite main_block_genv. discriminate.
  rewrite <- m0_same at 2. constructor.
Admitted.

Lemma Hmatch_reply : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply1 r r1 <-> reply2 r r2.
Proof.
  simpl. intros.
  destruct H, H, H0, H0, H1, H1.
  split; intro r'; inv r'.

  inv H. inv H0. inv H1. inv H2. destruct r2.
  inv H0. simpl in H2. inv H2.
  unfold rs0 in H16.
  rewrite Pregmap.gso in H16; [|discriminate]. rewrite Pregmap.gss in H16.
  assert (r0 PC = Vnullptr). {
    pose proof (INJ := H0 PC). rewrite H16 in INJ.
    unfold Vnullptr. unfold Vnullptr in INJ.
    destruct Archi.ptr64; inv INJ; auto.
  }
  constructor; auto.
  unfold Conventions1.loc_result, Conventions1.loc_result_64, Conventions1.loc_result_32 in tres.
  subst tres.
  destr_in H10; simpl in H10; inv H10;
  specialize (H0 RAX); rewrite <- H7 in H0; inv H0; auto.

  inv H2. inv H5. destruct x1. simpl in H6. inv H6.
  specialize (H5 RAX). rewrite H4 in H5. inv H5.
  inv H1. destruct r1.
  inv H. destruct H1. inv H0. unfold sg, proj_sig_res in H5. simpl in H5.
  assert (res = Vint r). {
    unfold Conventions1.loc_result, Conventions1.loc_result_64, Conventions1.loc_result_32 in tres.
    subst tres. destr_in H15; simpl in H15.
    rewrite <- H8 in H15. inv H15. auto.
    give_up. (* Vundef *)
    rewrite <- H8 in H15. inv H15. auto.
    give_up.
  }
  subst res. constructor.
  inv H1. destruct r1.
  inv H. inv H0.
  unfold Conventions1.loc_result, Conventions1.loc_result_64, Conventions1.loc_result_32 in tres.
  subst tres. destr_in H15; simpl in H15; rewrite <- H8 in H15; inv H15.
  give_up.
  give_up.
Admitted.

Lemma Hmatch_senv : match_senv ccB wB se1 se2.
Proof.
  unfold ccB, cc_compcert, se1, se2. simpl.
  split; [|split; [|split]].

  constructor. auto.
  constructor. auto.

  destruct Hinitial_state_c as (INIT & ? & ?).
  unfold se. unfold Mem.flat_inj.
  constructor.
  split; try erewrite Genv.init_mem_genv_sup by eauto; auto; intros.
  exists b1. destr.
  exists b2. destr.
  1,2,3:destr_in H1.
  1,2:erewrite Genv.init_mem_genv_sup by eauto. 2:rewrite m0_same.
  1,2:apply Mem.sup_include_refl.

  destruct Hinitial_state_c as (INIT & ? & ?).
  unfold se. unfold Mem.flat_inj.
  constructor.
  split; try erewrite Genv.init_mem_genv_sup by eauto; auto; intros.
  exists b1. destr.
  exists b2. destr.
  1,2,3:destr_in H1.
  1,2:erewrite Genv.init_mem_genv_sup by eauto. 2:rewrite m0_same.
  1,2:apply Mem.sup_include_refl.
Qed.

Lemma open_simulation: Smallstep.backward_simulation ccA ccB s1 s2.
Proof.
  apply c_semantic_preservation, transf_c_program_match. auto.
Qed.

Lemma compcert_close_sound :
  backward_simulation (L1 query1 reply1 s1 se1) (L2 query2 reply2 s2 se2).
Proof.
  eapply close_sound_backward; eauto using
    closed2, reply_sound2, Hvalid, Hmatch_query, Hmatch_reply, Hmatch_senv, open_simulation.
Qed.

End CLOSE_COMPCERT.

End Closed.
