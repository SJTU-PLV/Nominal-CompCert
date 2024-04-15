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

(** Elimination of unreferenced static definitions *)

Require Import FSets Coqlib Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import Integers Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL RTLmach.
Require Import Unusedglob.

Module ISF := FSetFacts.Facts(IS).
Module ISP := FSetProperties.Properties(IS).

(** * Relational specification of the transformation *)

(** The transformed program is obtained from the original program
  by keeping only the global definitions that belong to a given
  set [u] of names.  *)


Record match_prog_1 (u: IS.t) (p tp: program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_def:
    forall id,
      (prog_defmap tp)!id = if IS.mem id u then (prog_defmap p)!id else
                              option_map remove_gfun (prog_defmap p)!id;
  match_prog_skel:
    erase_program tp = erase_program p
}.

(** This set [u] (as "used") must be closed under references, and
  contain the entry point and the public identifiers of the program. *)

Definition ref_function (f: function) (id: ident) : Prop :=
  exists pc i, f.(fn_code)!pc = Some i /\ In id (ref_instruction i).

Definition ref_fundef (fd: fundef) (id: ident) : Prop :=
  match fd with Internal f => ref_function f id | External ef => False end.

Definition ref_init (il: list init_data) (id: ident) : Prop :=
  exists ofs, In (Init_addrof id ofs) il.

Definition ref_def (gd: globdef fundef unit) (id: ident) : Prop :=
  match gd with
  | Gfun fd => ref_fundef fd id
  | Gvar gv => ref_init gv.(gvar_init) id
  end.

Record valid_used_set (p: program) (u: IS.t) : Prop := {
  used_closed: forall id gd id',
    IS.In id u -> (prog_defmap p)!id = Some gd -> ref_def gd id' ->
    IS.In id' u;
  used_main:
    IS.In p.(prog_main) u;
  used_public: forall id,
    In id p.(prog_public) -> IS.In id u;
  used_defined: forall id,
    IS.In id u -> In id (prog_defs_names p) \/ id = p.(prog_main)
}.

Definition match_prog (p tp: program) : Prop :=
  exists u: IS.t, valid_used_set p u /\ match_prog_1 u p tp.

(** * Properties of the static analysis *)

(** Monotonic evolution of the workset. *)

Inductive workset_incl (w1 w2: workset) : Prop :=
  workset_incl_intro:
    forall (SEEN: IS.Subset w1.(w_seen) w2.(w_seen))
           (TODO: List.incl w1.(w_todo) w2.(w_todo))
           (TRACK: forall id, IS.In id w2.(w_seen) ->
                      IS.In id w1.(w_seen) \/ List.In id w2.(w_todo)),
    workset_incl w1 w2.

Lemma seen_workset_incl:
  forall w1 w2 id, workset_incl w1 w2 -> IS.In id w1 -> IS.In id w2.
Proof.
  intros. destruct H. auto.
Qed.

Lemma workset_incl_refl: forall w, workset_incl w w.
Proof.
  intros; split. red; auto. red; auto. auto.
Qed.

Lemma workset_incl_trans:
  forall w1 w2 w3, workset_incl w1 w2 -> workset_incl w2 w3 -> workset_incl w1 w3.
Proof.
  intros. destruct H, H0; split.
  red; eauto.
  red; eauto.
  intros. edestruct TRACK0; eauto. edestruct TRACK; eauto.
Qed.

Lemma add_workset_incl:
  forall id w, workset_incl w (add_workset id w).
Proof.
  unfold add_workset; intros. destruct (IS.mem id w) eqn:MEM.
- apply workset_incl_refl.
- split; simpl.
  + red; intros. apply IS.add_2; auto.
  + red; simpl; auto.
  + intros. destruct (ident_eq id id0); auto. apply IS.add_3 in H; auto.
Qed.

Lemma addlist_workset_incl:
  forall l w, workset_incl w (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. eauto.
Qed.

Lemma add_ref_function_incl:
  forall f w, workset_incl w (add_ref_function f w).
Proof.
  unfold add_ref_function; intros. apply PTree_Properties.fold_rec.
- auto.
- apply workset_incl_refl.
- intros. apply workset_incl_trans with a; auto.
  unfold add_ref_instruction. apply addlist_workset_incl.
Qed.

Lemma add_ref_globvar_incl:
  forall gv w, workset_incl w (add_ref_globvar gv w).
Proof.
  unfold add_ref_globvar; intros.
  revert w. induction (gvar_init gv); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans; [ | eauto ].
  unfold add_ref_init_data.
  destruct a; (apply workset_incl_refl || apply add_workset_incl).
Qed.

Lemma add_ref_definition_incl:
  forall pm id w, workset_incl w (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros.
  destruct (pm!id) as [[[] | ? ] | ].
  apply add_ref_function_incl.
  apply workset_incl_refl.
  apply add_ref_globvar_incl.
  apply workset_incl_refl.
Qed.

Lemma initial_workset_incl:
  forall p, workset_incl {| w_seen := IS.empty; w_todo := nil |} (initial_workset p).
Proof.
  unfold initial_workset; intros.
  eapply workset_incl_trans. 2: apply add_workset_incl.
  generalize {| w_seen := IS.empty; w_todo := nil |}. induction (prog_public p); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. apply IHl.
Qed.

(** Soundness properties for functions that add identifiers to the workset *)

Lemma seen_add_workset:
  forall id (w: workset), IS.In id (add_workset id w).
Proof.
  unfold add_workset; intros.
  destruct (IS.mem id w) eqn:MEM.
  apply IS.mem_2; auto.
  simpl. apply IS.add_1; auto.
Qed.

Lemma seen_addlist_workset:
  forall id l (w: workset),
  In id l -> IS.In id (addlist_workset l w).
Proof.
  induction l; simpl; intros.
  tauto.
  destruct H. subst a.
  eapply seen_workset_incl. apply addlist_workset_incl. apply seen_add_workset.
  apply IHl; auto.
Qed.

Lemma seen_add_ref_function:
  forall id f w,
  ref_function f id -> IS.In id (add_ref_function f w).
Proof.
  intros until w. unfold ref_function, add_ref_function. apply PTree_Properties.fold_rec; intros.
- destruct H1 as (pc & i & A & B). apply H0; auto. exists pc, i; split; auto. rewrite H; auto.
- destruct H as (pc & i & A & B). rewrite PTree.gempty in A; discriminate.
- destruct H2 as (pc & i & A & B). rewrite PTree.gsspec in A. destruct (peq pc k).
  + inv A. unfold add_ref_instruction. apply seen_addlist_workset; auto.
  + unfold add_ref_instruction. eapply seen_workset_incl. apply addlist_workset_incl.
    apply H1. exists pc, i; auto.
Qed.

Lemma seen_add_ref_definition:
  forall pm id gd id' w,
  pm!id = Some gd -> ref_def gd id' -> IS.In id' (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros. rewrite H. red in H0; destruct gd as [[f|ef]|gv].
  apply seen_add_ref_function; auto.
  contradiction.
  destruct H0 as (ofs & IN).
  unfold add_ref_globvar.
  assert (forall l (w: workset),
          IS.In id' w \/ In (Init_addrof id' ofs) l ->
          IS.In id' (fold_left add_ref_init_data l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto.
    left. destruct a; simpl; auto. eapply seen_workset_incl. apply add_workset_incl. auto.
    subst; left; simpl. apply seen_add_workset.
  }
  apply H0; auto.
Qed.

Lemma seen_main_initial_workset:
  forall p, IS.In p.(prog_main) (initial_workset p).
Proof.
  intros. apply seen_add_workset.
Qed.

Lemma seen_public_initial_workset:
  forall p id, In id p.(prog_public) -> IS.In id (initial_workset p).
Proof.
  intros. unfold initial_workset. eapply seen_workset_incl. apply add_workset_incl.
  assert (forall l (w: workset),
          IS.In id w \/ In id l -> IS.In id (fold_left (fun w id => add_workset id w) l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto; left.
    eapply seen_workset_incl. apply add_workset_incl. auto.
    subst a. apply seen_add_workset.
  }
  apply H0. auto.
Qed.

(** * Correctness of the transformation with respect to the relational specification *)

(** Correctness of the dependency graph traversal. *)

Section ANALYSIS.

Variable p: program.
Let pm := prog_defmap p.

Definition workset_invariant (w: workset) : Prop :=
  forall id gd id',
  IS.In id w -> ~List.In id (w_todo w) -> pm!id = Some gd -> ref_def gd id' ->
  IS.In id' w.

Definition used_set_closed (u: IS.t) : Prop :=
  forall id gd id',
  IS.In id u -> pm!id = Some gd -> ref_def gd id' -> IS.In id' u.

Lemma iter_step_invariant:
  forall w,
  workset_invariant w ->
  match iter_step pm w with
  | inl u => used_set_closed u
  | inr w' => workset_invariant w'
  end.
Proof.
  unfold iter_step, workset_invariant, used_set_closed; intros.
  destruct (w_todo w) as [ | id rem ]; intros.
- eapply H; eauto.
- set (w' := {| w_seen := w.(w_seen); w_todo := rem |}) in *.
  destruct (add_ref_definition_incl pm id w').
  destruct (ident_eq id id0).
  + subst id0. eapply seen_add_ref_definition; eauto.
  + exploit TRACK; eauto. intros [A|A].
    * apply SEEN. eapply H; eauto. simpl.
      assert (~ In id0 rem).
      { change rem with (w_todo w'). red; intros. elim H1; auto. }
      tauto.
    * contradiction.
Qed.

Theorem used_globals_sound:
  forall u, used_globals p pm = Some u -> used_set_closed u.
Proof.
  unfold used_globals; intros. eapply PrimIter.iterate_prop with (P := workset_invariant); eauto.
- intros. apply iter_step_invariant; auto.
- destruct (initial_workset_incl p).
  red; intros. edestruct TRACK; eauto.
  simpl in H4. eelim IS.empty_1; eauto.
  contradiction.
Qed.

Theorem used_globals_incl:
  forall u, used_globals p pm = Some u -> IS.Subset (initial_workset p) u.
Proof.
  unfold used_globals; intros.
  eapply PrimIter.iterate_prop with (P := fun (w: workset) => IS.Subset (initial_workset p) w); eauto.
- fold pm; unfold iter_step; intros. destruct (w_todo a) as [ | id rem ].
  auto.
  destruct (add_ref_definition_incl pm id {| w_seen := a; w_todo := rem |}).
  red; auto.
- red; auto.
Qed.

Corollary used_globals_valid:
  forall u,
  used_globals p pm = Some u ->
  IS.for_all (global_defined p pm) u = true ->
  valid_used_set p u.
Proof.
  intros. constructor.
- intros. eapply used_globals_sound; eauto.
- eapply used_globals_incl; eauto. apply seen_main_initial_workset.
- intros. eapply used_globals_incl; eauto. apply seen_public_initial_workset; auto.
- intros. apply ISF.for_all_iff in H0.
+ red in H0. apply H0 in H1. unfold global_defined in H1.
  destruct pm!id as [g|] eqn:E.
* left. change id with (fst (id,g)). apply in_map. apply in_prog_defmap; auto.
* InvBooleans; auto.
+ hnf. simpl; intros; congruence.
Qed.

End ANALYSIS.

(** Properties of the elimination of unused global definitions. *)

Section TRANSFORMATION.

Variable p: program.
Variable used: IS.t.

Let add_def (m: prog_map) idg := PTree.set (fst idg) (snd idg) m.

Lemma filter_globdefs_map_1:
  forall id l u m1 m2,
  IS.mem id u = false ->
  m1! id = option_map remove_gfun m2!id ->
  (fold_left add_def (filter_globdefs u l) m1)!id = 
  option_map remove_gfun (fold_left add_def l m2)!id.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- destruct (IS.mem id1 u) eqn:MEM.
   + apply IHl; auto.
    unfold add_def at 1 2. simpl.
    rewrite ! PTree.gsspec. destruct (peq id id1).
    congruence. auto.
   + apply IHl; auto. unfold add_def. simpl.
     rewrite ! PTree.gsspec. destruct (peq id id1). auto. auto.
Qed.

Lemma filter_globdefs_map_2:
  forall id l u m1 m2,
  IS.mem id u = true ->
  m1!id = m2!id ->
  (fold_left add_def (filter_globdefs u l) m1)!id = (fold_left add_def l m2)!id.
Proof.
  induction l as [ | [id1 gd1] l]; simpl; intros.
- auto.
- simpl. 
  destruct (IS.mem id1 u) eqn:MEM.
  + apply IHl; auto.
    unfold filter_globdefs. 
    unfold add_def at 1 2. simpl.
    rewrite ! PTree.gsspec. destruct (peq id id1). auto. auto.
  + apply IHl; auto. unfold add_def. simpl.
     destruct (peq id id1). congruence. 
    rewrite !PTree.gso by congruence. auto.
Qed.

Lemma filter_globdefs_map:
  forall id u defs,
  (PTree_Properties.of_list (filter_globdefs u defs))! id =
  if IS.mem id u then (PTree_Properties.of_list defs)!id 
                 else option_map remove_gfun (PTree_Properties.of_list defs)!id.
Proof.
  intros. unfold PTree_Properties.of_list. fold prog_map. unfold PTree.elt. fold add_def.
  destruct (IS.mem id u) eqn:MEM.
  - apply filter_globdefs_map_2; eauto.
  - apply filter_globdefs_map_1; eauto.
Qed.

End TRANSFORMATION.

Theorem transf_program_match:
  forall p tp, transform_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp TR.
  exploit transform_skel; eauto. intro SKEL.
  unfold transform_program in TR. set (pm := prog_defmap p) in *.
  destruct (used_globals p pm) as [u|] eqn:U; try discriminate.
  destruct (IS.for_all (global_defined p pm) u) eqn:DEF; inv TR.
  exists u; split.
  apply used_globals_valid; auto.
  constructor; simpl; auto.
  intros. unfold prog_defmap; simpl.
  eapply filter_globdefs_map; eauto.
Qed.

(** * Semantic preservation *)
Section ORACLE.
Variable fn_stack_requirements : ident -> Z.

Require Import LanguageInterface Inject.

(** The initial memory injection inferred from global symbol tables *)
Definition init_meminj (se tse: Genv.symtbl) : meminj :=
  fun b =>
    match Genv.invert_symbol se b with
    | Some id =>
        match Genv.find_symbol tse id with
        | Some b' => Some (b', 0)
        | None => None
        end
    | None => None
    end.


Section SOUNDNESS.

Variable p: program.
Variable tp: program.
Variable used: IS.t.
Hypothesis USED_VALID: valid_used_set p used.
Hypothesis TRANSF: match_prog_1 used p tp.

Variable w: inj_world.
Variable se tse: Genv.symtbl.

Definition skel := erase_program p.
Definition tskel := erase_program tp.

Hypothesis GE: inj_stbls w se tse.
Hypothesis VALID: Genv.valid_for skel se.

Lemma main_symb_pres: forall b,
    Genv.find_symbol se (prog_main skel) = Some b -> 
    exists b', Genv.find_symbol tse (prog_main tskel) = Some b'.
Proof.
  intros. inv GE. inv inj_stbls_match.
  exploit mge_dom; eauto. eapply Genv.genv_symb_range; eauto.
  intros [b2 INJ]. exists b2.
  inv TRANSF. cbn. rewrite match_prog_main0. cbn in H.
  eapply mge_symb; eauto.
Qed.

Lemma symb_incl: forall id b,
    Genv.find_symbol tse id = Some b -> exists b', Genv.find_symbol se id = Some b'.
Proof.
  intros. inv GE.
  exploit Genv.mge_img; eauto. eapply Genv.genv_symb_range; eauto.
  intros [a B]. exists a. eapply Genv.mge_symb; eauto.
Qed.

Lemma info_eq: forall b b' id,
    Genv.find_symbol se id = Some b ->
    Genv.find_symbol tse id = Some b' ->
    Genv.find_info se b = Genv.find_info tse b'.
Proof.
  intros. inv GE.
  exploit Genv.mge_img; eauto. eapply Genv.genv_symb_range; eauto.
  intros (a & INJ).
  exploit Genv.mge_symb; eauto. intro EQ.
  apply EQ in H0 as H2. setoid_rewrite H in H2. inv H2.
  eapply Genv.mge_info; eauto.
Qed.

(** Hypothesis about injections in the world *)

Axiom inj_preserved : forall id b,
        Genv.find_symbol tse id = Some b ->
        IS.mem id used = true.

Lemma map_fst_in {A B:Type}: forall (a:A) (b:B) list,
    In (a,b) list -> In a (map fst list).
Proof.
  intros. induction list.
  - inv H.
  - inv H.
    left. auto.
    right. eauto.
Qed.

Lemma remove_unused_consistent: forall id gd b,
    (prog_defmap skel) ! id = Some gd -> 
    Genv.find_symbol tse id = Some b -> 
    (prog_defmap tskel) ! id = Some gd.
Proof.
  intros. simpl.
  unfold tskel in *. unfold skel in *.
  rewrite erase_program_defmap in *.
  unfold option_map in *.
  erewrite match_prog_def; eauto.
  erewrite inj_preserved; eauto.
Qed.


Lemma remove_unused_consistent_p :forall id gd b,
    (prog_defmap p) ! id = Some gd -> 
    Genv.find_symbol tse id = Some b -> 
    (prog_defmap tp) ! id = Some gd.
Proof.
  intros.
  generalize (erase_program_defmap p id).
  rewrite H. cbn [option_map].
  intros DEF.
  generalize (remove_unused_consistent _ _ _ DEF H0).
  intros TDEF.
  unfold tskel in TDEF.
  rewrite erase_program_defmap in TDEF.
  unfold option_map in TDEF.
  destruct ((prog_defmap tp) ! id) eqn:TDEF'; try discriminate.
  inv TDEF.
  inv TRANSF. 
  rewrite (match_prog_def0 id) in TDEF'.
  destruct (IS.mem id used) eqn:MEM; try discriminate.
  rewrite H in TDEF'. inv TDEF'.
  reflexivity.
  erewrite inj_preserved in MEM; eauto. congruence.
Qed.

(** Public symbols of source and target symbol tables are the same *)
Lemma se_public_same: forall id, 
    Genv.public_symbol se id = Genv.public_symbol tse id.
Proof.
  intros. symmetry. inv GE. inv inj_stbls_match. eauto.
Qed.

Let ge := Genv.globalenv se p.
Let tge := Genv.globalenv tse tp.
Let pm := prog_defmap p.

Definition kept (id: ident) : Prop := IS.In id used.

Lemma kept_closed:
  forall id gd id',
  kept id -> pm!id = Some gd -> ref_def gd id' -> kept id'.
Proof.
  intros. eapply used_closed; eauto.
Qed.

Lemma kept_main:
  kept p.(prog_main).
Proof.
  eapply used_main; eauto.
Qed.

Lemma kept_public:
  forall id, In id p.(prog_public) -> kept id.
Proof.
  intros. eapply used_public; eauto.
Qed.

(** Relating [Genv.find_symbol] operations in the original and transformed program *)

Lemma transform_find_symbol_1:
  forall id b,
  Genv.find_symbol ge id = Some b -> kept id -> exists b', Genv.find_symbol tge id = Some b'.
Proof.
  intros.
  inv USED_VALID.
  generalize (used_defined0 _ H0).
  destruct 1 as [IN | EQ].
  - exploit prog_defmap_dom; eauto.
    intros (gd & DEF).
    inv TRANSF.
    generalize (match_prog_def0 id).
    red in H0. apply IS.mem_1 in H0. rewrite H0.
    rewrite DEF.
    assert (match_senv (cc_c inj) w se tse).
    inv GE. constructor; eauto.
    eapply match_senv_valid_for in H1; eauto.
    unfold skel in H1.
    rewrite match_prog_def0.
    rewrite H0.
    rewrite (Genv.find_def_symbol id gd H1).
    intros (b' & SYM & DEF').
    eauto.
  - subst.
    erewrite <- match_prog_main; eauto.
    eapply main_symb_pres; eauto.
Qed.

Lemma symbols_inject_init_public: forall id b,
    Genv.public_symbol se id = true -> 
    Genv.find_symbol se id = Some b ->
    exists b', Genv.find_symbol tse id = Some b' /\ 
          init_meminj se tse b = Some(b', 0).
Proof.
  cbn.
  intros id b PUB FND.
  generalize PUB; intros PUB1.
  rewrite se_public_same in PUB1.
  unfold Genv.public_symbol in PUB.
  destruct (Genv.find_symbol se id) as [b1|] eqn:FND1; try discriminate.
  cbn in *.
  inv FND.
  assert (sup_In b (Genv.genv_sup se)) as INBOUND.
  {
    unfold Genv.find_symbol in FND1.
    eapply Genv.genv_symb_range; eauto.
  }
  unfold Genv.public_symbol in PUB1.
  destruct (Genv.find_symbol tse id) as [b1|] eqn:FND2; try discriminate.
  exists b1; split; auto.
  unfold init_meminj.
  rewrite (Genv.find_invert_symbol _ id); auto.
  rewrite FND2. auto.
Qed.

(** Injections that preserve used globals. *)

Record meminj_preserves_globals (f: meminj) : Prop := {
<<<<<<< HEAD
  (** Invariants for global injections *)
=======
  symbols_inject_0: forall id b' delta,
    f (Global id) = Some (b', delta) -> sup_In (Global id) (Genv.genv_sup ge) ->
      b' = Global id /\ delta = 0;  
>>>>>>> origin/StackAware-new
  symbols_inject_1: forall id b b' delta,
    f b = Some(b', delta) -> Genv.find_symbol ge id = Some b ->
    delta = 0 /\ Genv.find_symbol tge id = Some b';
  symbols_inject_3: forall id b',
    Genv.find_symbol tge id = Some b' ->
    exists b, Genv.find_symbol ge id = Some b /\ f b = Some(b', 0);
  symbols_inject_public: forall id b,
    Genv.public_symbol se id = true -> 
    Genv.find_symbol ge id = Some b ->
    exists b', Genv.find_symbol tge id = Some b' /\ f b = Some(b', 0);
  info_inject: forall b b' delta gd,
    f b = Some(b', delta) -> NMap.get _ b (Genv.genv_info ge) = Some gd ->
    NMap.get _ b' (Genv.genv_info tge) = Some gd /\ delta = 0;
  info_rev_inject: forall b b' delta gd,
    f b = Some(b', delta) -> NMap.get _ b' (Genv.genv_info tge) = Some gd ->
    NMap.get _ b (Genv.genv_info ge) = Some gd /\ delta = 0;

  (** Invariants for module-local injections *)
  symbols_inject_2: forall id b,
    kept id -> Genv.find_symbol ge id = Some b ->
    exists b', Genv.find_symbol tge id = Some b' /\ f b = Some(b', 0);
  defs_inject: forall b b' delta gd,
    f b = Some(b', delta) -> Genv.find_def ge b = Some gd ->
    Genv.find_def tge b' = Some gd /\ delta = 0 /\
    (forall id, ref_def gd id -> kept id);
}.

Remark init_meminj_eq:
  forall id b b',
  Genv.find_symbol ge id = Some b -> Genv.find_symbol tge id = Some b' ->
  init_meminj se tse b = Some(b', 0).
Proof.
  intros. unfold init_meminj. erewrite Genv.find_invert_symbol by eauto. 
  subst tge. cbn in H0. rewrite H0. auto.
Qed.

Remark init_meminj_invert:
  forall b b' delta,
  init_meminj se tse b = Some(b', delta) ->
  delta = 0 /\ exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol tge id = Some b'.
Proof.
  unfold init_meminj; intros.
  destruct (Genv.invert_symbol se b) as [id|] eqn:S; try discriminate.
  destruct (Genv.find_symbol tse id) as [b''|] eqn:F; inv H.
  split. auto. exists id. split. apply Genv.invert_find_symbol; auto. auto.
Qed.

Lemma init_meminj_preserves_globals:
  meminj_preserves_globals (init_meminj se tse).
Proof.
  constructor; intros.
- unfold init_meminj in H. repeat destr_in H.
  apply Genv.invert_find_symbol in Heqo.
  apply Genv.genv_vars_eq in Heqo.
  apply Genv.genv_vars_eq in Heqo0. split; congruence.
- exploit init_meminj_invert; eauto. intros (A & id1 & B & C).
  assert (id1 = id) by (eapply (Genv.genv_vars_inj ge); eauto). subst id1.
  auto.
- exploit symb_incl; eauto. intros (b & F).
  exists b; split; auto. eapply init_meminj_eq; eauto.
- exploit symbols_inject_init_public; eauto. 
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  exploit info_eq; eauto.
  intros EQ.
  split; auto. 
  cbn. unfold Genv.find_info in EQ. rewrite <- EQ.
  apply H0.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  exploit info_eq; eauto.
  intros EQ.
  split; auto. 
  cbn. unfold Genv.find_info in EQ. rewrite EQ.
  apply H0.
- exploit transform_find_symbol_1; eauto. intros (b' & F). exists b'; split; auto.
  eapply init_meminj_eq; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). 
  unfold tge. rewrite Genv.find_def_spec.
  rewrite (Genv.find_invert_symbol tse id); auto.
  unfold ge in H0. rewrite Genv.find_def_spec in H0.
  destruct (Genv.invert_symbol se b) eqn:INV; try discriminate.
  rewrite (Genv.find_invert_symbol se id) in INV; auto. 
  inv INV.
  generalize (erase_program_defmap p i).
  rewrite H0. cbn [option_map].
  intros DEF.
  generalize (remove_unused_consistent _ _ _ DEF C).
  intros TDEF.
  unfold tskel in TDEF.
  rewrite erase_program_defmap in TDEF.
  unfold option_map in TDEF.
  destruct ((prog_defmap tp) ! i) eqn:TDEF'; try discriminate.
  inv TDEF.
  inv TRANSF. 
  rewrite (match_prog_def0 i) in TDEF'.
  destruct (IS.mem i used) eqn:MEM; try discriminate.
  rewrite H0 in TDEF'. inv TDEF'.
  split; auto.
  split; auto.
  inv USED_VALID.
  intros. 
  apply used_closed0 with i g; eauto.
  apply IS.mem_2; auto.
  erewrite inj_preserved in MEM; eauto. congruence.
Qed.

Remark inj_eq:
  forall id b b',
  Genv.find_symbol se id = Some b -> Genv.find_symbol tse id = Some b' ->
  injw_meminj w b = Some(b', 0).
Proof.
  intros.
  inv GE. exploit Genv.mge_img; eauto.
  eapply Genv.genv_symb_range; eauto.
  intros (b1 & INJ1).
  exploit Genv.mge_symb; eauto.
  intro EQ. apply EQ in H0 as F'.
  setoid_rewrite F' in H. inv H. eauto.
Qed.


Lemma inj_world_preserves_globals:
  meminj_preserves_globals w.
Proof.
  constructor.
  - intros. inv GE. inv inj_stbls_match.
    exploit mge_dom; eauto.
    eapply Genv.genv_symb_range; eauto.
    intro. subst.
    exploit mge_symb; eauto.
    intro EQ. apply EQ in H0.
    destruct H1 as [A B]. rewrite H in B. inv B.
    split; eauto.
  - intros. exploit symb_incl; eauto.
    intros [b0 FIND]. exists b0. split. auto.
    eapply inj_eq; eauto.
  - intros.
    exploit symbols_inject_init_public; eauto.
    intros [b' [FIND _]]. exists b'. split. auto.
    eapply inj_eq; eauto.
  - intros. inv GE. inv inj_stbls_match. split.
    erewrite <- mge_info; eauto.
    exploit mge_dom; eauto.
    eapply Genv.genv_info_range; eauto.
    intros [b2 INJ]. rewrite H in INJ. congruence.
  - intros.  inv GE. inv inj_stbls_match. split.
    erewrite mge_info; eauto.
    exploit mge_img; eauto. eapply Genv.genv_info_range; eauto.
    intros [b1 INJ].
    erewrite <- mge_info in H0. 2: apply H.
    exploit mge_dom; eauto.
    eapply Genv.genv_info_range; eauto.
    intros [b2 INJ']. rewrite H in INJ'. congruence.
  - intros.
    exploit transform_find_symbol_1; eauto.
    intros (b' & FIND'). exists b'. split. auto.
    eapply inj_eq; eauto.
  - intros.
    inversion GE. inversion inj_stbls_match.
    unfold ge in H0. rewrite Genv.find_def_spec in H0.
    destruct (Genv.invert_symbol se b) eqn:REV1; try discriminate.
    apply Genv.invert_find_symbol in REV1 as FIND1.
    unfold tge. rewrite Genv.find_def_spec.
    exploit mge_symb; eauto. intro FINDEQ.
    apply FINDEQ in FIND1 as FIND2.
    apply Genv.find_invert_symbol in FIND2 as REV2.
    rewrite REV2.
    exploit mge_dom; eauto. eapply Genv.genv_symb_range; eauto.
    intro. subst.
    exploit remove_unused_consistent_p; eauto.
    intro A.
    split. auto. split.
    destruct H1 as [b2 INJ]. rewrite H in INJ. congruence.
    destruct (IS.mem i used) eqn:MEM; try discriminate.
    inv USED_VALID.
    intros. 
    apply used_closed0 with i gd; eauto.
    apply IS.mem_2; eauto.
    erewrite inj_preserved in MEM; eauto. congruence.
Qed.

(*  generalize init_meminj_preserves_globals.
  intros PRES. 
  constructor.
  - inv PRES. intros.
    eapply symbols_inject_4; eauto.    
    eapply winj_consistent_1; eauto.
    eapply Genv.genv_symb_range; eauto.
  - inv PRES. intros. 
    exploit symbols_inject_5; eauto.
    intros (b & FND & INIT).
    exists b; split; auto.
  - inv PRES. intros.
    exploit symbols_inject_public0; eauto.
    intros (b' & FND & INIT).
    exists b'; split; auto.
  - inv PRES. intros.
    eapply info_inject0; eauto.
    eapply winj_consistent_1; eauto.
    eapply Genv.genv_info_range; eauto.
  - inv PRES. intros.
    exploit info_rev_inject0; eauto.
    eapply winj_consistent_2; eauto.
    eapply Genv.genv_info_range; eauto.
  - inv PRES. intros.
    exploit symbols_inject_6; eauto.
    intros (b' & FND & INIT).
    exists b'; split; auto.
  - inv PRES. intros.
    eapply defs_inject0; eauto.
    eapply winj_consistent_1; eauto.
    exploit Genv.genv_defs_range; eauto.
Qed.
    *)

Lemma globals_symbols_inject:
  forall j, meminj_preserves_globals j -> symbols_inject j ge tge.
Proof.
  intros.
  split; [|split;[|split]]; intros.
  + unfold ge, tge. cbn. 
    rewrite se_public_same. auto.
  + eapply symbols_inject_1; eauto.
  + exploit symbols_inject_public; eauto. 
    intros (b' & FND & INJ).
    eauto.
  + unfold Genv.block_is_volatile.
    destruct (NMap.get _ b1 (Genv.genv_info ge)) as [gd|] eqn:V1.
    - generalize (info_inject _ H _ _ _ _ H0 V1); eauto.
      intros (V2 & D). subst.
      rewrite V2. auto.
    - destruct (NMap.get _ b2 (Genv.genv_info tge)) as [gd2|] eqn:V2; auto.
      destruct gd2; auto.
      generalize (info_rev_inject _ H _ _ _ _ H0 V2).
      intros (V3 & D). subst.
      rewrite V1 in V3. discriminate.
Qed.

Lemma symbol_address_inject:
  forall j id ofs,
  meminj_preserves_globals j -> kept id ->
  Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & TFS & INJ). rewrite TFS.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

(** Semantic preservation *)

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

Inductive astackseq : stackadt -> stackadt -> Prop :=
  |astackseq_nil : astackseq nil nil
  |astackseq_cons : forall tl1 tl2 b1 b2 size,
      astackseq tl1 tl2 ->
      astackseq (((mk_frame b1 size) :: nil) :: tl1) (((mk_frame b2 size) :: nil) :: tl2).

Lemma astackseq_nil_refl : forall as1 as2,
    astackseq as1 as2 ->
    as1 <> nil <-> as2 <> nil.
Proof.
  intros. induction H; eauto. reflexivity.
  split; congruence.
Qed.

Lemma astackseq_size : forall as1 as2,
    astackseq as1 as2 ->
    stack_size as1 = stack_size as2.
Proof.
  intros. induction H; eauto.
  simpl. unfold frame_size_a. simpl.  lia.
Qed.

Inductive match_stacks (j: meminj):
        list stackframe -> list stackframe -> sup -> sup -> Prop :=
  | match_stacks_nil: forall bound tbound,
      meminj_preserves_globals j ->
      inj_incr w (injw j bound tbound) ->
      Mem.sup_include (Genv.genv_sup ge) bound -> Mem.sup_include (Genv.genv_sup tge) tbound ->
      match_stacks j nil nil bound tbound
| match_stacks_cons: forall res f sp pc rs s tsp trs ts bound tbound sps tsps
         (SPS: sp = fresh_block sps)
         (TSPS: tsp = fresh_block tsps)
         (STACKS: match_stacks j s ts sps tsps)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (BELOW: Mem.sup_include (sup_incr sps) bound)
         (TBELOW: Mem.sup_include (sup_incr tsps) tbound),
      match_stacks j (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: s)
                     (Stackframe res f (Vptr tsp Ptrofs.zero) pc trs :: ts)
                     bound tbound.


Lemma match_stacks_bound1: forall j s ts sps tsps,
    match_stacks j s ts sps tsps -> Mem.sup_include (Genv.genv_sup se) sps.
Proof.
  induction 1; auto.
  eapply Mem.sup_include_trans; eauto.
Qed.

Lemma match_stacks_bound2: forall j s ts sps tsps,
    match_stacks j s ts sps tsps -> Mem.sup_include (Genv.genv_sup tse) tsps.
Proof.
  induction 1; auto.
  eapply Mem.sup_include_trans; eauto.
Qed.

Lemma match_stacks_incr_bound
     : forall (j : meminj) s ts
         (bound tbound : sup) (bound' tbound' : sup),
       match_stacks j s ts bound tbound ->
       Mem.sup_include bound bound' ->
       Mem.sup_include tbound tbound' -> match_stacks j s ts bound' tbound'.
Proof.
  intros. inv H. inv H3.
  econstructor; eauto. rewrite <- H9. econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma match_stacks_match_stbls:
  forall j s ts sp tsp,
    CKLR.match_stbls inj w se tse ->
    match_stacks j s ts sp tsp ->
    Genv.match_stbls j se tse.
Proof.
  induction 2; eauto. 
  generalize (CKLR.match_stbls_acc inj). cbn.
  intros MONO.
  repeat red in MONO. 
  generalize (MONO _ _ H1 se tse). intros SUB. 
  apply SUB.
  apply H.
Qed.

Lemma match_stacks_preserves_globals:
  forall j s ts bound tbound,
  match_stacks j s ts bound tbound ->
  meminj_preserves_globals j.
Proof.
  induction 1; auto.
Qed.


Lemma meminj_preserves_globals_incr: forall j j' bound tbound,
  inject_incr j j' ->
  Mem.sup_include (Genv.genv_sup ge) bound ->
  Mem.sup_include (Genv.genv_sup tge) tbound ->
  (forall b1 b2 delta,
      j b1 = None -> j' b1 = Some(b2, delta) -> ~sup_In b1 bound /\ ~ sup_In b2 tbound) ->
  meminj_preserves_globals j ->
  meminj_preserves_globals j'.
Proof.
  intros j j' bound tbound INCR BND1 BND2 SEP PRES.
  assert (SAME: forall b b' delta, sup_In b (Genv.genv_sup ge) ->
                              j' b = Some(b', delta) -> j b = Some(b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
    exploit INCR; eauto. congruence.
    exploit SEP; eauto. intros [A B].
    exfalso. apply A. apply BND1; eauto. }
  assert (SAME': forall b b' delta, sup_In b' (Genv.genv_sup tge) ->
                               j' b = Some(b', delta) -> j b = Some (b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
<<<<<<< HEAD
    exploit INCR; eauto. congruence.
    exploit SEP; eauto. intros [A B].
    exfalso. apply B. apply BND2; eauto. }
  constructor; intros.  
=======
    exploit H; eauto. congruence.
    exploit H3; eauto. intros [A B].
    apply H2 in H4. congruence. }
  constructor; auto.  constructor; intros.
  + exploit symbols_inject_0; eauto.
>>>>>>> origin/StackAware-new
  + exploit symbols_inject_1; eauto. apply SAME; auto.
    eapply Genv.genv_symb_range; eauto.
  + exploit symbols_inject_3; eauto. intros (b & A & B).
    exists b; auto.
  + exploit symbols_inject_public; eauto. intros (b' & A & B).
    exists b'; auto.
  + eapply info_inject; eauto. apply SAME; auto.
    eapply Genv.genv_info_range; eauto.
  + eapply info_rev_inject; eauto. apply SAME'; auto.
    eapply Genv.genv_info_range; eauto.
  + exploit symbols_inject_2; eauto. intros (b' & A & B).
    exists b'; auto.
  + eapply defs_inject; eauto. apply SAME; auto.
    eapply Genv.genv_defs_range; eauto.
Qed.


Lemma match_stacks_incr_aux:
  forall j bound tbound s ts, 
    match_stacks j s ts bound tbound ->
    forall j' bound' tbound', 
      inj_incr (injw j bound tbound) (injw j' bound' tbound') ->
      match_stacks j' s ts bound' tbound'.
Proof.
  induction 1; intros.
  inv H3.
- constructor; auto.
  + eapply meminj_preserves_globals_incr; eauto.
  + etransitivity. exact H0. auto.
  + eauto with mem.
  + eauto with mem.
- inv H0. econstructor; eauto.
  + apply IHmatch_stacks; auto.
    ++ constructor; auto; try lia.
       intro. intros. exploit H8; eauto.
       intros (BND1 & BND2). split.
       intro. apply BND1. apply BELOW. right. eauto.
       intro. apply BND2. apply TBELOW. right. eauto.
  + eapply regset_inject_incr; eauto.
Qed.

Lemma match_stacks_incr:
  forall j j' bound bound' tbound tbound' s ts, 
    inj_incr (injw j bound tbound) (injw j' bound' tbound') ->
    match_stacks j s ts bound tbound ->
    match_stacks j' s ts bound' tbound'.
Proof.
  intros. 
  apply match_stacks_incr_aux with j bound tbound; auto.
Qed.

Lemma match_stacks_bound:
  forall j s ts bound tbound bound' tbound',
  match_stacks j s ts bound tbound ->
  Mem.sup_include bound bound' -> Mem.sup_include tbound tbound' ->
  match_stacks j s ts bound' tbound'.
Proof.
  induction 1; intros.
- econstructor; eauto with mem.
  + inv H0. 
    constructor; eauto with mem.
- econstructor; eauto.
Qed.


Inductive match_states: state -> state -> Prop :=
| match_states_regular: forall s f sp sps pc rs m ts tsp tsps trs tm j
         (SPS: sp = fresh_block sps)
         (TSPS: tsp = fresh_block tsps)
         (STACKS: match_stacks j s ts sps tsps)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (MEMINJ: Mem.inject j m tm)
         (MASTK: astackseq (Mem.astack (Mem.support m)) (Mem.astack (Mem.support tm)))
         (SUPINC: Mem.sup_include sps (Mem.support m))
         (TSUPINC: Mem.sup_include tsps (Mem.support tm)),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State ts f (Vptr tsp Ptrofs.zero) pc trs tm)
<<<<<<< HEAD
  | match_states_call: forall s vf tvf fd args m ts targs tm j
=======
  | match_states_call: forall s fd args m ts targs tm j id
>>>>>>> origin/StackAware-new
         (STACKS: match_stacks j s ts (Mem.support m) (Mem.support tm))
         (FUN: Genv.find_funct ge vf = Some fd)
         (FUNINJ: Val.inject j vf tvf)
         (KEPT: forall id, ref_fundef fd id -> kept id)
         (ARGINJ: Val.inject_list j args targs)
         (MASTK: astackseq (Mem.astack (Mem.support m)) (Mem.astack (Mem.support tm)))
         (MEMINJ: Mem.inject j m tm),
<<<<<<< HEAD
      match_states (Callstate s vf args m)
                   (Callstate ts tvf targs tm)
=======
      match_states (Callstate s fd args m id)
                   (Callstate ts fd targs tm id)
>>>>>>> origin/StackAware-new
  | match_states_return: forall s res m ts tres tm j
         (STACKS: match_stacks j s ts (Mem.support m) (Mem.support tm))
         (RESINJ: Val.inject j res tres)
         (MASTK: astackseq (Mem.astack (Mem.support m)) (Mem.astack (Mem.support tm)))
         (MEMINJ: Mem.inject j m tm),
      match_states (Returnstate s res m)
        (Returnstate ts tres tm).

Lemma external_call_inject:
  forall ef vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
    external_call ef tge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros.
  exploit external_call_mem_inject_gen'; eauto.
  apply globals_symbols_inject; auto.
  intros (f' & vres' & m2' & A & B & C & D & E & F & G & I).
  exists f',vres',m2'. split. auto. split. auto. split. auto.
  split. auto. split; auto.
Qed.

Lemma find_function_inject:
  forall j vf tvf fd,
  meminj_preserves_globals j ->
  Val.inject j vf tvf ->
  Genv.find_funct ge vf = Some fd ->
  Genv.find_funct tge tvf = Some fd /\ (forall id, ref_fundef fd id -> kept id).
Proof.
  intros j vf tvf fd PRES INJ FIND.
  unfold Genv.find_funct in FIND.
  destruct vf; try discriminate.
  destruct Ptrofs.eq_dec; try discriminate.
  subst.
  rewrite Genv.find_funct_ptr_iff in FIND.
  inv INJ.
  generalize (defs_inject _ PRES _ _ _ _ H1 FIND); eauto.
  intros (FDEF & D' & KEPTS). subst.
  cbn.
  rewrite Ptrofs.add_zero_l. 
  unfold Ptrofs.zero.
  destruct Ptrofs.eq_dec; try congruence.
  rewrite Genv.find_funct_ptr_iff.
  auto.
Qed.

Lemma ros_address_inject: forall ros j rs trs,
  meminj_preserves_globals j ->
  match ros with inl r => regset_inject j rs trs | inr id => kept id end ->
  Val.inject j (ros_address ge ros rs) (ros_address tge ros trs).
Proof.
  intros. destruct ros as [r|id]; simpl in *.
  - auto.
  - unfold Genv.symbol_address.
    destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
    exploit symbols_inject_2; eauto. intros (tb & P & Q). 
    cbn in P. rewrite P. 
    econstructor; eauto.
Qed.

Lemma find_function_inject_ros:
  forall j ros rs fd trs,
  meminj_preserves_globals j ->
  Genv.find_funct ge (ros_address ge ros rs) = Some fd ->
  match ros with inl r => regset_inject j rs trs | inr id => kept id end ->
  Genv.find_funct tge (ros_address tge ros trs) = Some fd /\ 
  (forall id, ref_fundef fd id -> kept id).
Proof.
  intros j ros rs fd trs PRES FIND ROS.
  generalize (ros_address_inject _ _ _ _ PRES ROS).
  intros INJ.
  generalize (find_function_inject _ _ _ _ PRES INJ FIND).
  auto.
Qed.

Lemma eval_builtin_arg_inject:
  forall rs sp m j rs' sp' m' a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_arg a) -> kept id) ->
  exists v',
     eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
  /\ Val.inject j v v'.
Proof.
  induction 1; intros SP GL RS MI K; simpl in K.
- exists rs'#x; split; auto. constructor.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- simpl in H. exploit Mem.load_inject; eauto. rewrite Z.add_0_r.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. simpl. econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- assert (Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs)).
  { unfold Genv.symbol_address. 
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
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
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_builtin_args al) -> kept id) ->
  exists vl',
     eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; intros.
- exists (@nil val); split; constructor.
- simpl in H5.
  exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app.
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma ros_is_ident_transf:
    forall ros rs trs j id fd,
      ros_is_ident ros rs id ->
      find_function ge ros rs = Some fd ->
      meminj_preserves_globals j ->
      regset_inject j rs trs ->
      ros_is_ident ros trs id.
Proof.
  intros.
  destruct ros; simpl in *.  generalize (H2 r).
  intro. inv H3; (try congruence).
  rewrite H in H4. inv H4.
  rewrite H in H0. simpl in H0.
  destr_in H0. subst. unfold Genv.find_funct_ptr in H0.
  destr_in H0. inv H0. inv H1.
  exploit symbols_inject_4; eauto. eapply Genv.genv_defs_range; eauto.
  intros [C D]. subst. intros. eauto.
  eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2, step fn_stack_requirements ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  assert (A: exists tv,
               eval_operation tge (Vptr (fresh_block tsps) Ptrofs.zero) op trs##args tm = Some tv
            /\ Val.inject j v tv).
  { apply eval_operation_inj with (ge1 := ge) (m1 := m) (sp1 := Vptr (fresh_block sps) Ptrofs.zero) (vl1 := rs##args).
    intros; eapply Mem.valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
    intros; eapply Mem.different_pointers_inject; eauto.
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iop op args res pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (tv & B & C).
  econstructor; split. eapply exec_Iop; eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* load *)
  assert (A: exists ta,
               eval_addressing tge (Vptr (fresh_block tsps) Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr (fresh_block sps) Ptrofs.zero) (vl1 := rs##args).
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iload chunk addr args dst pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.loadv_inject; eauto. intros (tv & D & E).
  econstructor; split. eapply exec_Iload; eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  assert (A: exists ta,
               eval_addressing tge (Vptr (fresh_block tsps) Ptrofs.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr (fresh_block sps) Ptrofs.zero) (vl1 := rs##args).
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Istore chunk addr args src pc'); auto.
    econstructor; eauto.
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.storev_mapped_inject; eauto. intros (tm' & D & E).
  econstructor; split. eapply exec_Istore; eauto.
<<<<<<< HEAD
  econstructor; eauto. erewrite <- Mem.support_storev; eauto.
  erewrite <- Mem.support_storev; eauto.

=======
  econstructor;
  try (rewrite <- (Mem.support_storev _ _ _ _ _ H1)); eauto.
  rewrite <- (Mem.support_storev _ _ _ _ _ D). auto.
  rewrite <- (Mem.support_storev _ _ _ _ _ D). auto.
>>>>>>> origin/StackAware-new
- (* call *)
  exploit find_function_inject_ros.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id']. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  econstructor; split. eapply exec_Icall; eauto.
  eapply ros_is_ident_transf; eauto. eapply match_stacks_preserves_globals; eauto.
  econstructor; eauto.
<<<<<<< HEAD
  + econstructor; eauto.
    intro. intro. apply Mem.sup_incr_in in H1. destruct H1.
    change (Mem.valid_block m b). subst b. eapply Mem.valid_block_inject_1; eauto.
    apply SUPINC; eauto.
    intro. intro. apply Mem.sup_incr_in in H1. destruct H1.
    change (Mem.valid_block tm b). subst b. eapply Mem.valid_block_inject_2; eauto.
    apply TSUPINC; eauto.
  + subst vf.
    unfold ros_address. 
    destruct ros; eauto.
    eapply symbol_address_inject; eauto.
    eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  + apply regs_inject; auto.
=======
  econstructor; eauto.
  intro. intro. apply Mem.sup_incr_in in H2. destruct H2.
  change (Mem.valid_block m b). subst b. eapply Mem.valid_block_inject_1;eauto. apply SUPINC; auto.
  intro. intro. apply Mem.sup_incr_in in H2. destruct H2.
  change (Mem.valid_block tm b). subst b. eapply Mem.valid_block_inject_2;eauto. apply TSUPINC; auto.
  apply regs_inject; auto.
>>>>>>> origin/StackAware-new

    
- (* tailcall *)
  exploit find_function_inject_ros.
  eapply match_stacks_preserves_globals; eauto. eauto.
  destruct ros as [r|id']. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (tm' & C & D).
  apply Mem.support_free in C as SUPF. apply Mem.support_free in H3 as SUPF'.
  exploit Mem.pop_stage_parallel_inject; eauto. rewrite SUPF. apply astackseq_nil_refl in MASTK.
  rewrite <- MASTK. rewrite <- SUPF'.            
  eapply Mem.pop_stage_nonempty; eauto.
  intros (tm''' & G & I).
  econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply ros_is_ident_transf; eauto. eapply match_stacks_preserves_globals; eauto.
  econstructor; eauto.
<<<<<<< HEAD
  + apply match_stacks_bound with sps tsps; auto.
    erewrite Mem.support_free; eauto.
    erewrite Mem.support_free; eauto.
  + subst vf.
    unfold ros_address.
    destruct ros; eauto.
    eapply symbol_address_inject; eauto.
    eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  + apply regs_inject; auto.

=======
  apply match_stacks_bound with sps tsps; auto.
  eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto.
  intro. eapply Mem.support_pop_stage_1 in H4. apply H4.
  eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto.
  intro. eapply Mem.support_pop_stage_1 in G. apply G.
  apply regs_inject; auto.
  apply Mem.astack_pop_stage in H4. destruct H4. apply Mem.astack_pop_stage in G.
  destruct G. rewrite <- SUPF', H2 in MASTK. rewrite <- SUPF, H4 in MASTK.
  inv MASTK. eauto.
>>>>>>> origin/StackAware-new
- (* builtin *)
  exploit eval_builtin_args_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros. apply KEPT. red. econstructor; econstructor; eauto.
  intros (vargs' & P & Q).
  exploit external_call_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros (j' & tv & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply match_states_regular with (j := j'); eauto.
<<<<<<< HEAD
  + apply match_stacks_incr with j sps tsps; eauto.
    constructor; auto.
    intro. intros. exploit G; eauto. intros [U V]. split.
    intro. apply U. apply SUPINC; eauto.
    intro. apply V. apply TSUPINC; eauto.
  + apply set_res_inject; auto. apply regset_inject_incr with j; auto.
  + inversion D. eauto with mem.
  + inversion E. eauto with mem.

=======
  apply match_stacks_incr with j; auto.
  intros. exploit G; eauto. intros [U V].
  split.
  intro. apply SUPINC in H4. apply U. auto.
  intro. apply TSUPINC in H4. apply V. auto.
  apply set_res_inject; auto. apply regset_inject_incr with j; auto.
  apply external_call_astack in H1. apply external_call_astack in A.
  congruence.
  eapply Mem.sup_include_trans. eauto. eapply Mem.unchanged_on_support;eauto.
  eapply Mem.sup_include_trans. eauto. eapply Mem.unchanged_on_support;eauto.
>>>>>>> origin/StackAware-new
- (* cond *)
  assert (C: eval_condition cond trs##args tm = Some b).
  { eapply eval_condition_inject; eauto. apply regs_inject; auto. }
  econstructor; split.
  eapply exec_Icond with (pc' := if b then ifso else ifnot); eauto.
  econstructor; eauto.

- (* jumptbl *)
  generalize (REGINJ arg); rewrite H0; intros INJ; inv INJ.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (tm' & C & D).
  apply Mem.support_free in H0 as SUPF. apply Mem.support_free in C as SUPF'.
  exploit Mem.pop_stage_parallel_inject; eauto.
  apply Mem.pop_stage_nonempty in H1.
  apply astackseq_nil_refl in MASTK. rewrite SUPF'. apply MASTK. rewrite <- SUPF. eauto.
  intros (tm''' & G & I).
  econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; subst; eauto.
  apply match_stacks_bound with sps tsps; auto.
  eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto.
  intro. eapply Mem.support_pop_stage_1 in H1. apply H1.
  eapply Mem.sup_include_trans; eauto.
  erewrite <- Mem.support_free; eauto.
  intro. eapply Mem.support_pop_stage_1 in G. apply G.
  destruct or; simpl; auto.
  apply Mem.astack_pop_stage in H1. destruct H1. apply Mem.astack_pop_stage in G.
  destruct G. rewrite <- SUPF', H2, <- SUPF, H1 in MASTK. inv MASTK. eauto.
- (* internal function *)
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (j' & tm'' & tstk & C & D & E & F & G).
  apply Mem.astack_alloc in H as ASTKA.
  apply Mem.astack_alloc in C as ASTKA'. 
  exploit Mem.push_stage_inject. eauto. intro.
  exploit Mem.record_frame_parallel_inject; eauto. simpl. congruence.
  simpl. rewrite ASTKA', ASTKA. apply astackseq_size in MASTK. lia.
  intros (tm''' & I & J).
  assert (STK: stk = Mem.nextblock m) by (eapply Mem.alloc_result; eauto).
  assert (TSTK: tstk = Mem.nextblock tm) by (eapply Mem.alloc_result; eauto).
  assert (STACKS': match_stacks j' s ts (Mem.support m) (Mem.support tm)).
<<<<<<< HEAD
  { 
    apply match_stacks_incr with j (Mem.support m) (Mem.support tm); auto.
    constructor; auto; try lia.
    intro. intros. destruct (eq_block b stk).
    subst b. rewrite F in H1; inv H1.
    split; apply freshness.
    rewrite G in H1 by auto. congruence. }
=======
  {
    apply match_stacks_incr with j; auto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite F in H3; inv H3. split. apply freshness.
    apply freshness.
    rewrite G in H3 by auto. congruence. }
>>>>>>> origin/StackAware-new
  econstructor; split.
  rewrite FIND in FUN. inv FUN.
  eapply exec_function_internal; eauto.
  eapply find_function_inject; eauto.
  generalize (match_stacks_preserves_globals _ _ _ _ _ STACKS).
  auto. 
  subst.
  eapply match_states_regular with (j := j'); eauto.
<<<<<<< HEAD
  + reflexivity.
  + reflexivity.
  + intros id REF. rewrite FIND in FUN. inv FUN. auto.
  + apply init_regs_inject; auto. apply val_inject_list_incr with j; auto.
  + rewrite (Mem.support_alloc _ _ _ _ _  H). apply Mem.sup_incr_in2.
  + rewrite (Mem.support_alloc _ _ _ _ _  C). apply Mem.sup_incr_in2.
=======
  apply init_regs_inject; auto. apply val_inject_list_incr with j; auto.
  apply Mem.astack_record_frame in H0. apply Mem.astack_record_frame in I.
  destruct H0 as [a [b [c d]]]. destruct I as [e[f'[g h]]]. simpl in *.
  rewrite d,h. inv g. inv c. econstructor. rewrite ASTKA, ASTKA'. auto.
  eapply Mem.sup_include_trans. 2: { intro; eapply Mem.support_record_frame_1 in H0; apply H0; eauto. } simpl.
  rewrite Mem.support_alloc with m 0 (fn_stacksize f) m' stk. apply Mem.sup_incr_in2. auto.
  eapply Mem.sup_include_trans. 2: {intro; eapply Mem.support_record_frame_1 in I. apply I; eauto. } simpl.
  rewrite Mem.support_alloc with tm 0 (fn_stacksize f) tm'' tstk. apply Mem.sup_incr_in2. auto.
>>>>>>> origin/StackAware-new

- (* external function *)
  exploit external_call_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  intros (j' & tres & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  rewrite FIND in FUN. inv FUN.
  eapply exec_function_external; eauto.
  eapply find_function_inject; eauto.
  generalize (match_stacks_preserves_globals _ _ _ _ _ STACKS).
  auto.
  eapply match_states_return with (j := j'); eauto.
  apply match_stacks_bound with (Mem.support m) (Mem.support tm).
<<<<<<< HEAD
  apply match_stacks_incr 
    with j (Mem.support m) (Mem.support tm); auto.
  inversion D. eauto. inversion E. eauto.
=======
  apply match_stacks_incr with j; auto.
  eapply external_call_support; eauto.
  eapply external_call_support; eauto.
  apply external_call_astack in H. apply external_call_astack in A.
  congruence.
>>>>>>> origin/StackAware-new

- (* return *)
  inv STACKS. econstructor; split.
  eapply exec_return.
  econstructor; eauto. apply set_reg_inject; auto.
<<<<<<< HEAD
=======
  intro. intro. apply BELOW. apply Mem.sup_incr_in2. auto.
  intro. intro. apply TBELOW. apply Mem.sup_incr_in2. auto.
Qed.

(** Relating initial memory states *)

(*
Remark genv_find_def_exists:
  forall (F V: Type) (p: AST.program F V) b,
  Plt b (Genv.genv_next (Genv.globalenv p)) ->
  exists gd, Genv.find_def (Genv.globalenv p) b = Some gd.
Proof.
  intros until b.
  set (P := fun (g: Genv.t F V) =>
        Plt b (Genv.genv_next g) -> exists gd, (Genv.genv_defs g)!b = Some gd).
  assert (forall l g, P g -> P (Genv.add_globals g l)).
  { induction l as [ | [id1 g1] l]; simpl; intros.
  - auto.
  - apply IHl. unfold Genv.add_global, P; simpl. intros LT. apply Plt_succ_inv in LT. destruct LT.
  + rewrite PTree.gso. apply H; auto. apply Plt_ne; auto.
  + rewrite H0. rewrite PTree.gss. exists g1; auto. }
  apply H. red; simpl; intros. exfalso; extlia.
Qed.
*)

Lemma init_meminj_invert_strong:
  forall b b' delta,
  init_meminj b = Some(b', delta) ->
  delta = 0 /\
  exists id gd,
     Genv.find_symbol ge id = Some b
  /\ Genv.find_symbol tge id = Some b'
  /\ Genv.find_def ge b = Some gd
  /\ Genv.find_def tge b' = Some gd
  /\ (forall i, ref_def gd i -> kept i).
Proof.
  intros. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  assert (exists gd, (prog_defmap p)!id = Some gd).
  { apply prog_defmap_dom. eapply Genv.find_symbol_inversion; eauto. }
  destruct H0 as [gd DM]. rewrite Genv.find_def_symbol in DM.
  destruct DM as (b'' & P & Q). fold ge in P. rewrite P in B; inv B.
  fold ge in Q. exploit defs_inject. apply init_meminj_preserves_globals.
  eauto. eauto. intros (X & _ & Y).
  split. auto. exists id, gd; auto.
Qed.

Section INIT_MEM.

Variables m tm: mem.
Hypothesis IM: Genv.init_mem p = Some m.
Hypothesis TIM: Genv.init_mem tp = Some tm.

Lemma bytes_of_init_inject:
  forall il,
  (forall id, ref_init il id -> kept id) ->
  list_forall2 (memval_inject init_meminj) (Genv.bytes_of_init_data_list ge il) (Genv.bytes_of_init_data_list tge il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- constructor.
- apply list_forall2_app.
+ destruct i1; simpl; try (apply inj_bytes_inject).
  induction (Z.to_nat z); simpl; constructor. constructor. auto.
  destruct (Genv.find_symbol ge i) as [b|] eqn:FS.
  assert (kept i). { apply H. red. exists i0; auto with coqlib. }
  exploit symbols_inject_2. apply init_meminj_preserves_globals. eauto. eauto.
  intros (b' & A & B). rewrite A. apply inj_value_inject.
  econstructor; eauto. symmetry; apply Ptrofs.add_zero.
  destruct (Genv.find_symbol tge i) as [b'|] eqn:FS'.
  exploit symbols_inject_3. apply init_meminj_preserves_globals. eauto.
  intros (b & A & B). congruence.
  apply repeat_Undef_inject_self.
+ apply IHil. intros id [ofs IN]. apply H. exists ofs; auto with coqlib.
Qed.

Lemma Mem_getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 i n p,
  list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
  p <= i -> i < p + Z.of_nat n ->
  P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
- simpl in H1. extlia.
- inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p0).
+ congruence.
+ apply IHn with (p0 + 1); auto. lia. lia.
Qed.

Lemma init_mem_inj_1:
  Mem.mem_inj init_meminj m tm.
Proof.
  intros; constructor; intros.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. auto.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0. subst.
  apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P2. lia.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  subst delta. apply Z.divide_0_r.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (P2 & Q2) (P1 & Q1).
  apply Q1 in H0. destruct H0; discriminate.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q1 in H0. destruct H0.
  assert (NO: gvar_volatile v = false).
  { unfold Genv.perm_globvar in H1. destruct (gvar_volatile v); auto. inv H1. }
Local Transparent Mem.loadbytes.
  generalize (S1 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
  generalize (S2 NO). unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E2; inv E2.
  rewrite Z.add_0_r.
  apply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
  rewrite H3, H4. apply bytes_of_init_inject. auto.
  lia.
  rewrite Z2Nat.id by (apply Z.ge_le; apply init_data_list_size_pos). lia.
Qed.

Lemma init_mem_inj_2:
  Mem.inject init_meminj m tm.
Proof.
  constructor; intros.
- apply init_mem_inj_1.
- destruct (init_meminj b) as [[b' delta]|] eqn:INJ; auto.
  elim H. exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  eapply Genv.find_symbol_not_fresh; eauto.
- red; intros.
  exploit init_meminj_invert. eexact H0. intros (A1 & id1 & B1 & C1).
  exploit init_meminj_invert. eexact H1. intros (A2 & id2 & B2 & C2).
  destruct (ident_eq id1 id2). congruence. left; eapply Genv.global_addresses_distinct; eauto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). subst delta.
  split. lia. generalize (Ptrofs.unsigned_range_2 ofs). lia.
- exploit init_meminj_invert_strong; eauto. intros (A & id & gd & B & C & D & E & F).
  exploit (Genv.init_mem_characterization_gen p); eauto.
  exploit (Genv.init_mem_characterization_gen tp); eauto.
  destruct gd as [f|v].
+ intros (P2 & Q2) (P1 & Q1).
  apply Q2 in H0. destruct H0. subst. replace ofs with 0 by lia.
  left; apply Mem.perm_cur; auto.
+ intros (P2 & Q2 & R2 & S2) (P1 & Q1 & R1 & S1).
  apply Q2 in H0. destruct H0. subst.
  left. apply Mem.perm_cur. eapply Mem.perm_implies; eauto.
  apply P1. lia.
Qed.

End INIT_MEM.

Lemma init_mem_exists:
  forall m, Genv.init_mem p = Some m ->
  exists tm, Genv.init_mem tp = Some tm.
Proof.
  intros. apply Genv.init_mem_exists.
  intros.
  assert (P: (prog_defmap tp)!id = Some (Gvar v)).
  { eapply prog_defmap_norepet; eauto. eapply match_prog_unique; eauto. }
  rewrite (match_prog_def _ _ _ TRANSF) in P. destruct (IS.mem id used) eqn:U; try discriminate.
  exploit Genv.init_mem_inversion; eauto. apply in_prog_defmap; eauto. intros [AL FV].
  split. auto.
  intros. exploit FV; eauto. intros (b & FS).
  apply transform_find_symbol_1 with b; auto.
  apply kept_closed with id (Gvar v).
  apply IS.mem_2; auto. auto. red. red. exists o; auto.
Qed.

Theorem init_mem_inject:
  forall m,
  Genv.init_mem p = Some m ->
  exists tm, Genv.init_mem tp = Some tm /\ Mem.inject init_meminj m tm /\ meminj_preserves_globals init_meminj.
Proof.
  intros.
  exploit init_mem_exists; eauto. intros [tm INIT].
  exists tm.
  split. auto.
  split. eapply init_mem_inj_2; eauto.
  apply init_meminj_preserves_globals.
>>>>>>> origin/StackAware-new
Qed.

Lemma transf_initial_states:
  forall q1 q2,
    match_query (cc_c inj) w q1 q2 ->
  forall S, initial_state ge q1 S ->
  exists R, initial_state tge q2 R /\ match_states S R.
Proof.
<<<<<<< HEAD
  intros q1 q2 MQUERY S INIT_STATE.
  inv MQUERY. inv INIT_STATE.
  cbn in *.
  generalize inj_world_preserves_globals.
  intros PRES.
  eexists; split. 
  - constructor.
    generalize (find_function_inject _ _ _ _ PRES H H8).
    intros (FINDFUN & KEPT). auto.
  - eapply match_states_call with (j := injw_meminj w); eauto.
    + inversion GE.
      constructor; eauto.
      ++ inv H1; cbn in *. 
         constructor; intros; try congruence. 
      ++ inv H1; cbn in *. auto.
      ++ inv H1; cbn in *. auto.
    + generalize (find_function_inject _ _ _ _ PRES H H8).
      intros (FINDFUN & KEPT). auto.
=======
  intros. inv H. exploit init_mem_inject; eauto. intros (tm & A & B & C).
  exploit symbols_inject_2. eauto. eapply kept_main. eexact H1. intros (tb & P & Q).
  rewrite Genv.find_funct_ptr_iff in H2.
  exploit defs_inject. eauto. eexact Q. exact H2.
  intros (R & S & T).
  rewrite <- Genv.find_funct_ptr_iff in R.
  exploit Genv.init_mem_stack; eauto. intro STK2.
  exploit Genv.init_mem_stack. apply H0. intro STK1.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (f' & tm' & b' & U &V &W&X&Y).
  apply Mem.alloc_result in H4 as H5. unfold Mem.nextblock in H5. unfold fresh_block in H5.
  rewrite STK1 in H5. simpl in H5. subst.
  apply Mem.alloc_result in U as U'.  unfold Mem.nextblock in U'. unfold fresh_block in U'.
  rewrite STK2 in U'. simpl in U'. subst.
  apply Mem.valid_new_block in H4 as H6.
  apply Mem.valid_new_block in U as U''.
  apply Mem.stack_alloc in H4 as STK3. rewrite STK1 in STK3. simpl in STK3.
  apply Mem.stack_alloc in U as STK4. rewrite STK2 in STK4. simpl in STK4.
  exists (Callstate nil f nil tm' (prog_main tp)); split.
  econstructor; eauto.
  fold tge. erewrite match_prog_main by eauto. auto.
  erewrite <- match_prog_main; eauto.
  econstructor; eauto.
  eapply match_stacks_bound. 2: eapply Mem.sup_include_alloc; eauto. 2: eapply Mem.sup_include_alloc; eauto.
  eapply match_stacks_incr. eauto.
  constructor. auto.
  erewrite <- Genv.init_mem_genv_sup by eauto. apply Mem.sup_include_refl.
  erewrite <- Genv.init_mem_genv_sup by eauto. apply Mem.sup_include_refl.
  intros. destruct (eq_block b1 (Stack 1%positive)). subst. rewrite X in H5. inv H5.
  simpl. rewrite STK1. rewrite STK2. simpl. split. lia. lia. rewrite Y in H5. congruence. auto.
  erewrite Mem.astack_alloc. 2: eauto. apply Mem.astack_alloc in U. rewrite U.
  erewrite Genv.init_mem_astack; eauto. erewrite Genv.init_mem_astack; eauto. constructor.
>>>>>>> origin/StackAware-new
Qed.

Lemma transf_final_states:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, final_state R r2 /\ match_reply (cc_c inj) w r1 r2.
Proof.
  intros S R r1 MSTATE FINAL.
  inv FINAL. inv MSTATE. inv STACKS.
  eexists; split.
  - econstructor.
  - unfold cc_c; cbn. red.
    exists (injw j (Mem.support m) (Mem.support tm)).
    split; cbn.
    + inv H0. constructor; auto.
    + constructor; auto.
      cbn. constructor; auto.
Qed.

<<<<<<< HEAD
Lemma transf_external_states:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, at_external tge R q2 /\ match_query (cc_c inj) wx q1 q2 /\ match_senv (cc_c inj) wx se tse /\
  forall r1 r2 S', match_reply (cc_c inj) wx r1 r2 -> after_external S r1 S' ->
  exists R', after_external R r2 R' /\ match_states S' R'.
=======
Lemma transf_program_correct_1:
  forward_simulation (semantics fn_stack_requirements p) (semantics fn_stack_requirements tp).
>>>>>>> origin/StackAware-new
Proof.
  intros S R q1 MSTATE AT_EXT.
  inv AT_EXT. inv MSTATE.
  rewrite H in FUN. inv FUN.
  generalize (match_stacks_preserves_globals _ _ _ _ _ STACKS).
  intros PRES.
  generalize (find_function_inject _ _ _ _ PRES FUNINJ H).
  intros (FIND & KEPT1).
  eexists (injw j (Mem.support m) (Mem.support tm)), _. intuition idtac.  
  - econstructor; eauto.
  - econstructor; eauto. constructor. auto.
    intros EQ. subst vf. inv FUNINJ. inv H.
  - constructor.
    + eapply match_stacks_match_stbls; eauto.
    + eapply match_stacks_bound1; eauto.
    + eapply match_stacks_bound2; eauto.
  - destruct H0 as (wx' & Hwx' & H'). inv Hwx'. inv H1. inv H'. eexists. split.
    + econstructor; eauto.
    + inv H6. econstructor; eauto. cbn.
      apply match_stacks_incr_bound 
        with (Mem.support m) (Mem.support tm); auto.
      apply match_stacks_incr 
        with j (Mem.support m) (Mem.support tm); auto.
Qed.

End SOUNDNESS.

<<<<<<< HEAD
Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (cc_c inj) (cc_c inj) (semantics prog) (semantics tprog).
=======
Theorem transf_program_correct:
  forall p tp, match_prog p tp -> forward_simulation (semantics fn_stack_requirements p) (semantics fn_stack_requirements tp).
>>>>>>> origin/StackAware-new
Proof.
  intros MATCH.
  inv MATCH. destruct H as (VALID_USED & MATCH1).
  rename x into used.
  constructor.
  eapply Forward_simulation.
  - inv MATCH1. eauto.
  - intros se1 se2 wB GE COMPAT. inversion GE. rename inj_stbls_match into MSENV.
    assert (forall b : block,
               Genv.find_symbol se1 (prog_main (skel prog)) = Some b ->
               exists b' : block, Genv.find_symbol se2 (prog_main (tskel tprog)) = Some b')
      as MAIN_SYM_PRES.
    { 
      eapply main_symb_pres; eauto.
    }
    assert (forall (id : ident) (b : block),
               Genv.find_symbol se2 id = Some b ->
               exists b' : block, Genv.find_symbol se1 id = Some b')
      as SYMB_INCL.
    {
     eapply symb_incl; eauto.
    }
    assert (forall (b b' : block) (id : ident),
               Genv.find_symbol se1 id = Some b ->
               Genv.find_symbol se2 id = Some b' ->
               Genv.find_info se1 b = Genv.find_info se2 b')
      as INFO_EQ.
    {
      eapply info_eq; eauto.
    }
    assert (forall (id : positive) (gd : globdef unit unit) (b : block),
               (prog_defmap (skel prog)) ! id = Some gd ->
               Genv.find_symbol se2 id = Some b ->
               (prog_defmap (tskel tprog)) ! id = Some gd)
      as REMOVE_UNUSED_CONSISTENT.
    {
      eapply remove_unused_consistent; eauto.
    }
    assert (forall id,Genv.public_symbol se2 id = Genv.public_symbol se1 id) as
      PUBEQ.
    {
      inv GE. inv inj_stbls_match. eauto.
    }
    eapply forward_simulation_step
      with (match_states := match_states prog tprog used wB se1 se2).
    + intros q1 q2 QRY.
      destruct QRY. simpl in *.
      destruct vf1; try congruence; try (inv H; cbn; auto).
      unfold Genv.is_internal.
      destruct (Genv.invert_symbol se1 b) eqn:INV; try discriminate.
      * apply Genv.invert_find_symbol in INV as FIND.
        inversion MSENV. exploit mge_dom; eauto. eapply Genv.genv_symb_range; eauto.
        intros [b3 INJ']. rewrite H5 in INJ'. inv INJ'.
        rewrite Ptrofs.add_zero.
      
      unfold Genv.find_funct.
      unfold Genv.find_funct_ptr.
      destruct (Ptrofs.eq_dec i Ptrofs.zero); try congruence.
      rewrite !Genv.find_def_spec.
      eapply mge_symb in FIND as FIND'; eauto.
      apply Genv.find_invert_symbol in FIND' as INV'.
      rewrite INV. rewrite INV'.
      assert (REMOVE1: forall (id : positive) gd (b : block),
                             (prog_defmap (prog)) ! id = Some gd ->
                             Genv.find_symbol se2 id = Some b -> (prog_defmap ( tprog)) ! id = Some gd).
      eapply remove_unused_consistent_p; eauto.
      destruct ((prog_defmap prog) ! i0) eqn:F.
      exploit REMOVE1; eauto. intro F'. rewrite F'. reflexivity.
       inv MATCH1. rewrite match_prog_def0.
       destruct (IS.mem i0 used) eqn:MEM; eauto. rewrite F. eauto.
       erewrite inj_preserved in MEM; eauto. congruence.
      * unfold Genv.find_funct.
      unfold Genv.find_funct_ptr.
      rewrite ! Genv.find_def_spec.
      rewrite INV.
      assert (INV2: Genv.invert_symbol se2 b2 = None).
      {
        inv MSENV. destruct ( Genv.invert_symbol se2 b2) eqn: HH; eauto.
        apply Genv.invert_find_symbol in HH. eapply mge_symb in HH; eauto.
        apply Genv.find_invert_symbol in HH. congruence.
      }
      rewrite INV2.
      destruct (Ptrofs.eq_dec (Ptrofs.add i (Ptrofs.repr delta)) Ptrofs.zero);
      destruct ( Ptrofs.eq_dec i Ptrofs.zero); eauto.
    + intros q1 q2 s1 MQUERY INIT.
      eapply transf_initial_states with (se := se1) (tse := se2); eauto.
      
    + intros s1 s2 r1 MSTATE FINAL.
      eapply transf_final_states with (se := se1) (tse := se2); eauto.
    + intros s1 s2 q1 MSTATE ATEXT.
      eapply transf_external_states; eauto.
    + intros s1 t s1' STEP s2 MSTATE.
      unfold semantics; cbn in *.
      assert (exists s2', step (Genv.globalenv se2 tprog) s2 t s2' /\
                     match_states prog tprog used wB se1 se2 s1' s2') as GOAL.
      { 
        apply step_simulation with (w:=wB) (S1:=s1); auto.
      }
      destruct GOAL as (s2' & STEP' & MSTATE').
      exists s2'. split; auto.
  - apply well_founded_ltof.
Qed.

End ORACLE.
(** * Commutation with linking *)

Remark link_def_either:
  forall (gd1 gd2 gd: globdef fundef unit),
  link_def gd1 gd2 = Some gd -> gd = gd1 \/ gd = gd2.
Proof with (try discriminate).
  intros until gd.
Local Transparent Linker_def Linker_fundef Linker_varinit Linker_vardef Linker_unit.
  destruct gd1 as [f1|v1], gd2 as [f2|v2]...
(* Two fundefs *)
  destruct f1 as [f1|ef1], f2 as [f2|ef2]; simpl...
  destruct ef2; intuition congruence.
  destruct ef1; intuition congruence.
  destruct (external_function_eq ef1 ef2); intuition congruence.
(* Two vardefs *)
  simpl. unfold link_vardef. destruct v1 as [info1 init1 ro1 vo1], v2 as [info2 init2 ro2 vo2]; simpl.
  destruct (link_varinit init1 init2) as [init|] eqn:LI...
  destruct (eqb ro1 ro2) eqn:RO...
  destruct (eqb vo1 vo2) eqn:VO...
  simpl.
  destruct info1, info2.
  assert (EITHER: init = init1 \/ init = init2).
  { revert LI. unfold link_varinit.
    destruct (classify_init init1), (classify_init init2); intro EQ; inv EQ; auto.
    destruct (zeq sz (Z.max sz0 0 + 0)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto.
    destruct (zeq sz (init_data_list_size il)); inv H0; auto. }
  apply eqb_prop in RO. apply eqb_prop in VO.
  intro EQ; inv EQ. destruct EITHER; subst init; auto.
Qed.

Remark used_not_defined:
  forall p used id,
  valid_used_set p used ->
  (prog_defmap p)!id = None ->
  IS.mem id used = false \/ id = prog_main p.
Proof.
  intros. destruct (IS.mem id used) eqn:M; auto.
  exploit used_defined; eauto using IS.mem_2. intros [A|A]; auto.
  apply prog_defmap_dom in A. destruct A as [g E]; congruence.
Qed.

Remark used_not_defined_2:
  forall p used id,
  valid_used_set p used ->
  id <> prog_main p ->
  (prog_defmap p)!id = None ->
  ~IS.In id used.
Proof.
  intros. exploit used_not_defined; eauto. intros [A|A].
  red; intros; apply IS.mem_1 in H2; congruence.
  congruence.
Qed.

Lemma link_valid_used_set:
  forall p1 p2 p used1 used2,
  link p1 p2 = Some p ->
  valid_used_set p1 used1 ->
  valid_used_set p2 used2 ->
  valid_used_set p (IS.union used1 used2).
Proof.
  intros until used2; intros L V1 V2.
  destruct (link_prog_inv _ _ _ L) as (X & Y & Z).
  rewrite Z; clear Z; constructor.
- intros. rewrite ISF.union_iff in H. rewrite ISF.union_iff.
  rewrite prog_defmap_elements, PTree.gcombine in H0.
  destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
  destruct (prog_defmap p2)!id as [gd2|] eqn:GD2;
  simpl in H0; try discriminate.
+ (* common definition *)
  exploit Y; eauto. intros (PUB1 & PUB2 & _).
  exploit link_def_either; eauto. intros [EQ|EQ]; subst gd.
* left. eapply used_closed. eexact V1. eapply used_public. eexact V1. eauto. eauto. auto.
* right. eapply used_closed. eexact V2. eapply used_public. eexact V2. eauto. eauto. auto.
+ (* left definition *)
  inv H0. destruct (ISP.In_dec id used1).
* left; eapply used_closed; eauto.
* assert (IS.In id used2) by tauto.
  exploit used_defined. eexact V2. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  elim n. rewrite A, <- X. eapply used_main; eauto.
+ (* right definition *)
  inv H0. destruct (ISP.In_dec id used2).
* right; eapply used_closed; eauto.
* assert (IS.In id used1) by tauto.
  exploit used_defined. eexact V1. eauto. intros [A|A].
  exploit prog_defmap_dom; eauto. intros [g E]; congruence.
  elim n. rewrite A, X. eapply used_main; eauto.
+ (* no definition *)
  auto.
- simpl. rewrite ISF.union_iff; left; eapply used_main; eauto.
- simpl. intros id. rewrite in_app_iff, ISF.union_iff.
  intros [A|A]; [left|right]; eapply used_public; eauto.
- intros. rewrite ISF.union_iff in H.
  destruct (ident_eq id (prog_main p1)).
+ right; assumption.
+ assert (E: exists g, link_prog_merge (prog_defmap p1)!id (prog_defmap p2)!id = Some g).
  { destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
    destruct (prog_defmap p2)!id as [gd2|] eqn:GD2; simpl.
  * apply Y with id; auto.
  * exists gd1; auto.
  * exists gd2; auto.
  * eapply used_not_defined_2 in GD1; [ | eauto | congruence ].
    eapply used_not_defined_2 in GD2; [ | eauto | congruence ].
    tauto.
  }
  destruct E as [g LD].
  left. unfold prog_defs_names; simpl.
  change id with (fst (id, g)). apply in_map. apply PTree.elements_correct.
  rewrite PTree.gcombine; auto.
Qed.

Theorem link_match_program:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p ->
  match_prog p1 tp1 -> match_prog p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_prog p tp.
Proof.
  intros. destruct H0 as (used1 & A1 & B1). destruct H1 as (used2 & A2 & B2).
  destruct (link_prog_inv _ _ _ H) as (U & V & W).
  set (tp := {|
    prog_defs := PTree.elements (PTree.combine link_prog_merge (prog_defmap tp1) (prog_defmap tp2));
    prog_public := prog_public tp1 ++ prog_public tp2;
              prog_main := prog_main tp1 |}).
  assert (link tp1 tp2 = Some tp).
  { apply link_prog_succeeds.
  + rewrite (match_prog_main _ _ _ B1), (match_prog_main _ _ _ B2). auto.
  + intros.
  rewrite (match_prog_def _ _ _ B1) in H0.
  rewrite (match_prog_def _ _ _ B2) in H1.
  destruct (IS.mem id used1) eqn:U1; try discriminate;
  destruct (IS.mem id used2) eqn:U2; try discriminate.
  * edestruct V as (X & Y & gd & Z); eauto.
    split. rewrite (match_prog_public _ _ _ B1); auto.
    split. rewrite (match_prog_public _ _ _ B2); auto.
    congruence.
  * destruct (prog_defmap p2)!id eqn:F2; try discriminate.
    edestruct V as (X & Y & gd & Z); eauto.
    exfalso. inv A2. exploit used_public0; eauto.
    intro.
    apply IS.mem_1 in H2. congruence.
  * destruct (prog_defmap p1)!id eqn:F1; try discriminate.
    edestruct V as (X & Y & gd & Z); eauto.
    exfalso. inv A1. exploit used_public0; eauto.
    intro.
    apply IS.mem_1 in H2. congruence.
  * destruct (prog_defmap p1)!id eqn:F1; try discriminate.
    destruct (prog_defmap p2)!id eqn:F2; try discriminate.
    edestruct V as (X & Y & gd & Z); eauto.
    exfalso. inv A2. exploit used_public0; eauto.
    intro.
    apply IS.mem_1 in H2. congruence.
  }
  exists tp. split. auto.
  exists (IS.union used1 used2); split.
  + eapply link_valid_used_set; eauto.
  + rewrite W. constructor; simpl; intros.
    * eapply match_prog_main; eauto.
    * rewrite (match_prog_public _ _ _ B1), (match_prog_public _ _ _ B2). auto.
    * unfold tp. rewrite ! prog_defmap_elements, !PTree.gcombine by auto.
      rewrite (match_prog_def _ _ _ B1 id), (match_prog_def _ _ _ B2 id).
      rewrite ISF.union_b.
      {
        destruct (prog_defmap p1)!id as [gd1|] eqn:GD1;
          destruct (prog_defmap p2)!id as [gd2|] eqn:GD2.
        - (* both defined *)
          exploit V; eauto. intros (PUB1 & PUB2 & _).
          assert (EQ1: IS.mem id used1 = true) by (apply IS.mem_1; eapply used_public; eauto).
          assert (EQ2: IS.mem id used2 = true) by (apply IS.mem_1; eapply used_public; eauto).
          rewrite EQ1, EQ2; auto.
        - (* left defined *)
          exploit used_not_defined; eauto. intros [A|A].
          rewrite A, orb_false_r. destruct (IS.mem id used1); auto.
          replace (IS.mem id used1) with true. destruct (IS.mem id used2); auto.
          symmetry. apply IS.mem_1. rewrite A, <- U. eapply used_main; eauto.
        - (* right defined *)
          exploit used_not_defined. eexact A1. eauto. intros [A|A].
          rewrite A, orb_false_l. destruct (IS.mem id used2); auto.
          replace (IS.mem id used2) with true. destruct (IS.mem id used1); auto.
          symmetry. apply IS.mem_1. rewrite A, U. eapply used_main; eauto.
        - (* none defined *)
          destruct (IS.mem id used1), (IS.mem id used2); auto.
}
    * apply link_erase_program in H as SK.
      apply link_erase_program in H0 as SK0.
      inv B1. rewrite match_prog_skel0 in SK0.
      inv B2. rewrite match_prog_skel1 in SK0.
      rewrite SK in SK0. congruence.
Qed.

Global Instance TransfSelectionLink : TransfLink match_prog := link_match_program.
