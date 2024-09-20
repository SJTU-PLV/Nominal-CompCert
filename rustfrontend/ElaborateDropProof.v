Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import InitDomain InitAnalysis ElaborateDrop.
Require Import Rustlight Rustlightown RustIR RustOp.
Require Import RustIRsem RustIRown RustIRcfg.
Require Import Errors.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(* auxilary functions for own_env *)
Fixpoint collect_children_in (s: PathsMap.t) (l: list place) : Paths.t :=
  match l with
  | nil => Paths.empty
  | p :: l' =>            
      let id := local_of_place p in
      let ps := PathsMap.get id s in
      Paths.union (Paths.filter (fun elt => is_prefix p elt) ps) (collect_children_in s l')
  end.

Lemma collect_children_in_exists: forall l own p,
    Paths.In p (collect_children_in own l) ->
    exists p', In p' l /\ is_prefix p' p = true.
Proof.
  induction l; intros own p IN; simpl in *.
  exfalso. eapply Paths.empty_1. eauto.
  eapply Paths.union_1 in IN. destruct IN as [IN1|IN2].
  - eapply Paths.filter_2 in IN1. exists a. auto.
    red. solve_proper.
  - eapply IHl in IN2.
    destruct IN2 as (p' & IN1 & PRE).
    eauto.
Qed.

Lemma collect_children_in_implies: forall l p1 p2 own,
    In p1 l ->
    is_prefix p1 p2 = true ->
    Paths.In p2 (PathsMap.get (local_of_place p2) own) ->
    Paths.In p2 (collect_children_in own l).
Proof.
  induction l; intros p1 p2 own IN1 PRE IN2; simpl in *.
  contradiction.
  destruct IN1; subst.
  - eapply Paths.union_2.
    eapply Paths.filter_3. red. solve_proper.
    erewrite is_prefix_same_local; eauto.
    auto.
  - eapply Paths.union_3.
    eapply IHl; eauto.
Qed.

Definition remove_paths_in (s: PathsMap.t) (id: ident) (ps: Paths.t) :=
  let l := PathsMap.get id s in
  PathsMap.set id (Paths.diff l ps) s.

(* just update PathsMap *)
Fixpoint move_split_places_uncheck (own: PathsMap.t) (l: list (place * bool)) : PathsMap.t :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      move_split_places_uncheck (remove_place p own) l'
  end.

Fixpoint add_split_places_uncheck (universe: PathsMap.t) (uninit: PathsMap.t) (l: list (place * bool)) : PathsMap.t :=
  match l with
  | nil => uninit
  | (p,_) :: l' =>
      add_split_places_uncheck universe (add_place universe p uninit) l'
  end.

(* update Paths.t *)
Fixpoint filter_split_places_uncheck (own: Paths.t) (l: list (place * bool)) : Paths.t :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      filter_split_places_uncheck (Paths.filter (fun elt => negb (is_prefix p elt)) own) l'
  end.

Lemma filter_split_places_uncheck_more: forall l u1 u2,
    LPaths.ge u1 u2 ->
    LPaths.ge (filter_split_places_uncheck u1 l) (filter_split_places_uncheck u2 l).
Proof.
  induction l; simpl; auto.
  intros u1 u2 GE. destruct a.
  eapply IHl.
  red. red. intros a IN.
  eapply Paths.filter_3.
  red. solve_proper.
  eapply GE. eapply Paths.filter_1; eauto.
  red. solve_proper.
  eapply Paths.filter_2 in IN.
  auto.
  red. solve_proper.
Qed.

Lemma filter_split_places_uncheck_unchange: forall l p own,
    Paths.In p (filter_split_places_uncheck own l) ->
    Paths.In p own.
Proof.
  induction l; simpl; auto.
  intros p own IN. destruct a.
  eapply IHl. 
  eapply filter_split_places_uncheck_more; eauto.
  red. red.
  intros a IN1.
  eapply Paths.filter_1; eauto.
  red. solve_proper.
Qed.

  
Lemma move_split_places_uncheck_more: forall l u1 u2,
    PathsMap.ge u1 u2 ->
    PathsMap.ge (move_split_places_uncheck u1 l) (move_split_places_uncheck u2 l).
Proof.
  induction l; intros; simpl; auto.
  destruct a. eapply IHl.
  red. intros id.
  unfold remove_place.
  red. do 2 rewrite PathsMap.gsspec.
  destruct (peq id (local_of_place p)); subst.
  - red. intros a A.
    eapply Paths.filter_3. red. solve_proper.
    apply H.
    eapply Paths.filter_1; eauto. red. solve_proper.
    eapply Paths.filter_2 in A. auto.
    red. solve_proper.
  - eapply H.
Qed.
  
Lemma add_split_places_uncheck_more: forall l w u1 u2,
    PathsMap.ge u1 u2 ->
    PathsMap.ge (add_split_places_uncheck w u1 l) (add_split_places_uncheck w u2 l).
Proof.
  induction l; intros; simpl; auto.
  destruct a. eapply IHl.
  red. intros id.
  unfold add_place.
  red. do 2 rewrite PathsMap.gsspec.
  destruct (peq id (local_of_place p)); subst.
  - red. intros a A.
    eapply Paths.union_1 in A.
    destruct A.
    eapply Paths.union_2. eapply H. auto.
    eapply Paths.union_3. auto.
  - eapply H.
Qed.

Lemma move_split_places_uncheck_sound: forall drops own own',
    move_split_places own drops = own' ->
    PathsMap.ge (move_split_places_uncheck (own_init own) drops) (own_init own')
    /\ PathsMap.ge (add_split_places_uncheck (own_universe own) (own_uninit own) drops) (own_uninit own')
    /\ PathsMap.eq (own_universe own) (own_universe own').
Proof.
  induction drops; intros; subst; simpl.
  - split. apply PathsMap.ge_refl. eapply PathsMap.eq_refl.
    split. apply PathsMap.ge_refl. eapply PathsMap.eq_refl.
    apply PathsMap.eq_refl.
  - destruct a.
    destruct (is_owned own p) eqn: OWN.
    + exploit (IHdrops (move_place own p)); eauto.
    (* p is not owned, so remove it has no effect *)
    + exploit (IHdrops own); eauto.
      intros (A & B & C).
      split; try split. 3: auto.
      2: { eapply PathsMap.ge_trans; eauto.
           eapply add_split_places_uncheck_more.
           red. intros id. unfold add_place.
           red. rewrite PathsMap.gsspec.
           destruct (peq id (local_of_place p)); subst.
           + red. intros a D. eapply Paths.union_2. auto.
           + eapply LPaths.ge_refl. apply LPaths.eq_refl. }
      (* core proof *)
      eapply PathsMap.ge_trans; eauto.
      assert (CORE: PathsMap.ge (remove_place p (own_init own)) (own_init own)).
      { red. intros id. unfold remove_place. red.
        rewrite PathsMap.gsspec.
        destruct (peq id (local_of_place p)); subst.
        + red. intros a IN.
          eapply Paths.filter_3. red. solve_proper.
          auto.
          (* key to prove: a is not a child of p. From opposite side,
          if a is a children of p, then is_owned p = true. This can be
          proved by own_wf_init *)
          eapply negb_true_iff in OWN.
          apply Is_true_eq_true. apply Is_true_eq_left in OWN.           
          apply negb_prop_intro. apply negb_prop_elim in OWN.
          intro PRE. apply OWN. apply Is_true_eq_true in PRE.
          apply Is_true_eq_left.
          (* prove p is owned *)
          unfold is_owned. eapply Paths.for_all_1.
          red. solve_proper.
          red. intros p1 IN1. eapply Paths.filter_2 in IN1 as IN2.
          eapply Paths.filter_1 in IN1 as IN3.
          exploit (own_wf_init own (local_of_place p) a IN p1). auto.
          erewrite is_prefix_trans; eauto.
          red. solve_proper.
          red. solve_proper.          
        + eapply LPaths.ge_refl. apply LPaths.eq_refl. }
      eapply move_split_places_uncheck_more; eauto.
Qed.

  
(* equivalent (just ge for now because it is enough) between
get-filter-set and get-set-get-set ... -get-set mode *)
Lemma filter_move_split_places_ge: forall l id init
    (NAME: forall p b, In (p, b) l -> local_of_place p = id),
    PathsMap.ge (PathsMap.set id (filter_split_places_uncheck (PathsMap.get id init) l) init) (move_split_places_uncheck init l).
Proof.
  induction l; simpl; intros.
  red. intros p. red. rewrite PathsMap.gsspec.
  destruct (peq p id); subst. apply LPaths.ge_refl.
  apply LPaths.eq_refl.
  apply LPaths.ge_refl. apply LPaths.eq_refl.
  destruct a.
  generalize (IHl id (remove_place p init)).
  intros GE.
  eapply PathsMap.ge_trans.
  2: eauto.
  red. intros p1. red.
  do 2 rewrite PathsMap.gsspec.
  destruct (peq p1 id); subst.
  - eapply filter_split_places_uncheck_more.
    (* core of proof *)
    red. red. erewrite <- NAME; eauto.
    unfold remove_place.
    intros a IN. rewrite PathsMap.gsspec in IN.
    destruct (peq (local_of_place p) (local_of_place p)); try congruence.
  - red. unfold remove_place.
    intros a IN. rewrite PathsMap.gsspec in IN.
    destruct (peq p1 (local_of_place p)); subst.
    eapply Paths.filter_1; eauto. red. solve_proper.
    auto.
Qed.

Lemma filter_split_places_subset_collect_children: forall l p1 p2 own,
    Paths.In p1 (filter_split_places_uncheck own l) ->
    In p2 (map fst l) ->
    is_prefix p2 p1 = false.
Proof.
  induction l; simpl; intros p1 p2 own IN1 IN2.
  contradiction.
  destruct a. 
  destruct (split l) eqn: SPLIT. simpl in *.
  destruct IN2; subst.
  - eapply filter_split_places_uncheck_unchange in IN1.
    eapply Paths.filter_2 in IN1.
    eapply negb_true_iff; auto.
    red. solve_proper.
  - eapply IHl; eauto.
Qed.

(* analysis result and flag map types *)
Definition AN : Type := (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t).
Definition FM : Type := PTree.t (list (place * ident)).

Definition match_glob (ctx: composite_env) (gd tgd: globdef fundef type) : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar eq v1 v2
  | Gfun fd1, Gfun fd2 =>
      transf_fundef ctx fd1 = OK fd2
  | _, _ => False
  end.

(* We do not want to introduce link_order in match_states so we do not
use match_program_gen *)
Record match_prog (p tp: RustIR.program) : Prop :=
  {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_types:
    tp.(prog_types) = p.(prog_types);
    match_prog_def:
    forall id, Coqlib.option_rel (match_glob p.(prog_comp_env)) ((prog_defmap p)!id) ((prog_defmap tp)!id);
    match_prog_skel:
    erase_program tp = erase_program p;
  }.

Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  intros. unfold transl_program in H. monadInv H. unfold transform_partial_program in EQ.
  destruct p. simpl in *. unfold transform_partial_program2 in EQ. 
Admitted. 

(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: program.
Variable tp: program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Let ce := prog_comp_env p.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob ce) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob ce) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob ce)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None ))).
  (* adhoc generalize because types are the same *)
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None) at 1 3.
    generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None).
    induction Hd as [ | [id1 g1] l1 [id2 g2] l2 [Hi Hg] Hl IH]; cbn in *; eauto.
    intros t1 t2 Ht. eapply IH. eauto. rewrite Hi.
    eapply Genv.add_globdef_match; eauto.
  - unfold NMap.get. rewrite !NMap.gi. constructor.
Qed.

Theorem find_def_match:
  forall b tb delta g,
  Genv.find_def (Genv.globalenv se p) b = Some g ->
  j b = Some (tb, delta) ->
  exists tg,
  Genv.find_def (Genv.globalenv tse tp) tb = Some tg /\
  match_glob ce g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ transf_fundef ce f = OK tf.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v. inv H0.
  rewrite Genv.find_funct_find_funct_ptr in H. unfold Genv.find_funct_ptr in H.
  destruct Genv.find_def as [[|]|] eqn:Hf; try congruence. inv H.
  edestruct find_def_match as (tg & ? & ? & ?); eauto. subst.
  simpl in H0. destruct tg.
  rewrite Genv.find_funct_find_funct_ptr. unfold Genv.find_funct_ptr. rewrite H. eauto.
  contradiction.
Qed.


Theorem find_funct_none:
  forall v tv,
  Genv.find_funct (globalenv se p) v = None ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.find_funct (globalenv tse tp) tv = None.
Proof.
  intros v tv Hf1 INJ Hv. destruct INJ; auto; try congruence.
  destruct (Mem.sup_dec b1 se.(Genv.genv_sup)).
  - edestruct Genv.mge_dom; eauto. rewrite H1 in H. inv H.
    rewrite Ptrofs.add_zero. revert Hf1.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    generalize (Genv.mge_defs globalenvs_match b1 H1). intros REL. simpl.
    inv REL. auto.
    destruct x. congruence. simpl in H2.
    destruct y. contradiction. auto.    
  - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    destruct NMap.get as [[|]|] eqn:Hdef; auto. exfalso.
    apply Genv.genv_defs_range in Hdef.
    eapply Genv.mge_separated in H; eauto. cbn in *.
    apply n,H,Hdef.
Qed.

Theorem is_internal_match :
  (forall f tf, transf_fundef ce f = OK tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold fundef.
    simpl. rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.


(* Definitions used in match_cont and match_states *)

Inductive match_drop_place_state : option drop_place_state -> statement -> Prop :=
| match_dps_none:
  match_drop_place_state None Sskip
| match_dps_comp: forall p l,
    (* step_dropplace_init2 has simulated the drop flag condition
    checking *)
    match_drop_place_state (Some (drop_fully_owned_comp p l)) (Ssequence (Sdrop p) (makeseq (map (fun p => Sdrop p) l)))
| match_dps_box: forall l,
    match_drop_place_state (Some (drop_fully_owned_box l)) (makeseq (map (fun p => Sdrop p) l))
.

(* Because in dropplace state we do not know the pc, so we use own_env
to establish the relation between split drop places and target
statement. This relation should be proved when we enter Dropplace
state *)
Inductive match_split_drop_places flagm : own_env -> list (place * bool) -> statement -> Prop :=
| match_sdp_nil: forall own,
    match_split_drop_places flagm own nil Sskip
| match_sdp_cons_flag: forall p flag own l ts full
    (FLAG: get_dropflag_temp flagm p = Some flag)
    (SPLIT: match_split_drop_places flagm (if is_owned own p then move_place own p else own) l ts),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full (Some flag)) ts)
| match_sdp_cons_must_init: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_owned own p = true),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full None) ts)
| match_sdp_cons_must_uninit: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm own l ts)
    (OWN: is_owned own p = false),
    (* how to ensure that p is owned in own_env *)
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
.


(* Invariant of generate_drop_flags *)

Definition sound_flagm ce (body: statement) (cfg: rustcfg) (flagm: FM) (init uninit: PMap.t PathsMap.t) (universe: PathsMap.t) :=
  forall pc next p p1 sel drops,
    cfg ! pc = Some (Isel sel next) ->
    select_stmt body sel = Some (Sdrop p) ->
    split_drop_place ce (PathsMap.get (local_of_place p) universe) p (typeof_place p) = OK drops ->
    In p1 (map fst drops) ->
    get_dropflag_temp flagm p1 = None ->
    (* must owned *)
    (must_owned init!!pc uninit!!pc universe p1 = true \/
       (* must unowned *)
       may_owned init!!pc uninit!!pc universe p1 = false).

Lemma generate_drop_flags_inv: forall init uninit universe f cfg ce flags entry
  (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
  (GEN: generate_drop_flags init uninit universe ce f cfg = OK flags),
  sound_flagm ce f.(fn_body) cfg (generate_place_map flags) init uninit universe.
Admitted.


Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Hypothesis TRANSL: match_prog prog tprog.
Variable w: injp_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := globalenv tse tprog.
Let ce := ge.(genv_cenv).

Hypothesis GE: match_stbls injp w se tse.

Let match_stmt (ae: AN) (flagm: FM) := match_stmt get_init_info ae (elaborate_stmt flagm ce).


Lemma comp_env_preserved:
  genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. inv TRANSL. simpl in *.
  congruence.
Qed.

Lemma dropm_preserved:
  genv_dropm tge = genv_dropm ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. destruct TRANSL as [_ EQ]. simpl in EQ.
  unfold generate_dropm. simpl.
Admitted.


Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef ce fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. destruct x2. destruct p.
  monadInv EQ2.
  simpl; unfold type_of_function; simpl. auto.
Qed.



Record match_envs (j: meminj) (e: env) (m: mem) (lo hi: Mem.sup) (te: env) (tm: mem) (tlo thi: Mem.sup) : Type :=
  { me_vars: forall id b ty,
      e ! id = Some (b, ty) ->
      exists tb, te ! id = Some (tb, ty)
            /\ j b = Some (tb, 0);

    me_range: forall id b ty,
      e ! id = Some (b, ty) ->
      ~ In b lo /\ In b hi;
    
    me_trange: forall id b ty,
      te ! id = Some (b, ty) ->
      ~ In b tlo /\ In b thi;

    me_incr:
      Mem.sup_include lo hi;
    me_tincr:
      Mem.sup_include tlo thi;
    
    (* use out_of_reach to protect the drop flags *)
    me_protect: forall id b ty,
      e ! id = None ->
      te ! id = Some (b, ty) ->
      (* used in free_list *)
      Mem.range_perm tm b 0 (size_chunk Mint8unsigned) Cur Freeable
      /\ (forall ofs, loc_out_of_reach j m b ofs);  
  }.

(* relation between source env and target env including the own_env
and invariant of flags map. [(t)lo] is caller stack blocks and [t(hi)]
is callee stack blocks (including heap blocks), so [(t)lo] ⊆
[(t)[hi]] *)
Record match_envs_flagm (j: meminj) (own: own_env) (e: env) (m: mem) (lo hi: Mem.sup) (te: env) (flagm: FM) (tm: mem) (tlo thi: Mem.sup) : Type :=
  { me_wf_flagm: forall p id,
      get_dropflag_temp flagm p = Some id ->
      exists tb v, te ! id = Some (tb, type_bool)
              /\ e ! id = None
              /\ Mem.load Mint8unsigned tm tb 0 = Some (Vint v)
              (* TODO: add a rust bool_val *)
              /\ negb (Int.eq v Int.zero) = is_owned own p;
    
    me_envs: match_envs j e m lo hi te tm tlo thi;
  }.


(* empty env match *)
Lemma match_empty_envs: forall j m tm lo hi tlo thi,
    Mem.sup_include lo hi ->
    Mem.sup_include tlo thi ->
    match_envs j empty_env m lo hi empty_env tm tlo thi.
Proof.
  intros.
  constructor; intros.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  auto. auto.
  erewrite PTree.gempty in *. congruence.
Qed.
  
(** Properties of match_envs_flagm *)
Lemma match_envs_flagm_injp_acc: forall j1 j2 own le m1 m2 lo hi tle flagm tm1 tm2 tlo thi Hm1 Hm2,
    match_envs_flagm j1 own le m1 lo hi tle flagm tm1 tlo thi ->
    injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2) ->
    Mem.sup_include hi (Mem.support m1) ->
    Mem.sup_include thi (Mem.support tm1) ->
    match_envs_flagm j2 own le m2 lo hi tle flagm tm2 tlo thi.
Admitted.

Lemma match_envs_flagm_incr: forall j own le m lo hi1 hi2 tle flagm tm tlo thi1 thi2
   (MENV: match_envs_flagm j own le m lo hi1 tle flagm tm tlo thi1)
   (INCR: Mem.sup_include hi1 hi2)
   (TINCR: Mem.sup_include thi1 thi2),
    match_envs_flagm j own le m lo hi2 tle flagm tm tlo thi2.
Admitted.

Lemma match_envs_flagm_bound_unchanged: forall j own le m1 m2 lo hi tle flagm tm1 tm2 tlo thi ,
    match_envs_flagm j own le m1 lo hi tle flagm tm1 tlo thi ->
    Mem.unchanged_on (fun b _ => ~ In b hi) m1 m2 ->
    Mem.unchanged_on (fun b _ => ~ In b thi) tm1 tm2 ->
    match_envs_flagm j own le m2 lo hi tle flagm tm2 tlo thi.
Proof.
Admitted.

(* establish match_envs after the allocation of the drop flags in the
target programs *)
Lemma alloc_drop_flags_match: forall j1 m1 tm1 e1 lo hi te1 tlo thi flags Hm1
    (MENV: match_envs j1 e1 m1 lo hi te1 tm1 tlo thi)
    (SINCR: Mem.sup_include thi (Mem.support tm1))
    (TYS: forall id ty, In (id, ty) flags -> ty = type_bool)
    (DISJOINT: forall id ty, In (id, ty) flags -> e1 ! id = None),
  exists te2 tm2 Hm2,
    alloc_variables tge te1 tm1 flags te2 tm2
    /\ injp_acc (injpw j1 m1 tm1 Hm1) (injpw j1 m1 tm2 Hm2)
    (* wf_dropm *)
    /\ (forall id, In id (map fst flags) ->
             exists b, te2 ! id = Some (b, type_bool)
                  /\ e1 ! id = None)
    /\ match_envs j1 e1 m1 lo hi te2 tm2 tlo (Mem.support tm2).
Admitted.

(* allocate the same variables inject *)
Lemma alloc_variables_match: forall e1 te1 m1 tm1 vars e2 m2 lo hi tlo thi j1 Hm1
    (ALLOC: alloc_variables ge e1 m1 vars e2 m2)
    (MENV: match_envs j1 e1 m1 lo hi te1 tm1 tlo thi)
    (INCL: Mem.sup_include hi (Mem.support m1))
    (TINCL: Mem.sup_include thi (Mem.support tm1)),
  exists j2 tm2 Hm2 te2,
    alloc_variables tge te1 tm1 vars te2 tm2
    /\ match_envs j2 e2 m2 lo (Mem.support m2) te2 tm2 tlo (Mem.support tm2)
    /\ injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2).
Admitted.

Lemma alloc_variables_app: forall ce m1 m2 m3 l1 l2 e1 e2 e3,
    alloc_variables ce e1 m1 l1 e2 m2 ->
    alloc_variables ce e2 m2 l2 e3 m3 ->
    alloc_variables ce e1 m1 (l1 ++ l2) e3 m3.
Admitted.

Lemma bind_parameters_injp_acc: forall params e te m1 m2 vl j lo hi tlo thi tm1 Hm1
    (STORE: bind_parameters ge e m1 params vl m2)
    (MENV: match_envs j e m1 lo hi te tm1 tlo thi),
  exists tm2 Hm2,
    bind_parameters tge te tm1 params vl tm2
    /\ injp_acc (injpw j m1 tm1 Hm1) (injpw j m2 tm2 Hm2).
Admitted.

Inductive match_cont (j: meminj) : AN -> FM -> statement -> rustcfg -> cont -> RustIRsem.cont -> node -> option node -> option node -> node -> mem -> mem -> sup -> sup -> Prop :=
| match_Kseq: forall an flagm body cfg s ts k tk pc next cont brk nret m tm bound tbound
    (MSTMT: match_stmt an flagm body cfg s ts pc next cont brk nret)
    (MCONT: match_cont j an flagm body cfg k tk next cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kseq s k) (RustIRsem.Kseq ts tk) pc cont brk nret m tm bound tbound
| match_Kstop: forall an flagm body cfg nret m tm bound tbound
    (RET: cfg ! nret = Some Iend),
    match_cont j an flagm body cfg Kstop RustIRsem.Kstop nret None None nret m tm bound tbound
| match_Kloop: forall an flagm body cfg s ts k tk body_start loop_jump_node exit_loop nret contn brk m tm bound tbound
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an flagm body cfg s ts body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: match_cont j an flagm body cfg k tk exit_loop contn brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kloop s k) (RustIRsem.Kloop ts tk) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret m tm bound tbound
| match_Kcall: forall an flagm body cfg k tk nret f tf le tle own p m tm bound tbound
    (MSTK: match_stacks j (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) m tm bound tbound)
    (RET: cfg ! nret = Some Iend),
    (* in the end of a function. an and body are not important, those
    in match_stacks are important *)
    match_cont j an flagm body cfg (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) nret None None nret m tm bound tbound
| match_Kdropcall: forall an flagm body cfg k tk pc cont brk nret st membs b tb ofs tofs id m tm bound tbound
    (INJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (MCONT: match_cont j an flagm body cfg k tk pc cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kdropcall id (Vptr b ofs) st membs k) (RustIRsem.Kdropcall id (Vptr tb tofs) st membs tk) pc cont brk nret m tm bound tbound
| match_Kdropplace: forall f tf st l k tk e te own1 own2 flagm cfg nret cont brk pc ts1 ts2 m tm lo tlo hi thi maybeInit maybeUninit universe entry
    (** Do we need match_stacks here?  *)
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MSTK: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc cont brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (OWN: sound_own own2 maybeInit!!pc maybeUninit!!pc universe)
    (MOVESPLIT: move_split_places own1 l = own2),
    (* source program: from dropplace to droopstate, target: from
    state to dropstate. So Kdropplace matches Kcall *)
    match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg (Kdropplace f st l e own1 k) (RustIRsem.Kcall None tf te (RustIRsem.Kseq ts1 (RustIRsem.Kseq ts2 tk))) pc cont brk nret m tm hi thi

with match_stacks (j: meminj) : cont -> RustIRsem.cont -> mem -> mem -> sup -> sup -> Prop :=
| match_stacks_stop: forall m tm bound tbound,
    match_stacks j Kstop (RustIRsem.Kstop) m tm bound tbound
| match_stacks_call: forall flagm f tf nret cfg pc contn brk k tk own1 own2 p le tle m tm lo tlo hi thi maybeInit maybeUninit universe entry
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (* callee use stacks hi and thi, so caller f uses lo and tlo*)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc contn brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)                  
    (OWN: sound_own own2 maybeInit!!pc maybeUninit!!pc universe),
    match_stacks j (Kcall p f le own1 k) (RustIRsem.Kcall (Some p) tf tle (RustIRsem.Kseq (add_dropflag flagm p true) tk)) m tm hi thi
.

(** Properties of match_cont  *)

Lemma match_cont_injp_acc: forall j1 j2 an fm body cfg k tk pc cont brk nret m1 m2 tm1 tm2 lo tlo Hm1 Hm2,
    match_cont j1 an fm body cfg k tk pc cont brk nret m1 tm1 lo tlo ->
    injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2) ->
    Mem.sup_include lo (Mem.support m1) ->
    Mem.sup_include tlo (Mem.support tm1) ->
    match_cont j2 an fm body cfg k tk pc cont brk nret m2 tm2 lo tlo.
Admitted.

(* how to establish match_cont when modifying the drop flags in the
current stacks? We should use match_envs_flagm_unchanged to prove
it *)
Lemma match_cont_bound_unchanged: forall j an fm body cfg k tk pc cont brk nret m1 m2 tm1 tm2 lo tlo,
    match_cont j an fm body cfg k tk pc cont brk nret m1 tm1 lo tlo ->
    Mem.unchanged_on (fun b _ => ~ In b lo) m1 m2 ->
    Mem.unchanged_on (fun b _ => ~ In b tlo) tm1 tm2 ->
    match_cont j an fm body cfg k tk pc cont brk nret m2 tm2 lo tlo.
Proof.
Admitted.

Inductive match_states : state -> RustIRsem.state -> Prop := 
| match_regular_state:
  forall f s k e own m tf ts tk te tm j flagm maybeInit maybeUninit universe cfg nret cont brk next pc Hm lo tlo hi thi entry
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MSTMT: match_stmt (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg s ts pc next cont brk nret)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* well-formedness of the flag map *)
    (MENV: match_envs_flagm j own e m lo hi te flagm tm tlo thi)
    (* property of flagm when encounting drop statement *)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* Put sound_own here which may be inevitable due to the
    flow-insensitiveness of RustIR semantics.*)
    (SOUNDOWN: sound_own own maybeInit!!pc maybeUninit!!pc universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (State f s k e own m) (RustIRsem.State tf ts tk te tm)
| match_dropplace: forall f tf st l k tk e te own1 own2 m tm j flagm  maybeInit maybeUninit universe cfg nret cont brk next ts1 ts2 Hm lo tlo hi thi entry
    (AN: analyze ce f cfg entry= OK (maybeInit, maybeUninit, universe))
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* maybe difficult: transition of own is small step! *)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* small-step move_place to simulate big-step move_place in
    transfer. maybe difficult to prove *)
    (MOVESPLIT: move_split_places own1 l = own2)
    (OWN: sound_own own2 maybeInit!!next maybeUninit!!next universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (Dropplace f st l k e own1 m) (RustIRsem.State tf ts1 (RustIRsem.Kseq ts2 tk) te tm)
| match_dropstate: forall k tk m tm j flagm maybeInit maybeUninit universe body cfg nret cont brk next b ofs tb tofs st membs id lo tlo Hm
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm body cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (* no new stacks block in dropstate *)
    (BOUND: Mem.sup_include lo (Mem.support m))
    (TBOUND: Mem.sup_include tlo (Mem.support tm)),
    match_states (Dropstate id (Vptr b ofs) st membs k m) (RustIRsem.Dropstate id (Vptr tb tofs) st membs tk tm)
| match_callstate: forall j vf tvf m tm vargs tvargs k tk Hm
    (VINJ: Val.inject j vf tvf)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (AINJ: Val.inject_list j vargs tvargs)
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Callstate vf vargs k m) (RustIRsem.Callstate tvf tvargs tk tm)
| match_returnstate: forall j v tv m tm k tk Hm
    (VINJ: Val.inject j v tv)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Returnstate v k m) (RustIRsem.Returnstate tv tk tm)
. 

(** This property is difficult to prove! *)
Inductive wf_split_drop_places flagm (init uninit universe: PathsMap.t) : own_env -> list (place * bool) -> Prop :=
| wf_sdp_nil: forall own,
    wf_split_drop_places flagm init uninit universe own nil
| wf_sdp_flag: forall own b id l p
    (FLAG: get_dropflag_temp flagm p = Some id)
    (WF: wf_split_drop_places flagm init uninit universe (if is_owned own p then (move_place own p) else own) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
| wf_sdp_must: forall own b l p
    (FLAG: get_dropflag_temp flagm p = None)
    (OWN: must_owned init uninit universe p = is_owned own p)
    (WF: wf_split_drop_places flagm init uninit universe (if is_owned own p then (move_place own p) else own) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
.

Lemma move_place_still_not_owned: forall p1 p2 own,
    is_owned own p1 = false ->
    is_owned (move_place own p2) p1 = false.
  Admitted.

Lemma move_irrelavent_place_still_owned: forall p1 p2 own,
    is_owned own p1 = true ->
    is_prefix p2 p1 = false ->
    is_owned (move_place own p2) p1 = true.
Admitted.

(** IMPORTANT TODO  *)
Lemma ordered_split_drop_places_wf:
  forall drops own init uninit universe flagm
    (ORDER: split_places_ordered (map fst drops))
    (OWN: forall p full, In (p, full) drops ->
                    must_owned init uninit universe p = true ->
                    is_owned own p = true)
    (NOTOWN: forall p, must_owned init uninit universe p = false ->
                  may_owned init uninit universe p = false ->
                  is_owned own p = false)
    (UNI: PathsMap.eq universe (own_universe own))
    (FLAG: forall p full,
        In (p, full) drops ->
        get_dropflag_temp flagm p = None ->
        must_owned init uninit universe p = true
        \/ may_owned init uninit universe p = false),
    wf_split_drop_places flagm init uninit universe own drops.
Proof.
  induction drops; simpl; intros.
  constructor.
  destruct a.
  assert (A: wf_split_drop_places flagm init uninit universe
               (if is_owned own p then move_place own p else own) drops).
  { inv ORDER.
    eapply IHdrops. eauto.
    (* prove own *)
    + intros p1 full1 IN1 MUSTOWN1. 
      (* show that p1 is still owned after removing p which is not a
    pare nt of p1 from the own_env *)
      exploit OWN. right. eauto. auto. intros POWN1.
      destruct (is_owned own p) eqn: POWN; auto.
      eapply Forall_forall with (x:= p1) in H1; auto.
      (* use H1 POWN1 to prove this goal *)
      eapply move_irrelavent_place_still_owned; eauto.
      eapply in_map_iff. exists (p1, full1). auto.
    + intros p1 MUSTOWN1 MAYOWN1.
      exploit NOTOWN. eauto. eauto.
      intros NOTOWNP1.
      destruct (is_owned own p) eqn: POWN; auto.
      apply move_place_still_not_owned; auto.      
    + eapply PathsMap.eq_trans; eauto.
      unfold move_place. destruct (is_owned own p) eqn: POWN; apply PathsMap.eq_refl.
    + intros. eapply FLAG; eauto. }
  
  (* p has drop flag or not *)
  destruct (get_dropflag_temp flagm p) eqn: PFLAG.
  - econstructor; eauto.
  - exploit FLAG. left; eauto.
    auto. intros MOWN.
    eapply wf_sdp_must. eauto. 2: auto.
    destruct (must_owned init uninit universe p) eqn: MUSTOWN.
    + symmetry. eapply OWN; eauto.
    + destruct MOWN. congruence.
      symmetry. eapply NOTOWN.
      auto. auto.
Qed.      

    
Lemma elaborate_drop_match_drop_places:
  forall drops flagm own init uninit universe
    (** we need some restriction on drops!! *)
    (WFDROPS: wf_split_drop_places flagm init uninit universe own drops),
    match_split_drop_places flagm own drops (elaborate_drop_for_splits init uninit universe flagm drops).
Proof.
  induction drops; intros.
  econstructor.
  simpl. destruct a.
  destruct (get_dropflag_temp flagm p) eqn: FLAG.
  - econstructor. auto.
    eapply IHdrops. inv WFDROPS.
    auto. congruence.
  - inv WFDROPS. congruence.
    destruct (must_owned init uninit universe p) eqn: MUST.
    (* must_owned = true *)
    + rewrite <- OWN in WF.
      econstructor; auto.      
    (* must_owned = false *)
    + rewrite <- OWN in WF.
      econstructor; auto.
Qed.

Lemma deref_loc_inject: forall ty m b ofs v tm j tb tofs,
    deref_loc ty m b ofs v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr tb tofs) ->
    exists tv, deref_loc ty tm tb tofs tv /\ Val.inject j v tv.
Proof.
    intros. inv H. 
    - (*by value*)
      exploit Mem.loadv_inject; eauto. intros [tv [A B]].
      exists tv. split. econstructor. 
      instantiate (1:= chunk). 
      destruct ty; simpl in *; congruence.
      auto. auto.
    - (* by ref*)
      exists ((Vptr tb tofs)). split. 
      eapply deref_loc_reference. 
      destruct ty; simpl in *; congruence.
      auto. 
    - (*by copy*)
      exists (Vptr tb tofs). split. eapply deref_loc_copy.
      destruct ty; simpl in *; congruence.
      auto.
  Qed. 

Lemma eval_place_inject: forall le tle m tm p b ofs j own lo hi tlo thi flagm,
    eval_place ge le m p b ofs ->
    Mem.inject j m tm ->
    match_envs_flagm j own le m lo hi tle flagm tm tlo thi ->
    exists b' ofs', eval_place tge tle tm p b' ofs' /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Proof. 
  induction 1; intros. 
  - exploit me_vars; eauto. eapply me_envs; eauto.
    intros (tb & TE & J). eexists. eexists. split. eapply eval_Plocal; eauto. 
    eapply Val.inject_ptr; eauto.
  - exploit IHeval_place; eauto. intros (b' & ofs' & EV & INJ).  
    rewrite comp_env_preserved in *. 
    inv INJ. eexists. eexists. split. econstructor; eauto.
    eapply Val.inject_ptr; eauto.  
    repeat rewrite Ptrofs.add_assoc. f_equal.  
    rewrite Ptrofs.add_commut. eauto. 
  - exploit IHeval_place; eauto. intros (b' & ofs' & EV & INJ). 
    exploit Mem.loadv_inject; eauto. intros [v' [A B]]. inv B.
    rewrite comp_env_preserved in *. 
    eexists. eexists. split. econstructor; eauto. 
    inv INJ. econstructor; eauto. 
    repeat rewrite Ptrofs.add_assoc. f_equal.  
    rewrite Ptrofs.add_commut. eauto. 
  - exploit IHeval_place; eauto. 
    intros (b' & ofs'0 & EV & INJ). 
    exploit deref_loc_inject; eauto. intros [v' [A B]]. inv B. 
    eexists. eexists. split. econstructor; eauto. econstructor; eauto. 
Qed. 

Lemma deref_loc_rec_inject: forall j m tm b ofs tb tofs tyl v,
    deref_loc_rec m b ofs tyl v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr tb tofs) ->
    exists tv, deref_loc_rec tm tb tofs tyl tv /\ Val.inject j v tv.
Proof. 
  induction 1. 
  - intros. eexists. split. econstructor. auto. 
  - intros A B. exploit IHderef_loc_rec; eauto. intros (tv & C & D).
    inv D. exploit deref_loc_inject; eauto. intros (tv' & E & F). 
    eexists. split. econstructor; eauto. auto.
Qed. 
  
Lemma drop_box_rec_injp_acc: forall m1 m2 tm1 j Hm b ofs tb tofs tyl ge tge
        (DROP: drop_box_rec ge b ofs m1 tyl m2)
        (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)),
      exists tj tm2 tHm,
        drop_box_rec tge tb tofs tm1 tyl tm2
        /\ injp_acc (injpw j m1 tm1 Hm) (injpw tj m2 tm2 tHm).
Proof. 
  
Admitted. 



Lemma eval_pexpr_inject:
  forall e le m v tm tle own lo hi flagm tlo thi j
    (EVAL: eval_pexpr ge le m e v)
    (MINJ: Mem.inject j m tm)
    (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
    exists tv, eval_pexpr tge tle tm e tv /\ Val.inject j v tv.
Proof. 
  induction 1; intros. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - exploit IHEVAL; eauto. intros (tv & A & B).
    exploit Cop.sem_unary_operation_inject; eauto. intros (tv' & C & D). 
    eexists. split. 
    econstructor; eauto. eauto. 
  - exploit IHEVAL1; eauto. intros (tv1 & A1 & B1).
    exploit IHEVAL2; eauto. intros (tv2 & A2 & B2).
    exploit Cop.sem_binary_operation_rust_inject; eauto. intros (tv' & C & D). 
    eexists. split. 
    econstructor; eauto. unfold Cop.sem_binary_operation_rust. 
    destruct op; eauto.
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    exploit deref_loc_inject; eauto. intros (tv & TDEREF & VINJ).
    eexists. split. econstructor; eauto. auto. 
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    inv INJ. exploit Mem.loadv_inject; eauto. intros (tv & A & B). inv B. 
    eexists. split. econstructor; eauto. 
    rewrite comp_env_preserved; auto. 
    destruct (Int.eq tag (Int.repr tagz)); simpl; econstructor. 
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    eexists. split. econstructor; eauto. auto.
Qed. 


Lemma eval_expr_inject: forall e le m v tm tle own lo hi flagm tlo thi j
        (EVAL: eval_expr ge le m e v)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tv, eval_expr tge tle tm e tv /\ Val.inject j v tv.
Proof. 
  destruct e; intros. 
  - inv EVAL. inv H2. exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ). 
    exploit deref_loc_inject; eauto. intros (tv & TDEREF & VINJ). 
    eexists. split. econstructor. eapply eval_Eplace; eauto. eauto. 
  - inv EVAL. exploit eval_pexpr_inject; eauto. intros (tv & A & B). 
    eexists. split. econstructor. eauto. auto. 
Qed.

Lemma eval_exprlist_inject: forall le m args vl tm tle own lo hi flagm tlo thi j tyl
        (EVAL: eval_exprlist ge le m args tyl vl)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tvl, eval_exprlist tge tle tm args tyl tvl /\ Val.inject_list j vl tvl.
Admitted.


Lemma type_to_drop_member_state_eq: forall id ty,
    type_to_drop_member_state ge id ty = type_to_drop_member_state tge id ty.
Proof.
  intros. unfold type_to_drop_member_state.
  erewrite comp_env_preserved; eauto. auto.
  erewrite dropm_preserved; eauto.
Qed.

(** IMPORTANT TODO *)
Lemma eval_dropflag_match: forall j own1 own2 le tle lo hi tlo thi flagm m tm1 Hm1 (flag: bool) p tk tf
  (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm1 tlo thi)
  (OWN: own2 = if flag then init_place own1 p else move_place own1 p),
  exists tm2 Hm2, plus RustIRsem.step tge (RustIRsem.State tf (add_dropflag flagm p flag) tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)         
         /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
         /\ injp_acc (injpw j m tm1 Hm1) (injpw j m tm2 Hm2).
Admitted.

(* only consider move_place *)
Lemma eval_dropflag_list_match: forall al j own1 own2 le tle lo hi tlo thi flagm m tm1 Hm1 tk tf
    (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm1 tlo thi)
    (OWN: own2 = own_transfer_exprlist own1 al),
    exists tm2 Hm2, plus RustIRsem.step tge (RustIRsem.State tf (add_dropflag_list flagm (moved_place_list al) false) tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)
               /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
               /\ injp_acc (injpw j m tm1 Hm1) (injpw j m tm2 Hm2) .
Admitted.

(** IMPORTANT TODO  *)
Lemma generate_flag_map_sound: forall mayinitMap mayuninitMap universe ce f cfg flags
    (GEN: generate_drop_flags mayinitMap mayuninitMap universe ce f cfg = OK flags),
    sound_flagm ce f.(fn_body) cfg (generate_place_map flags) mayinitMap mayuninitMap universe.
Admitted.

  
(* difficult part is establish simulation (match_split_drop_places)
when entering dropplace state *)
Lemma step_dropplace_simulation:
  forall S1 t S2, step_dropplace ge S1 t S2 ->
   forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropplace_init1 *)
  - inv MDPS.
    (** Two cases of skipping this drop: one is must uninit and the
    other is drop flag is false *)
    inv MSPLIT.
    (* there is drop flag and the value of drop flag is false *)
    + exploit me_wf_flagm; eauto.
      intros (tb & v & TE & LOAD & ISOWN).
      simpl.
      eexists. split.
      (* step in target *)
      * admit.
      * admit.
    + congruence.
    (* no drop flag, must_unowned *)
    + eexists. split.
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      eapply star_refl. auto. auto.
      (* match_states *)
      econstructor; eauto.
      econstructor; eauto.
      simpl in OWN.
      rewrite NOTOWN in OWN. auto.
  (* step_dropplace_init2 *)
  - inv MDPS. inv MSPLIT.
    (* there is a drop flag *)
    + exploit me_wf_flagm; eauto.
      intros (tb & v & TE  & LOAD & ISOWN & OUTREACH).
      simpl.
      eexists. split.
      (* step in target *)
      * admit.
      * admit.
    (* must_owned *)
    + eexists. split.
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      eapply star_refl. 1-2: eauto.
      (* match_states *)
      econstructor; eauto.
      (** TODO: match_drop_place_state and gen_drop_place_state *)
      admit.
      (** TODO: move out a place which does not have drop flag has no
      effect on match_envs_flagm *)
      admit.
      simpl in OWN0.
      rewrite OWN1 in OWN0. auto.
    + congruence.
  (* step_dropplace_box *)
  - inv MDPS. simpl.
    (* hypotheses of step_drop_box *)
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    exploit deref_loc_inject; eauto.
    intros (tv & TDEREF & VINJ2). inv VINJ2.
    exploit extcall_free_injp; eauto.
    instantiate (1 := Hm). instantiate (1 := tge).
    intros (tm1 & Hm1 & TFREE & MINJ1).
    eexists. split.
    (* step *)
    econstructor. econstructor.
    (* step_drop_box *)
    eapply star_step. eapply RustIRsem.step_drop_box; eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_refl.
    1-3: eauto.
    (* match_states *)
    eapply match_dropplace with (hi:=hi) (thi:=thi).
    eauto. eauto.
    (* match_cont_injp_acc *)
    eapply match_cont_injp_acc. eapply MCONT.
    eauto.
    eapply Mem.sup_include_trans. eapply me_incr; eapply me_envs; eauto. auto.
    eapply Mem.sup_include_trans. eapply me_tincr; eapply me_envs; eauto. auto.
    (* match_drop_place_state *)
    econstructor.
    eauto. etransitivity; eauto.
    (* match_envs_flagm *)
    eapply match_envs_flagm_injp_acc; eauto.
    auto. eauto. auto.
    (* sup include *)
    inv MINJ1. inv H10. inv H11.
    eapply Mem.sup_include_trans; eauto.
    inv MINJ1. inv H10. inv H11.
    eapply Mem.sup_include_trans; eauto.
  (* step_dropplace_struct *)
  - inv MDPS.
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    eexists. split.
    (* step_drop_struct *)
    econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_drop_struct; eauto.
    erewrite comp_env_preserved; eauto.
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    econstructor; eauto.
    econstructor; eauto.
    (* match_drop_place_state *)
    econstructor.
  (* step_dropplace_enum *)
  - inv MDPS.
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    (* load tag inject *)
    inv VINJ1.
    exploit Mem.load_inject; eauto.
    intros (v2 & TLOAD & VINJ2). inv VINJ2.
    eexists. split.
    (* step_drop_struct *)
    econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_drop_enum; eauto.
    erewrite comp_env_preserved; eauto.
    (* use address_inject due with overflow *)
    assert (PERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty).
    { exploit Mem.load_valid_access. eapply TAG.
      intros (A & B). eapply Mem.perm_implies.
      eapply A. simpl. lia. econstructor. }
    simpl. exploit Mem.address_inject; eauto.
    intros A. rewrite A. auto.    
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    rewrite type_to_drop_member_state_eq.
    econstructor; eauto.
    (* match_cont *)
    econstructor; eauto.
    (* match_drop_place_state *)
    econstructor.
  (* step_dropplace_next *)
  - admit.
  (* step_dropplace_return *)
  - admit.
Admitted.

(** REMOVE IT: This lemma is impossible to prove: because the
semantics is flow-insensitive so that we do not know whether or not s
in match_stmt locates in the same branch as the s in tr_stmt. So pc1 =
pc2 is impossible. *)
Lemma match_stmt_cont_unique: forall k tk an fm body cfg s ts pc1 next1 cont1 brk1 nret j m tm lo tlo pc2 next2 cont2 brk2,
    match_stmt an fm body cfg s ts pc1 next1 cont1 brk1 nret ->
    match_cont j an fm body cfg k tk next1 cont1 brk1 nret m tm lo tlo ->
    tr_stmt body cfg s pc2 next2 cont2 brk2 nret ->
    tr_cont body cfg k next2 cont2 brk2 nret ->
    pc1 = pc2 /\ next1 = next2 /\ cont1 = cont2 /\ brk1 = brk2.
Proof.
  induction k; intros until brk2; intros MSTMT MCONT TRSTMT TRCONT.
  (* Sskip *)
  - inv MCONT. inv TRCONT.
    (* how to prove pc1 = pc2: match_stmt and tr_stmt with same next
    node have the same pc *)
    admit.
  (* Kseq *)
  - inv MCONT. inv TRCONT.
    assert (MSTMT1: match_stmt an fm body cfg (Ssequence s0 s) (Ssequence ts ts0) pc1 next cont1 brk1 nret).
    { econstructor; eauto. }
    assert (TRSTMT1: tr_stmt body cfg (Ssequence s0 s) pc2 next0 cont2 brk2 nret).
    { econstructor; eauto. }
    exploit IHk.
    eapply MSTMT1. eauto.
    eapply TRSTMT1. eauto. intros (A & B & C & D).
    subst.
    repeat split; eauto.
    (* how to prove pc1 = pc2: match_stmt and tr_stmt with same next
    node have the same pc *)
    admit.
Abort.

Lemma step_dropstate_simulation:
  forall S1 t S2, step_drop ge S1 t S2 ->
   forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropstate_init *)
  - eexists. split.
    econstructor. econstructor.
    eapply RustIRsem.step_dropstate_init.
    eapply star_refl.
    auto.
    erewrite type_to_drop_member_state_eq; eauto.
    econstructor; eauto.
  (* step_dropstate_struct *)
  - inv VINJ.
    exploit deref_loc_rec_inject; eauto.
    intros (tv & DEREF1 & VINJ1). inv VINJ1.
    erewrite <- comp_env_preserved in *; eauto.
    eexists. split.
    econstructor. econstructor. econstructor; eauto.
    replace (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr delta)) (Ptrofs.repr fofs)) with (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr fofs)) (Ptrofs.repr delta)).
    eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    eapply star_refl.
    auto.
    (* match_states *)
    econstructor. econstructor.
    econstructor; eauto.
    eauto. eauto.
    econstructor; eauto.
    auto. auto.
  (* step_dropstate_enum *)
  - admit.
  (* step_dropstate_box *)
  - inv VINJ.
    exploit (drop_box_rec_injp_acc m m' tm); eauto.
    instantiate (1:= Hm). instantiate (1 := tge).
    intros (tj & tm2 & tHm & TDROP & INJP1).
    erewrite <- comp_env_preserved in *; eauto.
    eexists. split.
    (* step *)
    econstructor. econstructor. econstructor; eauto.
    replace (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta)) (Ptrofs.repr fofs)) with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr fofs)) (Ptrofs.repr delta)).
    eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    eapply star_refl.
    auto.
    (* match_states *)
    generalize INJP1. intros INJP2.
    inv INJP2.
    assert (BOUND1: Mem.sup_include lo (Mem.support m')).
    eapply Mem.sup_include_trans. eauto.
    eapply Mem.unchanged_on_support; eauto.
    assert (TBOUND1: Mem.sup_include tlo (Mem.support tm2)).
    eapply Mem.sup_include_trans. eauto.
    eapply Mem.unchanged_on_support; eauto.
    (* match_cont_injp_acc *)
    exploit match_cont_injp_acc; eauto.
    intros MCONT1.        
    econstructor; eauto.
    etransitivity. eauto. eauto.
  (* step_dropstate_return1 *)
  - inv MCONT.
    eexists. split.
    econstructor. econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropstate_return2 *)
  - inv MCONT.
    eexists. split.
    econstructor. econstructor. econstructor.
    eapply star_refl.
    eauto.
    (* match_states *)
    econstructor; eauto.
Admitted.

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 -> forall S1' (MS: match_states S1 S1'),
    exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof. 
  induction 1; intros; inv MS.
  (* step_assign *)
  - inv MSTMT.
    simpl in TR. 
    admit.
  (* step_assign_variant *)
  - admit.
  (* step_box *)
  - admit.
  (* step_to_dropplace *)
  - inv MSTMT. simpl in TR.
    unfold elaborate_drop_for in TR.
    (** sound_own property *)
    assert (UNIEQ: PathsMap.eq (own_universe own) universe0) by admit.
    erewrite split_drop_place_eq_universe in TR.
    unfold ce in TR. erewrite SPLIT in TR.
    2: { symmetry. eapply UNIEQ. }
    inv TR.
    (* end of getting ts *)
    (* how to prevent stuttering? *)
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. eauto.
    (* match_states *)
    econstructor; eauto.
    econstructor.
    (* match_split_drop_places *)
    eapply elaborate_drop_match_drop_places.
    (** IMPORTANT TODO: wf_split_drop_places *)
    
    eapply ordered_split_drop_places_wf.
    eapply split_ordered. eapply split_drop_place_meet_spec; eauto.
    (* use sound_own properties *)
    intros. eapply must_owned_sound; eauto.
    intros. eapply must_not_owned_sound; eauto.
    eapply sound_own_universe; eauto.
    intros. eapply SFLAGM; eauto.
    erewrite split_drop_place_eq_universe; eauto.
    eapply sound_own_universe; eauto.
    eapply in_map_iff. exists (p0, full). auto.
    
    (** sound_own: this proof is important. Make it a lemma!  *)
    assert (SOWN: sound_own (move_split_places own drops) (remove_place p maybeInit!!pc) (add_place universe0 p maybeUninit!!pc) universe0). 
    { exploit split_drop_place_meet_spec; eauto.
      intros SPLIT_SPEC.
      exploit (move_split_places_uncheck_sound drops own); eauto.
      intros (INITGE & UNINITGE & UNIEQ1).      
      constructor.
      + (* step1 *)
        assert (STEP1: PathsMap.ge (move_split_places_uncheck own.(own_init) drops) (own_init (move_split_places own drops))) by auto.
        eapply PathsMap.ge_trans. 2: eapply STEP1.
        (* step2: one-time remove and recursively remove *)
        assert (STEP2: PathsMap.ge (remove_paths_in own.(own_init) (local_of_place p) (collect_children_in own.(own_init)  (map fst drops))) (move_split_places_uncheck (own_init own) drops)).
        { red. intros id.
          unfold remove_paths_in.
          (* reduce the steps of PathsMap.set in move_split_places_uncheck *)
          assert (A: PathsMap.ge (PathsMap.set (local_of_place p) (filter_split_places_uncheck (PathsMap.get (local_of_place p) (own_init own)) drops) (own_init own)) (move_split_places_uncheck (own_init own) drops)).
          { (* require that all places in drops are children of p *)
            eapply filter_move_split_places_ge.
            intros. symmetry. eapply is_prefix_same_local.
            eapply split_sound; eauto. eapply in_map_iff. exists (p0,b). auto. }
          eapply LPaths.ge_trans.
          2 : eapply A.
          assert (CORE: LPaths.ge (Paths.diff (PathsMap.get (local_of_place p) (own_init own))
                                     (collect_children_in (own_init own)  (map fst drops)))
                          (filter_split_places_uncheck (PathsMap.get (local_of_place p) (own_init own)) drops)).
          { (* any place in filter_split_places_uncheck is not a child of any place in drops (can be proved by induction), so this place is not in the collect_children_in. *)
            red. red. intros a IN.
            eapply Paths.diff_3.
            eapply filter_split_places_uncheck_unchange; eauto.
            (* prove by contradiction *)
            intros IN1.
            exploit collect_children_in_exists; eauto.
            intros (p' & IN' & PRE).                      
            exploit (filter_split_places_subset_collect_children drops a p'); eauto.
            
            intros. congruence. }
          (* unable to use setoid_rewrite *)
          red. do 2 rewrite PathsMap.gsspec.
          destruct (peq id (local_of_place p)); subst. auto.
          apply LPaths.ge_refl. apply LPaths.eq_refl.
        }
        
        eapply PathsMap.ge_trans. 2: eapply STEP2.
      (* step3 *)
      { red. intros id. unfold remove_paths_in, remove_place.
        assert (CORE: LPaths.ge (Paths.filter (fun elt : Paths.elt => negb (is_prefix p elt))
             (PathsMap.get (local_of_place p) maybeInit !! pc)) (Paths.diff (PathsMap.get (local_of_place p) (own_init own)) (collect_children_in (own_init own) (map fst drops))) ).
        { red. red. intros a.
          intros IN.
          eapply Paths.diff_1 in IN as IN1.
          eapply Paths.diff_2 in IN as IN2.
          eapply Paths.filter_3. red. solve_proper.
          eapply sound_own_init; eauto.
          (* key of proof: [a] is not a children of p *)
          apply Is_true_eq_true. apply negb_prop_intro.
          red. intros ISPRE. eapply IN2. clear IN2.
          eapply Is_true_eq_true in ISPRE.
          (** TODO: show that a is in the universe and use
          split_drop_complete to show a ∈ drops *)
          eapply Paths.union_2 in IN1.
          eapply own_consistent in IN1; eauto.
          exploit split_complete; eauto. intros IN2.
          eapply collect_children_in_implies. eauto.
          apply is_prefix_refl.
          eapply Paths.diff_1. erewrite <- is_prefix_same_local; eauto. }
        red. do 2 rewrite PathsMap.gsspec.
        destruct (peq id (local_of_place p)); subst. auto.
        eapply sound_own_init; eauto. }
      (* uninit part: maybe easy? because there are less places to be
      added in own_env side *)
      + admit.
      (* universe equal *)
      + eapply PathsMap.eq_trans; eauto. eapply sound_own_universe; eauto. }
    (* use analyze_succ *)
    exploit analyze_succ; eauto. simpl. eauto.
    instantiate (1 := (move_split_places own drops)).
    unfold transfer. rewrite SEL. rewrite STMT. auto.
    intros (mayinit3 & mayuninit3 & A & B & C). subst.
    auto.
  (* step_in_dropplace *)
  - eapply step_dropplace_simulation. eauto.
    econstructor; eauto.
  (* step_dropstate *)
  - eapply step_dropstate_simulation. eauto.
    econstructor; eauto.
  (* step_storagelive *)
  - admit.
  (* step_storagedead *)
  - admit.
  (* step_call *)
  - (* evaluate drop flag list of arguments *)
    exploit eval_dropflag_list_match; eauto.
    instantiate (1 := Hm). instantiate (1:= al).
    instantiate (2 := tf).
    intros (tm1 & Hm1 & EVAL1 & MENV1 & MINJ1).
    exploit eval_expr_inject; eauto.
    intros (tv & TEXPR & VINJ1).
    exploit eval_exprlist_inject; eauto.
    intros (tvl & TARGS & VINJ2).
    assert (GE1: Genv.match_stbls j se tse).
    { replace j with (mi injp (injpw j m tm Hm)) by auto.
      eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. }
    exploit find_funct_match; eauto.
    intros (tf1 & FINDFUN1 & TRANSF).
    inv MSTMT. simpl in TR. inv TR.
    (* match_cont injp_acc *)
    exploit match_cont_injp_acc. eauto.
    eauto.
    eapply Mem.sup_include_trans.
    eapply me_incr. eapply me_envs. eauto. auto.
    eapply Mem.sup_include_trans.
    eapply me_tincr. eapply me_envs. eauto. auto.
    intros MCONT1.    
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_step. econstructor.
    eapply plus_star. eapply plus_trans.
    eapply EVAL1.
    econstructor. eapply RustIRsem.step_skip_seq.
    eapply star_step.
    (* eval function call *)
    econstructor; eauto.
    erewrite type_of_fundef_preserved; eauto.
    (** TODO: add good_function in RustIRown *)
    admit.
    eapply star_refl.
    1-5: eauto.
    (* match_states *)
    econstructor; eauto.
    etransitivity; eauto.
    (* match_stacks *)
    econstructor; eauto.
    (* match_envs_flagm *)
    eapply match_envs_flagm_incr. eapply MENV1.
    auto.
    inv MINJ1. eapply Mem.sup_include_trans.
    eauto. eapply Mem.unchanged_on_support. eauto.
    (** sound_own *)
    exploit analyze_succ; eauto.
    simpl. eauto.
    instantiate (1 := (init_place (own_transfer_exprlist own1 al) p)).
    2: { intros (mayinit3 & mayuninit3 & A & B & C). subst. auto. }
    unfold transfer. rewrite SEL.
    rewrite STMT.
    (** IMPORTANT TODO: sound_own in call *)
    admit.
  (** DIFFICULT: step_internal_function *)
  - simpl in  FIND.
    assert (GE1: Genv.match_stbls j se tse).
    { replace j with (mi injp (injpw j m tm Hm)) by auto.
      eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. }    
    exploit find_funct_match; eauto.
    intros (tf & TFIND & TRFUN).
    (* destruct tf *)
    unfold transf_fundef in TRFUN.
    monadInv TRFUN. unfold transf_function in EQ.
    monadInv EQ. destruct x2 as [[mayinitMap mayuninitMap] universe].
    monadInv EQ2.
    (* use transl_on_cfg_meet_spec to get match_stmt in fuction entry *)
    exploit (@transl_on_cfg_meet_spec AN); eauto.
    intros (nret & MSTMT).
    (* own_env in function entry is sound *)
    exploit sound_function_entry. simpl. eauto.
    eauto. eauto. intros OWNENTRY.        
    (** TODO: construct function entry in target program *)
    inv ENTRY.
    (* alloc the same variables and parameters in source and target *)
    exploit alloc_variables_match; eauto.
    eapply match_empty_envs.
    eapply Mem.sup_include_refl.
    instantiate (1 := tm). eapply Mem.sup_include_refl.
    instantiate (1 := Hm).
    intros (j1 & tm1 & Hm1 & te1 & ALLOC1 & MENV1 & INJP1).
    (* alloc drop flag in the target program *)
    set (flags := combine (map snd x2) (repeat type_bool (Datatypes.length x2))) in *.
    exploit alloc_drop_flags_match; eauto.    
    instantiate (1 := flags).
    (* easy: all types of drop flag is bool *)
    admit.
    (* easy: added a norepet check in target program to ensure that
    source env does not contains identities of drop flags *)
    admit.
    instantiate (1 := Hm1).
    intros (te2 & tm2 & Hm2 & ALLOC2 & INJP2 & WFFLAG & MENV2).
    (* require that init_own is equal to entry analysis result *)
    
    
    eexists. split.
    (* step *)
    econstructor. econstructor; eauto.
    
    
Lemma transf_initial_states q:
  forall S1, initial_state ge q S1 ->
  exists S2, RustIRsem.initial_state tge q S2 /\ match_states S1 S2.
Proof.
Admitted. 

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> RustIRsem.final_state S2 r.
Proof.
Admitted. 

Lemma transf_external:
  forall S R q, match_states S R -> at_external ge S q ->
  RustIRsem.at_external tge R q /\
  forall r S', after_external S r S' ->
  exists R', RustIRsem.after_external R r R' /\ match_states S' R'.
Proof.
  intros S R q HSR Hq. destruct Hq; inv HSR.
Qed. 

Lemma transf_fundef_internal: 
forall q se2,
Genv.is_internal (Genv.globalenv se2 tprog) (cq_vf q) =
Genv.is_internal (Genv.globalenv se2 prog) (cq_vf q). 
Admitted. 

End PRESERVATION.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_id) (cc_id) (semantics prog) (RustIRsem.semantics tprog).
Proof.
    fsim eapply forward_simulation_plus; simpl in *. 
    - inv MATCH. simpl. auto. 
    - intros. inv H. eapply transf_fundef_internal; eauto. 
    - intros. inv H. eapply transf_initial_states. eauto.  
    - intros. exploit transf_final_states; eauto. 
    - intros. edestruct transf_external; eauto. exists tt, q1. intuition subst; eauto.
    - eauto using step_simulation.
Admitted.
