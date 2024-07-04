Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR RustOp.
Require Import Errors.
Require Import Clightgen Clightgenspec.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope gensym_monad_scope.

(** Correctness proof for the generation of Clight *)

Definition match_glob (ctx: clgen_env) gd tgd : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar (fun ty ty' => to_ctype ty = ty') v1 v2
  | Gfun fd1, Gfun fd2 =>
      tr_fundef ctx fd1 fd2
  | _, _ => False
  end.

Record match_prog (p: RustIR.program) (tp: Clight.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_comp_env:
    tr_composite_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env);
    match_prog_def:
    (* match_program_gen tr_fundef (fun ty ty' => to_ctype ty = ty') p p tp; *)
    forall id, Coqlib.option_rel (match_glob (build_clgen_env p tp)) ((prog_defmap p)!id) ((prog_defmap tp)!id);
    match_prog_skel:
    erase_program tp = erase_program p;
    match_prog_malloc:
    exists orgs rels tyl rety cc, (prog_defmap p) ! malloc_id = Some (Gfun (Rusttypes.External orgs rels EF_malloc tyl rety cc));
    match_prog_free:
    exists orgs rels tyl rety cc, (prog_defmap p) ! free_id = Some (Gfun (Rusttypes.External orgs rels EF_free tyl rety cc));

  }.

(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: RustIR.program.
Variable tp: Clight.program.
Let build_ctx := build_clgen_env p tp.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob build_ctx) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob build_ctx) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob build_ctx)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None ))).
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None),
      (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None).
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
  match_glob (build_ctx) g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ tr_fundef build_ctx f tf.
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
  Genv.find_funct (Clight.globalenv tse tp) tv = None.
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
  (forall c f tf, tr_fundef c f tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (Clight.globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold Clight.fundef.
    simpl. rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.

Section PRESERVATION.

Variable prog: RustIR.program.
Variable tprog: Clight.program.
Let ctx := build_clgen_env prog tprog.
Let ce := ctx.(clgen_src_cenv).
Let tce := ctx.(clgen_tgt_cenv).
Let dropm := ctx.(clgen_dropm).
Let glues := ctx.(clgen_glues).

Hypothesis TRANSL: match_prog prog tprog.
Variable w: inj_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* injp or inj ? *)
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.

Let ge := RustIR.globalenv se prog.
Let tge := Clight.globalenv tse tprog.

Hypothesis GE: inj_stbls w se tse.

(* Lemma comp_env_preserved:
   tge =  ce.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. destruct TRANSF as [_ EQ]. simpl in EQ. congruence.
Qed.  *)



(* Simulation relation *)

(* Let ce := prog.(prog_comp_env). *)
(* Let tce := tprog.(Ctypes.prog_comp_env). *)
(* Let dropm := generate_dropm prog. *)
(* Let glues := generate_drops ce tce prog.(prog_types) dropm. *)

Definition var_block_rel (f: meminj) (s: block * type) (t: block * Ctypes.type) : Prop :=
  let (b, ty) := s in
  let (tb, cty) := t in
  f b = Some (tb, 0) /\ cty = to_ctype ty.

Definition match_env (f: meminj) (e: env) (te: Clight.env) : Prop :=
  (* me_mapped in Simpllocalproof.v *)
  forall id, Coqlib.option_rel (var_block_rel f) e!id te!id.
  
Lemma match_env_incr: forall e te j1 j2,
    match_env j1 e te ->
    inject_incr j1 j2 ->
    match_env j2 e te.
Proof.
  unfold match_env.
  intros. generalize (H id). intros REL.
  inv REL. constructor. constructor.
  destruct x. destruct y.
  red. red in H3. destruct H3.
  split; eauto.
Qed.


(* We need to maintain the well-formedness of local environment in the
simulation *)
Definition well_formed_env (f: function) (e: env) : Prop :=
  forall id, ~ In id (var_names f.(fn_vars)) -> e!id = None.

Lemma wf_env_target_none: forall j e te l id f,
    match_env j e te ->
    well_formed_env f e ->
    list_disjoint (var_names (f.(fn_params) ++ f.(fn_vars))) l ->
    In id l ->
    te!id = None.
Proof.
Admitted.

Lemma function_entry_wf_env: forall ge f vargs e m1 m2,
    function_entry ge f vargs m1 e m2 ->
    well_formed_env f e.
Admitted.

(* Can be proved by tr_composite *)
Definition enum_consistent (eid fid uid ufid: ident) : Prop :=
  forall co,
    ce ! eid = Some co ->
    co.(co_sv) = TaggedUnion ->
    exists tco utco, tce ! eid = Some tco
                /\ tce ! uid = Some utco
                /\ forall fofs bf, variant_field_offset ce fid co.(co_members) = OK (fofs, bf) ->
                  exists cfofs1 cfofs2,
                    Ctypes.field_offset tce ufid tco.(Ctypes.co_members) = OK (cfofs1, Full)
                    /\ Ctypes.union_field_offset tce fid utco.(Ctypes.co_members) = OK (cfofs2, Full)
                    /\ fofs = cfofs1 + cfofs2.
    
Inductive match_dropmemb_stmt (co_id: ident) (arg: Clight.expr) : struct_or_variant -> option drop_member_state -> Clight.statement -> Prop :=
| match_drop_in_struct_comp: forall id fid fty tys drop_id ts call_arg,
    let field_param := Efield arg fid (to_ctype fty) in
    forall (GLUE: dropm ! id = Some drop_id)
    (MSTMT: makeseq (drop_glue_for_box_rec field_param tys) = ts)
    (CALLARG: call_arg = (deref_arg_rec field_param tys)),
    match_dropmemb_stmt co_id arg Struct (Some (drop_member_comp fid fty id tys))
      (Clight.Ssequence (call_composite_drop_glue call_arg (Clight.typeof call_arg) drop_id) ts)
| match_drop_in_enum_comp: forall id fid fty tys drop_id ts uid ufid call_arg,
    let field_param := Efield (Efield arg ufid (Tunion uid noattr)) fid (to_ctype fty) in
    forall (ECONSIST: enum_consistent co_id fid uid ufid)
    (GLUE: dropm ! id = Some drop_id)
    (MSTMT: makeseq (drop_glue_for_box_rec field_param tys) = ts)
    (CALLARG: call_arg = (deref_arg_rec field_param tys)),
    match_dropmemb_stmt co_id arg TaggedUnion (Some (drop_member_comp fid fty id tys))
    (Clight.Ssequence (call_composite_drop_glue call_arg (Clight.typeof call_arg) drop_id) ts)
| match_drop_box_struct: forall fid fty tys,
    let field_param := Efield arg fid (to_ctype fty) in
    match_dropmemb_stmt co_id arg Struct (Some (drop_member_box fid fty tys))
      (makeseq (drop_glue_for_box_rec field_param tys))
| match_drop_box_enum: forall fid fty tys uid ufid,
    let field_param := Efield (Efield arg ufid (Tunion uid noattr)) fid (to_ctype fty) in
    forall (ECONSIST: enum_consistent co_id fid uid ufid),
    match_dropmemb_stmt co_id arg TaggedUnion (Some (drop_member_box fid fty tys))
    (makeseq (drop_glue_for_box_rec field_param tys))
| match_drop_none: forall sv,
    match_dropmemb_stmt co_id arg sv None Clight.Sskip
.

(* We need to record the list of stack block for the parameter of the
drop glue *)
Inductive match_cont (j: meminj) : RustIR.cont -> Clight.cont -> mem -> mem -> list block -> Prop :=
| match_Kstop: forall m tm bs,
    match_cont j RustIR.Kstop Clight.Kstop m tm bs
| match_Kseq: forall s ts k tk m tm bs
    (* To avoid generator, we need to build the spec *)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs),
    match_cont j (RustIR.Kseq s k) (Clight.Kseq ts tk) m tm bs
| match_Kloop: forall s ts k tk m tm bs
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs),
    match_cont j (RustIR.Kloop s k) (Clight.Kloop1 ts Clight.Sskip tk) m tm bs
| match_Kcall1: forall p f tf e te le k tk cty temp pe m tm bs
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None)
    (* we need to consider temp is set to a Clight expr which is
    translated from p *)
    (TRFUN: tr_function ce tce dropm glues f tf)
    (CTY: cty = to_ctype (typeof_place p))
    (PE: place_to_cexpr tce p = OK pe)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MENV: match_env j e te),
    match_cont j (RustIR.Kcall (Some p) f e k) (Clight.Kcall (Some temp) tf te le (Clight.Kseq (Clight.Sassign pe (Etempvar temp cty)) tk)) m tm bs
| match_Kcall2: forall f tf e te le k tk m tm bs
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None)
    (* how to relate le? *)
    (TRFUN: tr_function ce tce dropm glues f tf)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MENV: match_env j e te),
    match_cont j (RustIR.Kcall None f e k) (Clight.Kcall None tf te le tk) m tm bs
| match_Kdropcall_composite: forall id te le k tk tf b ofs b' ofs' pb m tm co membs ts1 kts fid fty tys bs,
    (* invariant that needed to be preserved *)
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    (* let field_param := Efield deref_param fid (to_ctype fty) in *)
    forall (CO: ce ! id = Some co)
      (MSTMT:
        match_dropmemb_stmt id deref_param co.(co_sv) (Some (drop_member_box fid fty tys)) ts1 /\
        match co.(co_sv) with
        | Struct =>
            exists ts2,            
              drop_glue_for_members ce dropm deref_param membs = ts2 /\
              kts = (Clight.Kseq ts2 tk)
        | TaggedUnion =>
            exists uts,
              kts = (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Clight.Kswitch tk))) /\
              membs = nil
        end)
    (* (STRUCT: co.(co_sv) = Struct) *)
    (* (MSTMT1: match_dropmemb_stmt id deref_param Struct (Some (drop_member_box fid fty tys)) ts1) *)
    (* (MSTMT2: drop_glue_for_members ce dropm deref_param membs = ts2) *)
    (MCONT: match_cont j k tk m tm bs)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env ))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (* Free pb does not affect bs *)
    (NOTIN: ~ In pb bs)
    (GLUE: glues ! id = Some tf)
    (MINJ: Mem.inject j m tm),
      match_cont j
        (RustIR.Kdropcall id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k)
        (Clight.Kcall None tf te le (Clight.Kseq ts1 kts)) m tm (pb :: bs)
.

(* | match_Kdropcall_enum: forall id te le k tk tf b ofs b' ofs' pb m tm co tys ts fid fty uts, *)
(*     (* invariant that needed to be preserved *) *)
(*     let co_ty := (Ctypes.Tstruct id co.(co_attr)) in *)
(*     let pty := Tpointer co_ty noattr in *)
(*     let deref_param := Ederef (Evar param_id pty) co_ty in *)
(*     (* we do not know the union_id and union_type *) *)
(*     (* let field_param := Efield (Efield deref_param ufid (Tunion uid noattr)) fid (to_ctype fty) in *) *)
(*     forall (CO: ce ! id = Some co) *)
(*     (ENUM: co.(co_sv) = TaggedUnion)       *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MSTMT: match_dropmemb_stmt id deref_param TaggedUnion (Some (drop_member_box fid fty tys)) ts) *)
(*     (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env )) *)
(*     (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs')) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs')) *)
(*     (UNREACH: forall ofs, loc_out_of_reach j m pb ofs) *)
(*     (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable) *)
(*     (GLUE: glues ! id = Some tf) *)
(*     (MINJ: Mem.inject j m tm), *)
(*       match_cont j *)
(*         (RustIR.Kdropcall id (Vptr b ofs) (Some (drop_member_box fid fty tys)) nil k) *)
(*         (Clight.Kcall None tf te le (Clight.Kseq ts (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Clight.Kswitch tk))))) m tm *)
(* . *)


Inductive match_states: RustIR.state -> Clight.state -> Prop :=
| match_regular_state: forall f tf s ts k tk m tm e te le j
    (WFENV: well_formed_env f e)
    (* maintain that this function is a normal function *)
    (NORMALF: f.(fn_drop_glue) = None)
    (MFUN: tr_function ce tce dropm glues f tf)
    (MSTMT: tr_stmt ce tce dropm s ts)    
    (* match continuation: we do not care about m and tm because they
    must be unused in the continuation of normal state *)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MINJ: Mem.inject j m tm)   
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (MENV: match_env j e te),
    match_states (RustIR.State f s k e m) (Clight.State tf ts tk te le tm)
| match_call_state: forall vf vargs k m tvf tvargs tk tm j
    (* match_kcall is independent of ce and dropm  *)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (VINJ: Val.inject j vf tvf)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (AINJ: Val.inject_list j vargs tvargs),
    (* (VFIND: Genv.find_funct ge vf = Some fd) *)
    (* (FUNTY: type_of_fundef fd = Tfunction orgs rels targs tres cconv), *)
    match_states (RustIR.Callstate vf vargs k m) (Clight.Callstate tvf tvargs tk tm)
| match_return_state: forall v k m tv tk tm j
   (MCONT: forall m tm bs, match_cont j k tk m tm bs)
   (MINJ: Mem.inject j m tm)
   (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
   (RINJ: Val.inject j v tv),
    match_states (RustIR.Returnstate v k m) (Clight.Returnstate tv tk tm)
(* | match_calldrop_box: forall k m b ofs tk tm ty j fb tb tofs *)
(*     (* we can store the address of p in calldrop and build a local env *)
(*        in Drop state according to this address *) *)
(*     (VFIND: Genv.find_def tge fb = Some (Gfun free_decl)) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)) *)
(*     (* Because k may contain Kdropcall, we must consider the specific *)
(*     m and tm *) *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MINJ: Mem.inject j m tm) *)
(*     (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))), *)
(*     match_states (RustIR.Calldrop (Vptr b ofs) (Tbox ty) k m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr tb tofs)] tk tm) *)
(* | match_calldrop_composite: forall k m b ofs tb tofs tk tm j fb id fid drop_glue orgs ty *)
(*     (GLUE: glues ! id = Some drop_glue) *)
(*     (DROPM: dropm ! id = Some fid) *)
(*     (VFIND: Genv.find_funct tge (Vptr fb Ptrofs.zero) = Some (Ctypes.Internal drop_glue)) *)
(*     (SYMB: Genv.find_symbol tge fid = Some fb) *)
(*     (TY: ty = Tstruct orgs id \/ ty = Tvariant orgs id) *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MINJ: Mem.inject j m tm) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)) *)
(*     (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))), *)
(*     match_states (RustIR.Calldrop (Vptr b ofs) ty k m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr tb tofs)] tk tm) *)
| match_dropstate_struct: forall id k m tf ts1 ts2 tk te le tm j co membs pb b' ofs' b ofs s bs,
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    forall (CO: ce ! id = Some co)
    (STRUCT: co.(co_sv) = Struct)
    (MSTMT1: match_dropmemb_stmt id deref_param Struct s ts1)
    (MSTMT2: drop_glue_for_members ce dropm deref_param membs = ts2)
    (MCONT: match_cont j k tk m tm bs)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (GLUE: glues ! id = Some tf)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (VALIDBS: forall b, In b bs -> Mem.valid_block tm b)
    (NOTIN: ~ In pb bs),
      match_states (RustIR.Dropstate id (Vptr b ofs) s membs k m) (Clight.State tf ts1 (Clight.Kseq ts2 tk) te le tm)
| match_dropstate_enum: forall id k m tf tk te le tm j co pb b' ofs' b ofs s ts uts bs,
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    (* we do not know the union_id and union_type *)
    (* let field_param := Efield (Efield deref_param ufid (Tunion uid noattr)) fid (to_ctype fty) in *)
    forall (CO: ce ! id = Some co)
    (ENUM: co.(co_sv) = TaggedUnion)
    (MCONT: match_cont j k tk m tm bs)
    (MSTMT: match_dropmemb_stmt id deref_param TaggedUnion s ts)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (GLUE: glues ! id = Some tf)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (* It is used to preserve pb during (m,tm) injected move *)
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (* Use VALIDBS to prove NOTIN in Dropstate tansitions *)
    (VALIDBS: forall b, In b bs -> Mem.valid_block tm b)
    (NOTIN: ~ In pb bs),
      match_states (RustIR.Dropstate id (Vptr b ofs) s nil k m) (Clight.State tf ts (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Kswitch tk))) te le tm)
.


(* Type preservation in translation *)
Lemma type_eq_except_origins_to_ctype: forall ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    to_ctype ty1 = to_ctype ty2.
Proof.
  induction ty1; destruct ty2;simpl; try congruence;
    intros TYEQ; try eapply proj_sumbool_true in TYEQ; try congruence.
    erewrite IHty1. eauto.
    destruct m; destruct m0; auto.
    congruence. congruence.
Qed.

Lemma place_to_cexpr_type: forall p e,
    place_to_cexpr tce p = OK e ->
    to_ctype (typeof_place p) = Clight.typeof e.
    Proof.
    induction p; simpl; intros; simpl in *.
  -  monadInv H. auto.
  - monadInv H. auto.
  - monadInv H. auto.
  - destruct (typeof_place _); inversion H.
    destruct (tce ! i0);  inversion H.
    destruct (co_su c);  inversion H.
    destruct (Ctypes.co_members c );  inversion H.
    destruct m;
    destruct m0; inversion H;
    try destruct m; try destruct m0;
    monadInv H4; try monadInv H; auto.  
  Qed.

Lemma expr_to_cexpr_type: forall e e',
    expr_to_cexpr ce tce e = OK e' ->
    to_ctype (typeof e) = Clight.typeof e'.
Proof.
    destruct e eqn: E. 
    - simpl. 
      destruct (type_eq_except_origins) eqn:Horg.
      intros.
      assert ((to_ctype t) = to_ctype (typeof_place p)) as EQtp.
      { 
        eapply type_eq_except_origins_to_ctype.
        auto.
      }
      rewrite EQtp. apply place_to_cexpr_type. auto.
      intros. monadInv H.
    - simpl; destruct p;  intros ; simpl in *; try (monadInv H); auto.
      destruct (type_eq_except_origins t (typeof_place p)) eqn : Htype_eq_org; simpl in *.
      apply type_eq_except_origins_to_ctype in Htype_eq_org.
      rewrite Htype_eq_org. apply place_to_cexpr_type. auto.
      inversion H.
      destruct (typeof_place p); try (inversion H).
      destruct (ce ! i0); try (inversion H).
      destruct (field_tag i (co_members c)); try inversion H.
      destruct (get_variant_tag tce i0); try inversion H.
      monadInv H4. auto.
Qed.

(* Injection is preserved during evaluation *)

Lemma deref_loc_inject: forall ty m tm b ofs b' ofs' v j,
    deref_loc ty m b ofs v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr b' ofs') ->
    exists v', Clight.deref_loc (to_ctype ty) tm b' ofs' Full v' /\ Val.inject j v v'.
Proof.
  intros.
  inv H.
  - (*by value*)
    exploit Mem.loadv_inject; eauto. intros [tv [A B]].
    exists tv. split. econstructor. 
    instantiate (1:= chunk). 
    destruct ty; simpl in *; congruence.
    auto. auto.
  - (* by ref*)
    exists ((Vptr b' ofs')). split. 
    eapply Clight.deref_loc_reference. 
    destruct ty; simpl in *; congruence.
    auto. 
  - (*by copy*)
    exists (Vptr b' ofs'). split. eapply Clight.deref_loc_copy.
    destruct ty; simpl in *; congruence.
    auto.
Qed.



Lemma eval_place_inject: forall p lv e te j m tm le b ofs,
    place_to_cexpr tce p = OK lv ->
    eval_place ce e m p b ofs ->
    match_env j e te ->
    Mem.inject j m tm ->
    (** Why eval_lvalue requires tge ? Because eval_Evar_global ! We
    want to just use ctce. But I think we can prove that ctce!id =
    tge.(cenv)!id because we have ce!id and tr_composte ce tge.(cenv)
    and tr_composite ce ctce *)
    exists b' ofs', Clight.eval_lvalue tge te le tm lv b' ofs' Full /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Proof. 
  intros p;
  intros lv e te j m tm le b ofs.
  intros Hplaceok Hevalp. 
  generalize dependent lv.
  induction Hevalp; intros lv Hplaceok Hmatch Hmem_inj; intros.   
  - (* p = Plocal i t *)
    monadInv Hplaceok.
    generalize (Hmatch id). intros REL. inv REL.
    + rewrite <- H1 in H. inv H.
    + destruct x. destruct y. simpl in H2. destruct H2. 
      subst. 
      rewrite <- H0 in H. inv H.
      esplit. esplit. 
      split. econstructor. eauto. 
      econstructor. eauto. eauto.
  - (* p = Pfield p i t *)  
    simpl in Hplaceok. 
    inv Hplaceok. simpl in *.  monadInv H3. 
    exploit IHHevalp; eauto.
    intros[b' [ofs' [A B]]].
    inv B. 
    exists b'.
    exists (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta0)) (Ptrofs.repr delta)). 
    split.
    + exploit place_to_cexpr_type; eauto. intro Htpx. rewrite H in Htpx. simpl in Htpx.
      eapply eval_Efield_struct. eapply Clight.eval_Elvalue. 
      apply A.  rewrite <- Htpx. apply Clight.deref_loc_copy.   
      auto.
      rewrite <- Htpx.  eauto. 
      *   admit.
      * (*Ctypes.field_offset tge i (Ctypes.co_members ?co) = OK (delta, Full) *) admit.
    + econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut.
  - admit.
  - monadInv Hplaceok.
    exploit IHHevalp; eauto.
    intros [b' [ofs'' [A B]]]. 
    exploit deref_loc_inject; eauto. intros [tv [C D]].
    inv D. 
    esplit. esplit. 
    split. eapply Clight.eval_Ederef. 
    eapply eval_Elvalue. apply A. 
    + exploit place_to_cexpr_type. eauto. intro Hctypex. rewrite <- Hctypex.
      eauto.
    + eauto.
Admitted.


Lemma eval_expr_inject: forall e te j a a' m tm v le,
    eval_expr ce e m a v ->
    expr_to_cexpr ce tce a = OK a' ->
    match_env j e te ->
    Mem.inject j m tm ->
    exists v', Clight.eval_expr tge te le tm a' v' /\ Val.inject j v v'.  
(* To prove this lemma, we need to support type checking in the
   evaluation of expression in RustIR *)
Proof. 
  destruct a.
  - admit. 
  - simpl. 
    intros. 
    induction p eqn:Hp. 
    + simpl. intros. simpl in *. inv H. inv H0. 
      esplit. split. econstructor.
      inv H4. auto. 
    + intros. simpl in *. inv H. inv H4. exists (Vint i). 
      split. inv H0. constructor. auto.
    + intros. simpl in *. inv H. inv H4. exists (Vfloat f).
      split. inv H0. constructor. auto.
    + intros. simpl in *. inv H. inv H4. exists (Vsingle f).
      split. inv H0. constructor. auto.
    + intros. simpl in *. inv H. inv H4. exists (Vlong i).
      split. inv H0. constructor. auto.
    + (* Eplace p0 t *)
      intros. 
      * simpl in *. destruct (type_eq_except_origins t (typeof_place p0) ) eqn:Horg. 
        inv H. inv H4.  inv H5. inv H0.      
        ** generalize (H1 id). intros REL. inv REL.
            *** esplit. split. econstructor. econstructor. 
                instantiate (1:= b). congruence.
                simpl in *.
                exploit deref_loc_inject; eauto.
                (* instantiate (1:= ) *)
                admit.
                admit.
            *** destruct x. destruct y. simpl in H4. destruct H4. 
                esplit. split. econstructor. econstructor.
                instantiate (1:= b1).  congruence.
                simpl.
    Admitted.     
    

Lemma assign_loc_inject: forall f ty m loc ofs v m' tm loc' ofs' v',
    assign_loc ge ty m loc ofs v m' ->
    Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
    Val.inject f v v' ->
    Mem.inject f m tm ->
    exists f' tm',
      Clight.assign_loc tge (to_ctype ty) tm loc' ofs' Full v' tm'
      /\ Mem.inject f' m' tm'
      /\ inj_incr (injw f (Mem.support m) (Mem.support tm)) (injw f' (Mem.support m') (Mem.support tm')).
Admitted.

Lemma sem_cast_to_ctype_inject: forall f v1 v1' v2 t1 t2 m,
    sem_cast v1 t1 t2 = Some v2 ->
    Val.inject f v1 v1' ->
    exists v2', Cop.sem_cast v1' (to_ctype t1) (to_ctype t2) m = Some v2' /\ Val.inject f v2 v2'.
Admitted.

Lemma extcall_free_inject: forall se tse v tv m m' tm t j,
    extcall_free_sem se [v] m t Vundef m' ->
    Mem.inject j m tm ->
    Val.inject j v tv ->
    exists tm', extcall_free_sem tse [tv] tm t Vundef tm'
           /\ Mem.inject j m' tm'
           /\ inj_incr (injw j (Mem.support m) (Mem.support tm)) (injw j (Mem.support m') (Mem.support tm')).
Admitted.

(* use injp_acc to prove inj_incr *)
Lemma injp_acc_inj_incr: forall f f' m1 m2 m1' m2' Hm Hm',
          injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm') ->
          inj_incr (injw f (Mem.support m1) (Mem.support m2)) (injw f' (Mem.support m1') (Mem.support m2')).
Proof.
  intros. inv H.
  econstructor. eauto.
  red. red in H13. unfold Mem.valid_block in H13. eauto.
  eapply (Mem.unchanged_on_support _ _ _ H10).
  eapply (Mem.unchanged_on_support _ _ _ H11).
Qed.


Remark list_cons_neq: forall A (a: A) l, a :: l <> l.
Proof.
  intros. induction l. intro. congruence.
  intro. inv H.  congruence.
Qed.

Lemma initial_states_simulation:
  forall q1 q2 S, match_query (cc_c inj) w q1 q2 -> initial_state ge q1 S ->
             exists R, Clight.initial_state tge q2 R /\ match_states S R.
Proof.
  intros ? ? ? Hq HS.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq.
  subst. 
  inversion HS. clear HS. subst vf sg vargs m.
  exploit find_funct_match;eauto. eapply inj_stbls_match. eauto. eauto.
  intros (tf & FIND & TRF).
  (* inversion TRF to get tf *)
  inv TRF.
  eexists. split.
  - assert (SIG: signature_of_type targs tres tcc = Ctypes.signature_of_type (to_ctypelist targs) (to_ctype tres) tcc). admit.
    rewrite SIG. econstructor. eauto.
    (* type of function *) admit.
    (* val_casted_list *) admit.
    (* sup include *)
    simpl. inv Hm. inv GE. simpl in *. auto.
  - econstructor; eauto. econstructor.
    inv Hm. simpl. reflexivity.
Admitted.

Lemma function_entry_inject:
  forall f tf m1 m2 tm1 j1 vargs tvargs e
    (VARS:  Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars))
    (PARAMS: Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params)),
    function_entry ge f vargs m1 e m2 ->
    Mem.inject j1 m1 tm1 ->
    Val.inject_list j1 vargs tvargs ->
    exists j2 te tm2,
      Clight.function_entry1 tge tf tvargs tm1 te (create_undef_temps (fn_temps tf)) tm2
      /\ match_env j2 e te
      /\ Mem.inject j2 m2 tm2
      /\ inj_incr (injw j1 (Mem.support m1) (Mem.support tm1)) (injw j2 (Mem.support m2) (Mem.support tm2)).
Admitted.

Lemma PTree_elements_one (A: Type) : forall id (elt: A),
    PTree.elements (PTree.set id elt (PTree.empty A)) = (id, elt) :: nil.
Proof.
  intros.
  generalize (PTree.elements_correct (PTree.set id elt (PTree.empty A)) id (PTree.gss _ _ _)).
  intros IN.
  generalize (PTree.elements_keys_norepet (PTree.set id elt (PTree.empty A))).
  intros NOREPEAT.
  destruct (PTree.elements (PTree.set id elt (PTree.empty A))) eqn: LIST.
  inv IN.
  destruct p. 
  inv IN.
  - inv H.
    destruct l. auto. destruct p.
    assert (IN1: In (p,a) ((id,elt)::(p,a)::l)).
    eapply in_cons. econstructor. auto.
    simpl in NOREPEAT. inv NOREPEAT. 
    generalize (PTree.elements_complete (PTree.set id elt (PTree.empty A)) p a).
    rewrite LIST. intros B. apply B in IN1.
    erewrite PTree.gsspec in IN1.
    destruct (peq p id) eqn: PEQ. inv IN1.
    exfalso. eapply H1. econstructor. auto.
    rewrite PTree.gempty in IN1. congruence.
  - simpl in NOREPEAT. inv NOREPEAT.
    assert (GP: (PTree.set id elt (PTree.empty A))! p = Some a).
    eapply PTree.elements_complete. rewrite LIST.
    econstructor. auto.
    erewrite PTree.gsspec in GP.
    destruct (peq p id) eqn: PEQ. inv GP.
    exfalso. eapply H2. replace id with (fst (id, a)). eapply in_map.
    auto. auto.
    rewrite PTree.gempty in GP. congruence.
Qed.

Lemma step_drop_simulation:
  forall S1 t S2, step_drop ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  unfold build_clgen_env in *. unfold ctx in *. simpl in *.
  induction 1; intros; inv MS.

  (* step_dropstate_init *)
  - admit.

  (* step_dropstate_composite *)
  - admit.
  (* step_dropstate_composite *)
  - admit.

  (* step_dropstate_box *)
  - admit.
  (* step_dropstate_box *)
  - admit.

  (* step_drop_return1 *)
  - inv MSTMT1. simpl.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_refl.
      1-3: eauto.
    (* match_states *)
    + econstructor; auto. econstructor.
      instantiate (1 := initial_generator). auto.
      
      (* Mem.inject *)
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs0 + delta).
      replace (ofs0 + delta - delta) with ofs0 by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      (* inj_incr *)
      erewrite Mem.support_free with (m2:= tm1); eauto.
            
  (* step_drop_return1 (in enum) *)
  - inv MSTMT.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      (* evaluate Sbreak *)
      econstructor. eapply star_step.
      econstructor. auto.
      (* evaluate Kcall *)
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_refl.
      1-5: eauto.
    (* match_states *)
    + econstructor; auto. econstructor.
      instantiate (1 := initial_generator). auto.
      (* Mem.inject *)
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs0 + delta).
      replace (ofs0 + delta - delta) with ofs0 by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      (* inj_incr *)
      erewrite Mem.support_free with (m2:= tm1); eauto.
      
  (* step_drop_return2 (in struct) *)
  - inv MSTMT1. simpl.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    inv MCONT.
    
    eexists. split.
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_step.
      econstructor.
      eapply star_refl.
      1-4: eauto.
    (* match_states *)
    + assert (MINJ3: Mem.inject j m tm1).
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs + delta).
      replace (ofs + delta - delta) with ofs by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      assert (INCR3: inj_incr w (injw j (Mem.support m) (Mem.support tm1))).
      erewrite Mem.support_free with (m2:= tm1); eauto.
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => pb <> b) tm tm1).
      { eapply Mem.free_unchanged_on; eauto. }        
      assert (MCONT3: match_cont j k tk0 m tm1 bs0) by admit.
      assert (LOADV3: Mem.loadv Mptr tm1 (Vptr pb0 Ptrofs.zero) = Some (Vptr b'0 ofs'0)).
      { eapply Mem.load_unchanged_on; eauto.
        rewrite Ptrofs.unsigned_zero. intros.         
        eapply not_in_cons. eauto. }
      assert (PERM3: Mem.range_perm tm1 pb0 0 (Ctypes.sizeof tce (Tpointer (Ctypes.Tstruct id2 noattr) noattr)) Cur Freeable).
      { red. intros.
        (* range_perm *)
        erewrite <- Mem.unchanged_on_perm; eauto. simpl. eapply not_in_cons.
        eauto. eapply VALIDBS. constructor; auto. }
      assert (VALIDBS3: forall b : block, In b bs0 -> Mem.valid_block tm1 b).
      { (* validbs *)
        intros.
        eapply Mem.valid_block_unchanged_on; eauto.
        eapply VALIDBS. eapply in_cons. auto. }
      
      (* case 1: co_sv co0 = Struct. Return to a struct drop glue*)      
      destruct (co_sv co0) eqn: SV.
      * destruct MSTMT as (MEMBST & ts2 & TS2 & KTS). subst.
        eapply match_dropstate_struct; eauto.
        
      (* case 2: co_sv co0 = Taggedunion. Return to a enum drop glue*)      
      * destruct MSTMT as (MEMBST & uts & KTS & MEMBS). subst.
        eapply match_dropstate_enum; eauto.
        
  (* step_drop_return2 (in enum) *)
   -inv MSTMT.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      (* evaluate Sbreak *)
      econstructor. eapply star_step.
      econstructor. auto.
      (* evaluate Kcall *)
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_step.
      econstructor.      
      eapply star_refl.
      1-6: eauto.
    (* match_states *)
    + assert (MINJ3: Mem.inject j m tm1).
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs + delta).
      replace (ofs + delta - delta) with ofs by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      assert (INCR3: inj_incr w (injw j (Mem.support m) (Mem.support tm1))).
      erewrite Mem.support_free with (m2:= tm1); eauto.
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => pb <> b) tm tm1).
      { eapply Mem.free_unchanged_on; eauto. }        
      assert (MCONT3: match_cont j k tk0 m tm1 bs0) by admit.
      assert (LOADV3: Mem.loadv Mptr tm1 (Vptr pb0 Ptrofs.zero) = Some (Vptr b'0 ofs'0)).
      { eapply Mem.load_unchanged_on; eauto.
        rewrite Ptrofs.unsigned_zero. intros.         
        eapply not_in_cons. eauto. }
      assert (PERM3: Mem.range_perm tm1 pb0 0 (Ctypes.sizeof tce (Tpointer (Ctypes.Tstruct id2 noattr) noattr)) Cur Freeable).
      { red. intros.
        (* range_perm *)
        erewrite <- Mem.unchanged_on_perm; eauto. simpl. eapply not_in_cons.
        eauto. eapply VALIDBS. constructor; auto. }
      assert (VALIDBS3: forall b : block, In b bs0 -> Mem.valid_block tm1 b).
      { (* validbs *)
        intros.
        eapply Mem.valid_block_unchanged_on; eauto.
        eapply VALIDBS. eapply in_cons. auto. }
      
      (* case 1: co_sv co0 = Struct. Return to a struct drop glue*)      
      destruct (co_sv co0) eqn: SV.
      * destruct MSTMT as (MEMBST & ts2 & TS2 & KTS). subst.
        eapply match_dropstate_struct; eauto.
        
      (* case 2: co_sv co0 = Taggedunion. Return to a enum drop glue*)      
      * destruct MSTMT as (MEMBST & uts1 & KTS & MEMBS). subst.
        eapply match_dropstate_enum; eauto.
        
Admitted.

       
Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  unfold build_clgen_env in *. unfold ctx in *. simpl in *.
  induction 1; intros; inv MS.
          
  (* assign *)
  - inv MSTMT. simpl in H3.
    monadInv_comb H3.
    (* eval place and expr *)       
    exploit eval_place_inject;eauto. instantiate (1:= le0).
    intros (b' & ofs' & EL & INJL).
    exploit eval_expr_inject; eauto. instantiate (1:= le0).
    intros (v' & ER & INJV1).
    exploit sem_cast_to_ctype_inject; eauto. instantiate (1 := tm).
    intros (v1' & CASTINJ & INJV2).
    exploit assign_loc_inject. eauto. eauto. eapply INJV2. eauto.
    intros (j2 & tm2 & TASS & INJA & INCR2).
    erewrite place_to_cexpr_type in *;eauto.
    erewrite expr_to_cexpr_type in *;eauto.
    eexists. split.
    (* step *)
    + eapply plus_one.
      eapply Clight.step_assign;eauto.
      (* Other proof strategy for sem_cast:
         1. type equal between lhs and rhs
         2. evaluation of well typed expression produces casted value (val_casted)
         3. use cast_val_casted *)
    (* match state *)
    + assert (INCR3: inj_incr w (injw j2 (Mem.support m2) (Mem.support tm2))).
      etransitivity. eauto. eauto.      
      eapply match_regular_state. eauto. eauto. eauto.
      econstructor. simpl. instantiate (1 := g). eauto.
      instantiate (1 := j2). admit.   (* inject_incr and match_cont *)
      eauto. eauto.
      eapply match_env_incr;eauto. inv INCR2. auto.
      
  (* assign_variant *)
  - inv MSTMT. simpl in H9.
    monadInv_comb H9.
    unfold transl_assign_variant in EQ2.
    rename H4 into SENUM.
    unfold ge in SENUM. simpl in SENUM. fold ce in SENUM.
    rewrite SENUM in EQ2.
    destruct (co_sv co) eqn: SCV; [inv EQ2|].
    rename H5 into TAG. rewrite TAG in EQ2. 
    destruct TRANSL. eapply match_prog_comp_env0 in SENUM as MATCHCOMP.
    rewrite SCV in MATCHCOMP.
    destruct MATCHCOMP as (tco & union_id & tag_fid & union_fid & union & MATCHCOMP).
    cbn in MATCHCOMP.
    destruct MATCHCOMP as (A & B & C & D & MATCHCOMP).
    fold tce in A. rewrite A in EQ2.
    rewrite D in EQ2.
    inv EQ2.
    (* step in target *)
    (* eexists. split. *)
    (* + eapply plus_left. *)
    (*   eapply Clight.step_seq. *)
    (*   eapply star_step. eapply Clight.step_assign. *)
    admit.

  (* box *)
  - inv MSTMT. simpl in H7.
    monadInv_sym H7. unfold gensym in EQ. inv EQ.    
    monadInv_comb EQ0.
    destruct g. simpl in H9. inv H9. eapply list_cons_neq in H8.
    contradiction.
    unfold transl_Sbox in H11. monadInv H11.
    destruct andb eqn: ANDB in EQ0;try congruence.
    eapply andb_true_iff in ANDB. destruct ANDB as (SZGT & SZLT).
    eapply Z.leb_le in SZGT. eapply Z.leb_le in SZLT.
    inv EQ0.
    (* find_symbol malloc = Some b *)
    destruct (match_prog_malloc _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MALLOC).    
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in MALLOC as (mb & FINDSYMB & FINDMALLOC). clear A.    
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* find_funct tge tb = Some malloc_decl *)
    assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some malloc_decl).
    { edestruct find_funct_match as (malloc & TFINDFUN & TRMALLOC).
      eauto. 
      eapply inj_stbls_match. eauto.
      instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
      destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff. eauto.
      econstructor. eauto. eauto.
      erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
      inv TRMALLOC. eauto. intuition. }
    (* mem alloc in target *)
    exploit Mem.alloc_parallel_inject. eapply MINJ.
    eauto. eapply Z.le_refl. eapply Z.le_refl. 
    intros (j2 & tm2 & tb & TALLOC & INJ2 & INCR2 & A & B).
    cut (match_env j2 le te).
    2: { eapply match_env_incr;eauto. }
    intros MENV2.
    (* store in malloc *)
    exploit Mem.store_mapped_inject. eapply INJ2. eauto.
    eapply A. instantiate (1:= (Vptrofs (Ptrofs.repr (sizeof ge (typeof e))))).
    econstructor. rewrite Z.add_0_r.
    intros (tm3 & STORE & INJ3).
    (* evaluate the expression which is stored in the malloc pointer *)
    exploit eval_expr_inject. eauto. eauto.
    eapply match_env_incr. eapply match_env_incr.
    eauto. eauto. eauto. eauto.
    instantiate (1:= (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tv & EXPR & VINJ). 
    (* sem_cast *)
    exploit sem_cast_to_ctype_inject. eauto. eauto. instantiate (1 := tm3).
    intros (tv1 & CAST1 & INJCAST).
    (* assign_loc for *temp *)
    exploit assign_loc_inject. eapply H4. instantiate (3 := j2).
    econstructor;eauto. eauto. eauto.
    rewrite Ptrofs.add_zero_l.
    intros (j3 & tm4 & ASSIGNLOC1 & INJ4 & INCR3).
    cut (match_env j3 le te).
    2: { eapply match_env_incr;eauto. inv INCR3. eauto. }
    intros MENV3.
    (* eval_lvalue lhs *)
    exploit eval_place_inject. eauto. eauto.
    eauto. eauto.
    instantiate (1 := (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tpb & tpofs & ELHS & VINJ3).
    (* assign_loc for lhs *)
    exploit assign_loc_inject. eapply H6. instantiate (3 := j3).
    eauto. 
    econstructor. inv INCR3. eapply H12. eauto. eauto.
    eauto. rewrite Ptrofs.add_zero_l.
    intros (j4 & tm5 & ASSIGNLOC2 & INJ5 & INCR4).
    cut (match_env j4 le te).
    2: { eapply match_env_incr;eauto. inv INCR4. eauto. }
    intros MENV4.
    
    eexists. split.
    + econstructor. econstructor. eapply star_step.
      econstructor. eapply star_left.
      (* step_call to malloc *)
      { eapply Clight.step_call.
        * simpl. eauto.
        * eapply eval_Elvalue. eapply eval_Evar_global.
          (* We have to ensure that e!malloc_id = None *)
          eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. eauto.
          eauto.
          simpl. eapply Clight.deref_loc_reference. auto.
        * repeat econstructor.
        * eauto.          
        * auto. }
      eapply star_step.
      (* evaluate malloc *)
      { eapply Clight.step_external_function.
        eauto.
        econstructor. erewrite Ptrofs.unsigned_repr; try lia.
        (* alloc *)
        instantiate (1 := tb).
        erewrite <- TALLOC. f_equal. symmetry.
        eapply to_ctype_sizeof. eapply expr_to_cexpr_type;eauto.
        eapply TRANSL.
        (* store sz *)        
        erewrite <- STORE. repeat f_equal. symmetry.
        eapply to_ctype_sizeof. eapply expr_to_cexpr_type;eauto.
        eapply TRANSL. }
      eapply star_step.
      (* returnstate to regular state *)
      eapply Clight.step_returnstate.
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_step.
      (* assign to the malloc pointer *)
      { eapply Clight.step_assign.
        eapply eval_Ederef. eapply eval_Etempvar.
        simpl. eapply PTree.gss.
        eauto.
        (* sem_cast in C side *)
        erewrite <- CAST1. rewrite H. f_equal. symmetry.
        eapply expr_to_cexpr_type;eauto.
        rewrite H. eauto. }
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_one.
      (* assign temp to p *)
      { eapply Clight.step_assign.
        eauto.
        econstructor. eapply PTree.gss.
        instantiate (1 := (Vptr tb Ptrofs.zero)).
        erewrite <- (place_to_cexpr_type p lhs). rewrite H. simpl.
        eapply cast_val_casted. econstructor.
        eauto.
        erewrite <- (place_to_cexpr_type p lhs). eauto.
        auto. }
      1-8: eauto.
    (* match_states *)
    + econstructor. 1-3 : eauto.      
      econstructor. simpl. instantiate (1 := initial_generator). eauto.
      instantiate (1 := j4). admit.   (* inject_incr and match_cont *)
      apply INJ5.
      exploit Mem.support_alloc. eapply H0. intros SUPM2.
      exploit Mem.support_alloc. eapply TALLOC. intros SUPTM2.      
      etransitivity. eauto.
      etransitivity. instantiate (1 := injw j2 (Mem.support m2) (Mem.support tm2)).
      eapply injp_acc_inj_incr.
      instantiate (1 := INJ2). instantiate (1 := MINJ).
      eapply injp_acc_alloc;eauto.
      exploit Mem.support_store. eapply H1.
      exploit Mem.support_store. eapply STORE. intros S1 S2.
      rewrite <- S1. rewrite <- S2.
      etransitivity. eauto. eauto.
      apply MENV4.
      
  (* step_drop_box *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2. inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* find_symbol free = Some b *)
    destruct (match_prog_free _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MFREE).    
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in MFREE as (mb & FINDSYMB & FINDFREE). clear A.
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* find_funct tge tb = Some free_decl *)
    assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some free_decl).
    { edestruct find_funct_match as (free & TFINDFUN & TRFREE).
      eauto. 
      eapply inj_stbls_match. eauto.
      instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
      destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff. eauto.
      econstructor. eauto. eauto.
      erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
      inv TRFREE. eauto. intuition. }
    (* deref_loc inject *)
    exploit deref_loc_inject;eauto. intros (tv' & TDEREF & VINJ2).    
    (* extcall_free_sem inject *)
    exploit extcall_free_inject; eauto. instantiate (1:= tse).
    intros (tm' & TFREE & MINJ1 & INCR1).
    
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* step to call drop *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* We have to ensure that e!free_id = None *)
        eapply wf_env_target_none; eauto.
        inv MFUN; try congruence.
        eauto. simpl. eauto.
        eauto.
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. econstructor. econstructor.                   
        eapply PTree.gss. simpl.
        (* deref_loc inject *)
        eauto. 
        (* sem_cast *)
        simpl. instantiate (1:= tv'). inv VINJ2.
        unfold Cop.sem_cast. simpl. auto.
        (* eval_exprlist *)
        econstructor.
        eauto. simpl.
        auto. }
      (* step to external call *)
      eapply star_step.
      { eapply Clight.step_external_function. eauto.
        eauto. }
      eapply star_one.
      econstructor.
      1-5: eauto.
      
    (* match_states  *)
    + econstructor; eauto.
      econstructor. instantiate (1 := initial_generator). eauto.
      etransitivity. eauto. eauto.

  (* step_drop_struct *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2.
    destruct (own_type ce (Tstruct orgs id)) eqn: OWNTY; try congruence.
    destruct (dropm!id) as [glue_id|]eqn: DROPM; try congruence.
    inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* Four steps to get the target drop glue for composite id *)
    (* 1. use generate_dropm_inv to get the source empty drop glue *)
    exploit generate_dropm_inv;eauto.
    intros (src_drop & PROGM & GLUEID).
    (* 2. use Genv.find_def_symbol to get the block of this drop glue
    and prove that target can also find an injected block *)
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in PROGM as (mb & FINDSYMB & FINDGLUE). clear A.
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* 3. use find_funct_match to prove that taget can find a
    drop_glue and tr_fundef src_drop tgt_drop *)
    exploit find_funct_match. eauto.
    eapply inj_stbls_match. eauto.
    instantiate (2 := Vptr mb Ptrofs.zero). simpl.
    destruct Ptrofs.eq_dec; try congruence.
    eapply Genv.find_funct_ptr_iff. eauto.
    econstructor. eauto.
    erewrite Ptrofs.add_zero_l. reflexivity.
    intros (tgt_drop & TFINDFUNC & TRFUN).
    (* 4. use generate_drops_inv to prove tgt_drop is the same as the
    result of drop_glue_for_composite *)
    inv TRFUN. inv H0. congruence.
    rewrite GLUEID in H. inv H.
    simpl in H2.
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eauto. eauto. rewrite COSTRUCT. simpl.
    intros DGLUE. inv DGLUE.
    rename H2 into GETGLUE.   
    (* alloc stack block in function entry *)
    set (pty := Tpointer (Ctypes.Tstruct comp_id noattr) noattr) in *.
    destruct (Mem.alloc tm 0 (Ctypes.sizeof tce pty)) as [tm1 psb] eqn: ALLOC.
    (* permission of psb *)
    assert (PERMFREE1: Mem.range_perm tm1 psb 0 (Ctypes.sizeof tce pty) Cur Freeable).
    { red. intros.
      eapply Mem.perm_alloc_2; eauto. }
    (* Mem.inject j m tm1 *)
    exploit Mem.alloc_right_inject; eauto. intros MINJ1.
    (* forall ofs, loc_out_of_reach j m psb ofs *)
    generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). intros NVALID.
    assert (OUTREACH1: forall ofs, loc_out_of_reach j m psb ofs).
    { red. intros. intro. eapply NVALID.
      eapply Mem.valid_block_inject_2; eauto. }
    (* store the function argument to (psb,0) *)
    assert (STORETM1: {tm2: mem | Mem.store Mptr tm1 psb 0 (Vptr pb pofs) = Some tm2}).
    { eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
      eapply Mem.valid_access_alloc_same;eauto. lia. unfold Mptr. unfold pty. simpl.
      destruct Archi.ptr64. simpl. lia. simpl. lia.
      eapply Z.divide_0_r. econstructor. }
    destruct STORETM1 as (tm2 & STORETM1).
    (* Mem.inject j m tm2 *)
    exploit Mem.store_outside_inject. eapply MINJ1.
    2: eapply STORETM1. intros.
    eapply Mem.fresh_block_alloc;eauto.
    eapply Mem.valid_block_inject_2;eauto.
    intros MINJ2.       
    (* store does not change permission *)
    assert (PERMFREE2: Mem.range_perm tm2 psb 0 (Ctypes.sizeof tce pty) Cur Freeable).
    red. intros. eapply Mem.perm_store_1; eauto.
    
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. right. right.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (comp_id, glue_id). split;auto.
          eapply PTree.elements_correct. auto. }
        eauto.        
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. 
        eapply PTree.gss. simpl.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl.
      eapply star_one.
      econstructor.
      1-5: eauto.

    (* match_states *)
    + eapply match_dropstate_struct with (bs := nil);eauto.
      econstructor.
      econstructor; eauto.
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr pb pofs)). eauto. eauto.
      intros. inv H.
      
  (* step_drop_enum *)
  - (** The following code is mostly the same as that in step_drop_struct *)
    inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2.
    destruct (own_type ce (Tvariant orgs id)) eqn: OWNTY; try congruence.
    destruct (dropm!id) as [glue_id|]eqn: DROPM; try congruence.
    inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* Four steps to get the target drop glue for composite id *)
    (* 1. use generate_dropm_inv to get the source empty drop glue *)
    exploit generate_dropm_inv;eauto.
    intros (src_drop & PROGM & GLUEID).
    (* 2. use Genv.find_def_symbol to get the block of this drop glue
    and prove that target can also find an injected block *)
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in PROGM as (mb & FINDSYMB & FINDGLUE). clear A.
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* 3. use find_funct_match to prove that taget can find a
    drop_glue and tr_fundef src_drop tgt_drop *)
    exploit find_funct_match. eauto.
    eapply inj_stbls_match. eauto.
    instantiate (2 := Vptr mb Ptrofs.zero). simpl.
    destruct Ptrofs.eq_dec; try congruence.
    eapply Genv.find_funct_ptr_iff. eauto.
    econstructor. eauto.
    erewrite Ptrofs.add_zero_l. reflexivity.
    intros (tgt_drop & TFINDFUNC & TRFUN).
    (* 4. use generate_drops_inv to prove tgt_drop is the same as the
    result of drop_glue_for_composite *)
    inv TRFUN. inv H0. congruence.
    rewrite GLUEID in H. inv H.
    simpl in H2.
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eauto. eauto. rewrite COENUM.
    simpl. intros (union_id & tag_fid & union_fid & tco & uco & DGLUE & TCO & TUCO & TAGOFS & UFOFS).
    rename H2 into GETGLUE.    
    inv DGLUE.
    (* alloc stack block in function entry *)
    set (pty := Tpointer (Ctypes.Tstruct comp_id noattr) noattr) in *.
    destruct (Mem.alloc tm 0 (Ctypes.sizeof tce pty)) as [tm1 psb] eqn: ALLOC.
    (* permission of psb *)
    assert (PERMFREE1: Mem.range_perm tm1 psb 0 (Ctypes.sizeof tce pty) Cur Freeable).
    { red. intros.
      eapply Mem.perm_alloc_2; eauto. }
    (* Mem.inject j m tm1 *)
    exploit Mem.alloc_right_inject; eauto. intros MINJ1.
    (* forall ofs, loc_out_of_reach j m psb ofs *)
    generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). intros NVALID.
    assert (OUTREACH1: forall ofs, loc_out_of_reach j m psb ofs).
    { red. intros. intro. eapply NVALID.
      eapply Mem.valid_block_inject_2; eauto. }
    (* store the function argument to (psb,0) *)
    assert (STORETM1: {tm2: mem | Mem.store Mptr tm1 psb 0 (Vptr pb pofs) = Some tm2}).
    { eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
      eapply Mem.valid_access_alloc_same;eauto. lia. unfold Mptr. unfold pty. simpl.
      destruct Archi.ptr64. simpl. lia. simpl. lia.
      eapply Z.divide_0_r. econstructor. }
    destruct STORETM1 as (tm2 & STORETM1).
    (* Mem.inject j m tm2 *)
    exploit Mem.store_outside_inject. eapply MINJ1.
    2: eapply STORETM1. intros.
    eapply Mem.fresh_block_alloc;eauto.
    eapply Mem.valid_block_inject_2;eauto.
    intros MINJ2.       
    (* store does not change permission *)
    assert (PERMFREE2: Mem.range_perm tm2 psb 0 (Ctypes.sizeof tce pty) Cur Freeable).
    red. intros. eapply Mem.perm_store_1; eauto.

    exploit select_switch_sem_match; eauto.
    instantiate (1 := (Efield  (Ederef (Evar param_id pty) (Ctypes.Tstruct comp_id noattr)) union_fid (Tunion union_id noattr))).
    instantiate (1 := (generate_dropm prog)).
    instantiate (1 := (prog_comp_env prog)).
    intros (unused_ts & SEL). 
        
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. right. right.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (comp_id, glue_id). split;auto.
          eapply PTree.elements_correct. auto. }
        eauto.
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. 
        eapply PTree.gss. simpl.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl. eapply star_step.
      (** Start to evaluate the swtich statement *)
      { econstructor.
        (* evaluate switch tag *)
        { instantiate (1 := Vint tag).
          econstructor. econstructor. econstructor.
          econstructor. econstructor. econstructor.
          eapply PTree.gss. eapply Clight.deref_loc_value.
          unfold pty. simpl. eauto.
          instantiate (1 := pofs). instantiate (1 := pb).
          simpl. erewrite Mem.load_store_same with (v:= Vptr pb pofs).
          auto. eauto.
          simpl. eapply Clight.deref_loc_copy. auto.
          simpl. eauto. simpl. eauto.
          eauto. rewrite Ptrofs.add_zero.
          simpl. eapply Clight.deref_loc_value.
          simpl. eauto.
          inv VINJ1.
          exploit Mem.loadv_inject. eapply MINJ2. eauto. eauto.
          intros (v2 & TLOAD & VINJ2). inv VINJ2.
          auto. }
        simpl. unfold Ctypes.type_int32s, sem_switch_arg. simpl. eauto. }
      eapply star_step.
      (* evaluate switch *)
      rewrite SEL.
      econstructor. eapply star_step.
      econstructor. eapply star_refl.
      1-8 : eauto.

    + eapply match_dropstate_enum with (bs := nil); eauto.
      econstructor; eauto.
      unfold pty.
      set (param := (Ederef (Evar param_id (Tpointer (Ctypes.Tstruct comp_id noattr) noattr))
                       (Ctypes.Tstruct comp_id noattr))).
      (** FIXME (adhoc): prove match_dropmemb_stmt *)
      { unfold type_to_drop_member_state. simpl.
        destruct (own_type (prog_comp_env prog) fty); try econstructor.
        unfold drop_glue_for_type.
        destruct (drop_glue_children_types fty) eqn: CHILDTYS.
        econstructor.
        assert (ENUMCON: enum_consistent comp_id fid union_id union_fid).
        { unfold enum_consistent. simpl in SCO. unfold ce. rewrite SCO.
          intros. inv H. exists tco, uco.
          split. unfold tce. auto. split. unfold tce. auto.
          auto. intros. eapply UFOFS. eauto. }
        destruct t; try econstructor; eauto.
        destruct ((generate_dropm prog) ! i) eqn: DM.
        set (field_param := (Efield (Efield param union_fid (Tunion union_id noattr)) fid (to_ctype fty))).
        econstructor. eauto. eauto. eauto.
        eauto. econstructor.
        destruct ((generate_dropm prog) ! i) eqn: DM.
        set (field_param := (Efield (Efield param union_fid (Tunion union_id noattr)) fid (to_ctype fty))).
        econstructor. eauto. eauto. eauto.
        eauto. econstructor. }
      (* prove inj_incr *)
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      (* prove loadv in match_cont *)
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr pb pofs)). eauto. eauto.
      intros. inv H.
            
  (* step_dropstate (in struct) *)
  - eapply step_drop_simulation. eauto.
    eapply match_dropstate_struct; eauto.
  (* step_dropstate (in enum) *)
  - eapply step_drop_simulation. eauto.
    eapply match_dropstate_enum; eauto.

  (* step_storagelive *)
  - admit.
  (* step_storagedead *)
  - admit.

  (* step_call *)
  - inv MSTMT. simpl in H4.
    monadInv_comb H4. monadInv_sym EQ3. unfold gensym in EQ2. inv EQ2.
    inv EQ4. destruct g. simpl in H6. inv H6. eapply list_cons_neq in H5.
    contradiction.
    admit.

  (* step_internal_function *)
  - (* how to prove tr_function f tf because we should guarantee that
    f is not a drop glue *)
    assert (MSTBL: Genv.match_stbls j se tse). {   
      destruct w. inv GE. simpl in *. inv INCR. 
      eapply Genv.match_stbls_incr; eauto. 
      (* disjoint *)
      intros. exploit H7; eauto. intros (A & B). split; eauto. }
    
    edestruct find_funct_match as (tfd & FINDT & TF); eauto.
    inv TF. inv H1;try congruence.

    (* function entry inject *)
    exploit function_entry_inject; eauto.
    intros (j' & te & tm' & TENTRY & MENV1 & MINJ1 & INCR1).
    exists (Clight.State tf tf.(Clight.fn_body) tk te (create_undef_temps (fn_temps tf)) tm').
    (* step and match states *)
    split.
    + eapply plus_one. econstructor;eauto.
    + econstructor.
      (* initial env is well_formed *)
      eapply function_entry_wf_env. eauto. eauto.
      eapply tr_function_normal;eauto.
      eauto.
      instantiate (1 := j'). admit.   (* inject_incr and match_cont *)
      eauto.
      etransitivity;eauto. auto.
      
  (* step_external_function *)
  - admit.

  (* step_return_0 *)
  - admit.
  (* step_return_1 *)
  - admit.
  (* step_skip_call *)
  - admit.
  (* step_returnstate *)
  - admit.
  (* step_seq *)
  - admit.
  (* step_skip_seq *)
  - admit.
  (* step_continue_seq *)
  - admit.
  (* step_break_seq *)
  - admit.
  (* step_ifthenelse *)
  - admit.
  (* step_loop *)
  - admit.
  (* step_skip_or_continue_loop *)
  - admit.
  (* step_break_loop *)
  - admit.
        
Admitted.

    
Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, Clight.final_state R r2 /\ match_reply (cc_c inj) w r1 r2.
Admitted.

Lemma external_states_simulation:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, Clight.at_external tge R q2 /\ cc_c_query inj wx q1 q2 /\ match_stbls inj wx se tse /\
  forall r1 r2 S', match_reply (cc_c inj) wx r1 r2 -> after_external S r1 S' ->
  exists R', Clight.after_external R r2 R' /\ match_states S' R'.
Admitted.


End PRESERVATION.

Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (cc_c inj) (cc_c inj) (RustIR.semantics prog) (Clight.semantics1 tprog).
Proof.
  fsim eapply forward_simulation_plus. 
  - inv MATCH. auto.
  - intros. destruct Hse, H. simpl.
    eapply is_internal_match. eapply MATCH.
    eauto.
    (* tr_fundef relates internal function to internal function *)
    intros. inv H3;auto.
    auto. auto.
  (* initial state *)
  - eapply initial_states_simulation; eauto. 
  (* final state *)
  - eapply final_states_simulation; eauto.
  (* external state *)
  - eapply external_states_simulation; eauto.
  (* step *)
  - eapply step_simulation;eauto.
Qed.
