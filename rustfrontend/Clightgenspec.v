Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight.
Require Import Rusttypes RustlightBase RustIR.
Require Import Clightgen.

Import ListNotations.

(* monadInv for bind_res and bind and bind_res *)

(** ** Properties of the monad *)

Remark bind_inversion_sym:
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator),
  bind f g z1 = Res y z3 ->
  exists x, exists z2, 
  f z1 = Res x z2 /\ g x z2 = Res y z3.
Proof.
  intros until z3. unfold bind. destruct (f z1).
  congruence.
  caseEq (g a g'); intros; inv H0.
  econstructor; econstructor; eauto.
Qed.

Remark bind2_inversion_sym:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C) (y: C
    ) (z1 z3: generator),
  bind2 f g z1 = Res y z3 ->
  exists x1, exists x2, exists z2,
  f z1 = Res (x1,x2) z2 /\ g x1 x2 z2 = Res y z3.
Proof.
  unfold bind2. intros.
  exploit bind_inversion_sym; eauto.
  intros [[x1 x2] [z2]]. 
  exists x1; exists x2; exists z2; auto.
Qed.

Ltac monadInv_sym1 H :=
  match type of H with
  | (Res _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _) =>
      inversion H
  | (bind ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let z := fresh "z" in (                           
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion_sym _ _ F G X Z Z' H) as [x [z [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
   | (bind2 ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion_sym _ _ _ F G X Z Z' H) as [x [y [z [EQ1 EQ2]]]];
      clear H;
      try (monadInv1 EQ2))))))
  | (match ?X with left _ => _ | right _ => error _ end = OK _) =>
      destruct X; [try (monadInv_sym1 H) | discriminate]
  end.

Ltac monadInv_sym H :=
  match type of H with
  | (@ret _ _ _ = Res _ _) => monadInv_sym1 H
  | (@error _ _ _ = Res _ _) => monadInv_sym1 H
  | (bind ?F ?G ?Z = Res ?X ?Z') => monadInv_sym1 H
  | (bind2 ?F ?G ?Z = Res ?X ?Z') => monadInv_sym1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  end.


Remark bind_inversion_comb:
  forall (A B: Type) (f: Errors.res A) (g: A -> mon B) (y: B) (z1 z3: generator),
  bind_res f g z1 = Res y z3 ->
  exists x, 
  f = OK x /\ g x z1 = Res y z3.
Proof.
  intros until z3. unfold bind_res. destruct f.
  caseEq (g a z1); intros; inv H0.
  econstructor; econstructor; eauto.
  congruence.
Qed.

Remark bind2_inversion_comb:
  forall (A B C: Type) (f: Errors.res (A*B)) (g: A -> B -> mon C) (y: C
    ) (z1 z3: generator),
  bind_res2 f g z1 = Res y z3 ->
  exists x1, exists x2,
  f = OK (x1,x2) /\ g x1 x2 z1 = Res y z3.
Proof.
  unfold bind_res2. intros.
  exploit bind_inversion_comb; eauto.
  intros [[x1 x2]]. 
  exists x1; exists x2;  auto.
Qed.

Ltac monadInv_comb1 H :=
  match type of H with
  | (Res _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _) =>
      inversion H
  | (bind_res ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let z := fresh "z" in (                           
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion_comb _ _ F G X Z Z' H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv_comb1 EQ2)))))
  | (bind_res2 ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion_comb _ _ _ F G X Z Z' H) as [x [y [EQ1 EQ2]]];
      clear H;
      try (monadInv_comb1 EQ2))))))
  | (match ?X with left _ => _ | right _ => error _ end = OK _) =>
      destruct X; [try (monadInv_comb1 H) | discriminate]
  end.

Ltac monadInv_comb H :=
  match type of H with
  | (@ret _ _ _ = Res _ _) => monadInv_comb1 H
  | (@error _ _ _ = Res _ _) => monadInv_comb1 H
  | (bind_res ?F ?G ?Z = Res ?X ?Z') => monadInv_comb1 H
  | (bind_res2 ?F ?G ?Z = Res ?X ?Z') => monadInv_comb1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  end.


Definition tr_composite_env (ce: composite_env) (tce: Ctypes.composite_env) : Prop :=
  forall id co, ce!id = Some co ->        
         match co.(co_sv) with
         | Struct =>
             exists tco, tce!id = Some tco /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             map transl_composite_member co.(co_members) = tco.(Ctypes.co_members) /\
             (* co.(co_attr) = tco.(Ctypes.co_attr) /\ *)
             co.(co_sizeof) = tco.(Ctypes.co_sizeof) /\
             co.(co_alignof) = tco.(Ctypes.co_alignof) /\
             co.(co_rank) = tco.(Ctypes.co_rank)
         | TaggedUnion =>
             exists tco union_id tag_fid union_fid union,
             let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
             let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in
             let m := (map transl_composite_member co.(co_members)) in
             tce!id = Some tco /\ tce!union_id = Some union /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             tco.(Ctypes.co_members) = [tag_member; union_member] /\
             tag_fid <> union_fid /\
             tco.(Ctypes.co_sizeof) = co.(co_sizeof) /\
             tco.(Ctypes.co_alignof) = co.(co_alignof) /\
             tco.(Ctypes.co_rank) = co.(co_rank) /\
             union.(Ctypes.co_su) = Union /\
             union.(Ctypes.co_members) = m /\
             (* To specify *)
             union.(Ctypes.co_sizeof) = align (Ctypes.sizeof_composite tce Union m) (Ctypes.alignof_composite tce m) /\
             union.(Ctypes.co_alignof) = (Ctypes.alignof_composite tce m) /\
             union.(Ctypes.co_rank) = Ctypes.rank_members tce m
         end.

Lemma alignof_match: forall ce tce ty,
      tr_composite_env ce tce ->
      Ctypes.alignof tce (to_ctype ty) = alignof ce ty.
Admitted.

Lemma sizeof_match: forall ce tce ty,
    tr_composite_env ce tce ->
    Ctypes.sizeof tce (to_ctype ty) = sizeof ce ty.
Admitted.


Lemma field_offset_rec_match: forall ce tce membs fid ofs bf start,
    tr_composite_env ce tce ->
    field_offset_rec ce fid membs start = OK (ofs, bf) ->
    Ctypes.field_offset_rec tce fid (map transl_composite_member membs) start = OK (ofs, Full).
Proof.
  induction membs; simpl; intros fid ofs bf start TR FOFS.
  inv FOFS.
  destruct a. simpl in *.  
  destruct (ident_eq fid id). subst.
  unfold Ctypes.bitalignof, bitalignof in *. inv FOFS.
  erewrite alignof_match; eauto. 
  erewrite IHmembs;eauto.
  unfold Ctypes.bitalignof, Ctypes.bitsizeof.
  erewrite alignof_match; eauto. erewrite sizeof_match; eauto.
Qed.

Lemma field_offset_match: forall ce tce membs fid ofs bf,
    tr_composite_env ce tce ->
    field_offset ce fid membs = OK (ofs, bf) ->
    Ctypes.field_offset tce fid (map transl_composite_member membs) = OK (ofs, Full).
Proof.
  unfold Ctypes.field_offset, field_offset.
  intros.
  eapply field_offset_rec_match with (start := 0); eauto.
Qed.

Lemma struct_field_offset_match: forall ce tce id fid co ofs bf,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    co.(co_sv) = Struct ->
    field_offset ce fid co.(co_members) = OK (ofs, bf) ->
    exists tco, tce ! id = Some tco /\
           Ctypes.field_offset tce fid tco.(Ctypes.co_members) = OK (ofs, Full).
Proof.
  intros until bf.
  intros TR CO STRUCT FOFS.
  red in TR. generalize (TR id co CO).
  rewrite STRUCT. intros (tco & A & B & C & D).
  exists tco. split; auto.
  rewrite <- C.
  eapply field_offset_match; eauto.
Qed.

Lemma alignof_composite_match: forall ce tce ms,
    tr_composite_env ce tce ->
    Ctypes.alignof_composite tce (map transl_composite_member ms) = alignof_composite' ce ms.
Proof.
  induction ms; intros; simpl; auto.
  rewrite IHms. destruct a. simpl.
  erewrite alignof_match. eauto.
  auto. auto.
Qed.

Lemma union_field_offset_eq: forall ms tce fid,
    existsb (fun m : member => ident_eq fid (name_member m)) ms = true ->
    union_field_offset tce fid (map transl_composite_member ms) = OK (0, Full).
Proof.
  induction ms; simpl. congruence.
  intros tce fid. destruct a. simpl.
  destruct (ident_eq fid id); simpl.
  intros. rewrite align_same. f_equal.
  unfold Ctypes.bitalignof.
  generalize  (Ctypes.alignof_pos tce (to_ctype t)). lia.
  eapply Z.divide_0_r.
  eauto.
Qed.

Lemma variant_field_offset_match: forall ce tce co bf id,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    co.(co_sv) = TaggedUnion ->
    exists tco union_id tag_fid union_fid union,
      let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
      let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in
      tce!id = Some tco /\ tce!union_id = Some union /\
        tco.(Ctypes.co_members) = [tag_member; union_member] /\
        tag_fid <> union_fid /\
        (forall fid ofs, variant_field_offset ce fid co.(co_members) = OK (ofs, bf) ->
                    exists ofs1 ofs2,
                      Ctypes.field_offset tce union_fid tco.(Ctypes.co_members) = OK (ofs1, Full)
                      /\ union_field_offset tce fid union.(Ctypes.co_members) = OK (ofs2, Full)
                      /\ ofs = ofs1 + ofs2)
.
Proof.
  intros until id. intros TR CO ENUM.
  generalize (TR id co CO). rewrite ENUM.
  intros (tco & union_id & tag_fid & union_fid & union & A & B & C & D & E & F & G & H & I & J & K & L & M).
  exists tco, union_id, tag_fid, union_fid, union. simpl.
  repeat split;auto.
  unfold variant_field_offset.
  intros fid ofs.
  destruct (existsb (fun m : member => ident_eq fid (name_member m)) (co_members co)) eqn: EB; try congruence.
  intros. inv H0.
  exists (align 32 (alignof_composite' ce (co_members co) * 8) / 8), 0.
  split; try split.
  - rewrite D. unfold Ctypes.field_offset.
    simpl.
    destruct (ident_eq union_fid tag_fid). subst. contradiction.
    destruct (ident_eq union_fid union_fid); try contradiction.
    unfold Ctypes.bitalignof. simpl.
    rewrite B. unfold Ctypes.align_attr. simpl.
    rewrite L. 
    erewrite alignof_composite_match. unfold Ctypes.bitsizeof.
    simpl. eauto.
    auto.
  - rewrite J. eapply union_field_offset_eq. auto.
  - lia.
Qed.    
          
    
Lemma transl_composites_meet_spec: forall co_defs tco_defs ce tce,
    transl_composites co_defs = Some tco_defs ->
    build_composite_env co_defs = OK ce ->
    Ctypes.build_composite_env tco_defs = OK tce ->
    tr_composite_env ce tce.
Admitted.

Section SPEC.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.
Variable dropm: PTree.t ident.
Variable glues: PTree.t Clight.function.

Inductive tr_stmt : statement -> Clight.statement -> Prop :=
(* We only require there **exists** a [tce] which satisfies the
tr_composite relation *)
| tr_trivial: forall s ts g,
    transl_stmt ce tce dropm s g = Res ts g ->
    tr_stmt s ts
| tr_box: forall p e stmt lhs e' temp temp_ty deref_ty,
    temp_ty = to_ctype (typeof_place p) ->
    deref_ty = to_ctype (deref_type (typeof_place p)) ->
    transl_Sbox ce tce temp temp_ty deref_ty e = OK (stmt, e') ->
    place_to_cexpr ce tce p = OK lhs ->
    tr_stmt (Sbox p e) (Clight.Ssequence stmt (Clight.Sassign lhs e'))
| tr_call: forall p e l temp e' l' assign pe,
    expr_to_cexpr_list ce tce l = OK l' ->
    expr_to_cexpr ce tce e = OK e' ->
    place_to_cexpr ce tce p = OK pe ->
    assign = Clight.Sassign pe (Etempvar temp (to_ctype (typeof_place p))) ->
    tr_stmt (Scall p e l) (Clight.Ssequence (Clight.Scall (Some temp) e' l') assign)
| tr_drop: forall p set_stmt drop_stmt temp pe,
    set_stmt = Clight.Sset temp (Eaddrof pe (Tpointer (to_ctype (typeof_place p)) noattr)) ->
    place_to_cexpr ce tce p = OK pe ->
    expand_drop ce dropm temp (typeof_place p) = Some drop_stmt ->
    tr_stmt (Sdrop p) (Clight.Ssequence set_stmt drop_stmt)
| tr_seq: forall s1 s2 s1' s2',
    tr_stmt s1 s1' ->
    tr_stmt s2 s2' ->
    tr_stmt (Ssequence s1 s2) (Clight.Ssequence s1' s2')
| Sifthenelse: forall e e' s1 s2 s1' s2',
    expr_to_cexpr ce tce e = OK e' ->
    tr_stmt s1 s1' ->
    tr_stmt s2 s2' ->
    tr_stmt (Sifthenelse e s1 s2) (Clight.Sifthenelse e' s1' s2')
  | Sloop: forall s s',
      tr_stmt s s' ->
      tr_stmt (Sloop s) (Clight.Sloop s' Clight.Sskip)
.

Inductive tr_function: function -> Clight.function -> Prop :=
| tr_function_normal: forall f tf
    (* It is necessary to prove te!drop_id = None in eval_Evar_global *)
    (WFNAMES: list_disjoint (var_names (f.(fn_params) ++ f.(fn_vars))) (malloc_id :: free_id :: (map snd (PTree.elements dropm)))),
    f.(fn_drop_glue) = None ->
    tr_stmt f.(fn_body) tf.(Clight.fn_body) ->
    Clight.fn_return tf = to_ctype (fn_return f) ->
    Clight.fn_callconv tf = fn_callconv f ->
    Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) ->
    Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) ->
    tr_function f tf
(* | tr_function_drop_glue1: forall f tf comp_id, *)
(*     f.(fn_drop_glue) = Some comp_id -> *)
(*     glues!comp_id = None -> *)
(*     tr_stmt f.(fn_body) tf.(Clight.fn_body) -> *)
(*     Clight.fn_return tf = to_ctype (fn_return f) -> *)
(*     Clight.fn_callconv tf = fn_callconv f -> *)
(*     Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) -> *)
(*     Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) -> *)
(*     tr_function f tf *)
| tr_function_drop_glue: forall f comp_id glue,
    f.(fn_drop_glue) = Some comp_id ->
    (* We can ensure that every composite has a drop glue in Clightgen
    because if ce!id = Some co and tr_composite ce tce then
    drop_glue_for_composite does not return None *)
    glues!comp_id = Some glue ->
    tr_function f glue
.

End SPEC.

Record clgen_env : Type :=
  { clgen_src_cenv: Rusttypes.composite_env;
    clgen_tgt_cenv: Ctypes.composite_env;
    clgen_dropm: PTree.t ident;
    clgen_glues: PTree.t Clight.function }.
                         
Definition build_clgen_env (p: RustIR.program) (tp: Clight.program) : clgen_env :=
  let dropm := generate_dropm p in
  let glues := generate_drops p.(prog_comp_env) tp.(Ctypes.prog_comp_env) dropm in
  Build_clgen_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env) dropm glues.

Inductive tr_fundef (ctx: clgen_env): fundef -> Clight.fundef -> Prop :=
| tr_internal: forall f tf,
    tr_function ctx.(clgen_src_cenv) ctx.(clgen_tgt_cenv) ctx.(clgen_dropm) ctx.(clgen_glues) f tf ->
    tr_fundef ctx (Internal f) (Ctypes.Internal tf)
| tr_external_malloc: forall targs tres cconv orgs rels,
    tr_fundef ctx (External orgs rels EF_malloc targs tres cconv) malloc_decl
| tr_external_free: forall targs tres cconv orgs rels,
    tr_fundef ctx (External orgs rels EF_free targs tres cconv) free_decl
| tr_external: forall ef targs tres cconv orgs rels,
    ef <> EF_malloc /\ ef <> EF_free ->
    tr_fundef ctx (External orgs rels ef targs tres cconv) (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv).


Lemma generate_dropm_inv: forall p id gid,
    (generate_dropm p) ! id = Some gid ->
    exists f, (prog_defmap p) ! gid = Some (Gfun (Internal f)) /\ f.(fn_drop_glue) = Some id.
Admitted.

(* Is it enough? *)
Lemma generate_drops_inv: forall ce tce dropm id co f,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    (generate_drops ce tce dropm) ! id = Some f ->
    let co_ty := Ctypes.Tstruct id noattr in
    let param_ty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id param_ty) co_ty in
    match co.(co_sv) with
    | Struct =>
        let stmt_list := drop_glue_for_members ce dropm deref_param co.(co_members) in
        f = {| Clight.fn_return := Tvoid;
              Clight.fn_callconv := cc_default;
              Clight.fn_params := [(param_id, param_ty)];
              Clight.fn_vars := [];
              fn_temps := [];
              Clight.fn_body := Clight.Ssequence Clight.Sskip stmt_list |}
    | TaggedUnion =>
        exists union_id tag_fid union_fid tco uco,
        let get_tag := Efield deref_param tag_fid Ctypes.type_int32s in
        let get_union := Efield deref_param union_fid (Tunion union_id noattr) in
        let drop_switch_branches :=
          (make_labelled_drop_stmts ce dropm get_union 0 co.(co_members)) in
        let stmt := Sswitch get_tag drop_switch_branches in
        f = {| Clight.fn_return := Tvoid;
              Clight.fn_callconv := cc_default;
              Clight.fn_params := [(param_id, param_ty)];
              Clight.fn_vars := [];
              fn_temps := [];
              Clight.fn_body := stmt |}
        (* compute the field offset *)
        /\ tce ! id = Some tco
        /\ tce ! union_id = Some uco
        (* tag field offset is 0 *)
        /\ Ctypes.field_offset tce tag_fid tco.(Ctypes.co_members) = OK (0, Full)        
        /\ (forall fid ofs bf,
              variant_field_offset ce fid co.(co_members) = OK (ofs, bf) ->
              exists ofs1 ofs2,
                Ctypes.field_offset tce union_fid tco.(Ctypes.co_members) = OK (ofs1, Full)
                /\ Ctypes.union_field_offset tce fid uco.(Ctypes.co_members) = OK (ofs2, Full)
                /\ ofs = ofs1 + ofs2)
    end.
Admitted.

Lemma select_switch_sem_match_aux: forall ce dropm param membs tag memb idx,
    list_nth_z membs (tag - idx) = Some memb ->
    exists s, seq_of_labeled_statement (select_switch tag (make_labelled_drop_stmts ce dropm param idx membs)) = (Clight.Ssequence (Clight.Ssequence (drop_glue_for_member ce dropm param memb) Clight.Sbreak) s).
Proof.
  induction membs.
  simpl. congruence.
  simpl. intros. destruct zeq in H.
  assert (tag = idx) by lia. inv H.
  unfold select_switch. simpl. rewrite zeq_true.
  simpl. eauto.
  unfold select_switch. simpl.
  rewrite zeq_false; try lia.
  assert (Z.pred (tag - idx) = tag - (idx + 1)) by lia. rewrite H0 in *.
  exploit IHmembs.
  eauto. 
  intros (s & A).
  unfold select_switch in A.
  destruct (select_switch_case tag (make_labelled_drop_stmts ce dropm param (idx + 1) membs)) eqn: SEL.
  eauto. eauto.
Qed.

Lemma select_switch_sem_match: forall ce dropm param membs tag memb,
    list_nth_z membs tag = Some memb ->
    exists s, seq_of_labeled_statement (select_switch tag (make_labelled_drop_stmts ce dropm param 0 membs)) = (Clight.Ssequence (Clight.Ssequence (drop_glue_for_member ce dropm param memb) Clight.Sbreak) s).
Proof.
  intros. 
  eapply select_switch_sem_match_aux. rewrite Z.sub_0_r.
  auto.
Qed.
