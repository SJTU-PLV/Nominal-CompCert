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
             co.(co_attr) = tco.(Ctypes.co_attr) /\
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

Lemma to_ctype_sizeof: forall ce tce ty cty,
    to_ctype ty = cty ->
    tr_composite_env ce tce ->
    sizeof ce ty = Ctypes.sizeof tce cty.
Admitted.

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
| tr_box: forall p e stmt lhs e' temp temp_ty,
    temp_ty = Tpointer (to_ctype (typeof e)) noattr ->
    transl_Sbox ce tce temp temp_ty e = OK (stmt, e') ->
    place_to_cexpr tce p = OK lhs ->
    tr_stmt (Sbox p e) (Clight.Ssequence stmt (Clight.Sassign lhs e'))
| tr_call: forall p e l temp e' l' assign pe,
    expr_to_cexpr_list ce tce l = OK l' ->
    expr_to_cexpr ce tce e = OK e' ->
    place_to_cexpr tce p = OK pe ->
    assign = Clight.Sassign pe (Etempvar temp (to_ctype (typeof_place p))) ->
    tr_stmt (Scall p e l) (Clight.Ssequence (Clight.Scall (Some temp) e' l') assign)
| tr_drop: forall p set_stmt drop_stmt temp pe,
    set_stmt = Clight.Sset temp (Eaddrof pe (Tpointer (to_ctype (typeof_place p)) noattr)) ->
    expand_drop dropm temp (typeof_place p) = Some drop_stmt ->
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
| tr_function_normal: forall f tf,
    f.(fn_drop_glue) = None ->
    tr_stmt f.(fn_body) tf.(Clight.fn_body) ->
    Clight.fn_return tf = to_ctype (fn_return f) ->
    Clight.fn_callconv tf = fn_callconv f ->
    Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) ->
    Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) ->
    tr_function f tf
| tr_function_drop_glue1: forall f tf comp_id,
    f.(fn_drop_glue) = Some comp_id ->
    dropm!comp_id = None ->
    tr_stmt f.(fn_body) tf.(Clight.fn_body) ->
    Clight.fn_return tf = to_ctype (fn_return f) ->
    Clight.fn_callconv tf = fn_callconv f ->
    Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) ->
    Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) ->
    tr_function f tf
| tr_function_drop_glue2: forall f comp_id glue_id glue,
    f.(fn_drop_glue) = Some comp_id ->
    dropm!comp_id = Some glue_id ->
    glues!glue_id = Some glue ->
    tr_function f glue
.

End SPEC.

Inductive tr_fundef (p: program): fundef -> Clight.fundef -> Prop :=
| tr_internal: forall f tf tce co_defs,
    let dropm := generate_dropm p in
    let glues := generate_drops p.(prog_comp_env) tce p.(prog_types) dropm in
    transl_composites p.(prog_types) = Some co_defs ->
    Ctypes.build_composite_env co_defs = OK tce ->
    tr_function p.(prog_comp_env) tce dropm glues f tf ->
    tr_fundef p (Internal f) (Ctypes.Internal tf)
| tr_external_malloc: forall targs tres cconv orgs rels,
    tr_fundef p (External orgs rels EF_malloc targs tres cconv) malloc_decl
| tr_external_free: forall targs tres cconv orgs rels,
    tr_fundef p (External orgs rels EF_free targs tres cconv) free_decl
| tr_external: forall ef targs tres cconv orgs rels,    
    tr_fundef p (External orgs rels ef targs tres cconv) (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv).


Lemma tr_fundef_linkorder: forall c c' f tf,
    tr_fundef c f tf ->
    linkorder c c' ->
    tr_fundef c' f tf.
Proof.
  intros until tf. intros TR ((MAIN & PUBLIC & GDEF) & COMP).
  clear MAIN PUBLIC GDEF.
  inv TR.
  - econstructor.
    inv H. (* econstructor; eauto.     *)
    (** UNPROVABLE! Because c' may contain more enum and we cannot
    ensure that the generated id of the union is compatable. Try to
    add linkorder in match_states *)
    
Admitted.

