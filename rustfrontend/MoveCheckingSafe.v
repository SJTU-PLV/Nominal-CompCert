Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustIR RustIRcfg.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown MoveChecking.
Require Import Wfsimpl.

Import ListNotations.

(* Some simple type checking (move to Rusttyping.v) *)

Definition type_deref (ty: type) : res type :=
  match ty with
  (* Only support box type to be dereferenced for now *)
  | Tbox tyelt => OK tyelt
  (* | Treference _ _ tyelt => OK tyelt *)
  | _ => Error (msg "type_deref error")
  end.

Lemma type_deref_some: forall ty1 ty2,
    type_deref ty1 = OK ty2 ->
    ty1 = Tbox ty2.
Proof.
  destruct ty1; intros; simpl in *; try congruence.
Qed.

      
Definition typenv := PTree.t type.

Section TYPING.

Variable te: typenv.
Variable ce: composite_env.

Inductive wt_place : place -> Prop :=
| wt_local: forall id ty
    (WT1: te ! id = Some ty),
    wt_place (Plocal id ty)
| wt_deref: forall p ty
    (WT1: wt_place p)
    (WT2: type_deref (typeof_place p) = OK ty),
    wt_place (Pderef p ty)
| wt_field: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tstruct orgs id)
    (WT3: ce ! id = Some co)
    (WT4: field_type fid co.(co_members) = OK ty)
    (WT5: co.(co_sv) = Struct),
    wt_place (Pfield p fid ty)
| wt_downcast: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tvariant orgs id)
    (WT3: ce ! id = Some co)
    (WT4: field_type fid co.(co_members) = OK ty)
    (WT5: co.(co_sv) = TaggedUnion),
    wt_place (Pdowncast p fid ty).

Inductive wt_pexpr: pexpr -> Prop :=
| wt_Eunit:
  wt_pexpr Eunit.

Inductive wt_expr: expr -> Prop :=
| wt_move_place: forall p
    (WT1: wt_place p)
    (SCALAR: scalar_type (typeof_place p) = false),
    wt_expr (Emoveplace p (typeof_place p))
| wt_pure_expr: forall pe
    (SCALAR: scalar_type (typeof_pexpr pe) = true)
    (WT1: wt_pexpr pe),
    wt_expr pe
.


Inductive wt_stmt: statement -> Prop :=
| wt_Sassign: forall p e
    (WT1: wt_place p)
    (WT2: wt_expr e),
    (* Require the type of p equal to the type of e? *)
    wt_stmt (Sassign p e).
    
(* Well-typed continuation and state *)

Inductive wt_cont: cont -> Prop :=
| wt_Kseq: forall s k
    (WT1: wt_stmt s)
    (WT2: wt_cont k),
    wt_cont (Kseq s k).

End TYPING.

Coercion env_to_tenv (e: env) : typenv :=
  PTree.map1 snd e.

Inductive wt_state (ce: composite_env) : state -> Prop :=
| wt_regular_state: forall f s k (e: env) own m
    (WT1: wt_stmt e ce s)                  
    (WT2: wt_cont e ce k),
    wt_state ce (State f s k e own m)
| wt_dropplace_state: forall f st drops k own m (e: env)
    (WT1: Forall (fun p => wt_place e ce p) (map fst drops)),
    wt_state ce (Dropplace f st drops k e own m)
.


(* The prefix of a well typed place is also well typed  *)

Lemma wt_place_prefix: forall p2 p1 ce e,
    is_prefix p1 p2 = true ->
    wt_place e ce p2 ->
    wt_place e ce p1.
Proof.
  induction p2; intros; unfold is_prefix in H at 1; simpl in *.
  - inv H0. destruct place_eq; subst; simpl in *; try congruence.
    constructor. auto.
  - inv H0. destruct place_eq; simpl in H; try congruence.
    + subst. econstructor; eauto.
    + destruct place_eq in H; simpl in H; try congruence.
      destruct in_dec in H; simpl in H; try congruence.
      eapply IHp2. unfold is_prefix.
      destruct in_dec; simpl; try congruence. eapply orb_true_r.
      auto.
  - inv H0. destruct place_eq; simpl in H; try congruence.
    + subst. econstructor; eauto.
    + destruct place_eq in H; simpl in H; try congruence.
      destruct in_dec in H; simpl in H; try congruence.
      eapply IHp2. unfold is_prefix.
      destruct in_dec; simpl; try congruence. eapply orb_true_r.
      auto.
  - inv H0. destruct place_eq; simpl in H; try congruence.
    + subst. econstructor; eauto.
    + destruct place_eq in H; simpl in H; try congruence.
      destruct in_dec in H; simpl in H; try congruence.
      eapply IHp2. unfold is_prefix.
      destruct in_dec; simpl; try congruence. eapply orb_true_r.
      auto.
Qed.      
    
Lemma get_tenv_some: forall e id ty,
    (env_to_tenv e) ! id = Some ty ->
    exists b, e ! id = Some (b, ty).
Proof.
  intros. unfold env_to_tenv in H. erewrite PTree.gmap1 in H.
  unfold option_map in H. destruct (e!id) eqn: A; try congruence.
  destruct p. simpl in H. inv H. eauto.
Qed.

Lemma sizeof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> size_chunk chunk = sizeof ce ty.
Proof.
  unfold Rusttypes.access_mode; intros.
  assert (size_chunk chunk = sizeof ce ty).
  {
    destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; auto.
  }
  lia.
Qed.

Lemma alignof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> (align_chunk chunk | alignof ce ty).
Proof.
  unfold Rusttypes.access_mode; intros.
  destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; try apply Z.divide_refl.
  exists 2. auto.
  exists 2. auto.
Qed.


(* try to define top-most shallow prefix (whose starting offset of its
address is zero). [p'] is in the offset [ofs] of [p] *)
(* For subplace ce p1 p2 ofs: it means that p2 is in p1 with the
offset [ofs] *)
Inductive subplace (ce: composite_env) (p: place) : place -> Z -> Prop :=
| subplace_eq: subplace ce p p 0
| subplace_field: forall p' ofs orgs id co fofs fid fty
    (* &p‘ = &p + ofs *)
    (SUB: subplace ce p p' ofs)
    (TY: typeof_place p' = Tstruct orgs id)
    (CO: ce ! id = Some co)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs),
    (* &p'.fid = &p + ofs + fofs *)
    subplace ce p (Pfield p' fid fty) (ofs + fofs)
| subplace_downcast: forall p' ofs orgs id co fofs fid fty
    (* &p‘ = &p + ofs *)
    (SUB: subplace ce p p' ofs)
    (TY: typeof_place p' = Tvariant orgs id)
    (CO: ce ! id = Some co)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs),
    subplace ce p (Pdowncast p' fid fty) (ofs + fofs)
.

(* Properties of subplace *)

(* Maybe we should ensure that ce is consistent *)
Lemma subplace_align: forall ce tenv p1 p2 ofs
  (SUBP: subplace ce p1 p2 ofs)
  (WT: wt_place tenv ce p2)
  (CONS: composite_env_consistent ce),
  (alignof ce (typeof_place p2) | ofs).
Proof.
  induction 1; intros.
  - apply Z.divide_0_r.
  - simpl.
    inv WT. rewrite TY in WT2. inv WT2.
    rewrite CO in WT3. inv WT3.
    eapply Z.divide_add_r.
    (* difficult case *)
    + eapply Z.divide_trans.      
      2: { eapply IHSUBP; auto. }
      rewrite TY. simpl in *. rewrite CO.
      (** Prove that the align of composite is align of each field *)
      (* We need to say that ce is consistent *)
      erewrite co_consistent_alignof; eauto.
      (* show that alignof_composite is align of the alignment of
      field type. Because alignof_composite = 2^m and alignment of
      filed type is 2^n where m >= n *)
      exploit alignof_two_p. intros (n & AL). erewrite AL.      
      exploit alignof_composite_two_p. intros (m & COMPAL). erewrite COMPAL.
      do 2 rewrite two_power_nat_equiv in *.
      set (nz:= Z.of_nat n) in *.
      set (mz:= Z.of_nat m) in *.
      assert (LE: nz <= mz).
      { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
        unfold mz. eapply Nat2Z.is_nonneg.
        rewrite <- AL. rewrite <- COMPAL.
        eapply alignof_composite_max. eauto. }
      exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
      rewrite MZEQ. erewrite Z.pow_add_r; auto.
      eapply Z.divide_factor_r.
      unfold nz. eapply Nat2Z.is_nonneg.            
    + eapply field_offset_aligned. eauto. eauto.
  (* Pdowncast: mostly the same as Pfield *)
  - simpl.
    inv WT. rewrite TY in WT2. inv WT2.
    rewrite CO in WT3. inv WT3.
    eapply Z.divide_add_r.
    (* difficult case *)
    + eapply Z.divide_trans.      
      2: { eapply IHSUBP; auto. }
      rewrite TY. simpl in *. rewrite CO.
      erewrite co_consistent_alignof; eauto.
      exploit alignof_two_p. intros (n & AL). erewrite AL.      
      exploit alignof_composite_two_p. intros (m & COMPAL). erewrite COMPAL.
      do 2 rewrite two_power_nat_equiv in *.
      set (nz:= Z.of_nat n) in *.
      set (mz:= Z.of_nat m) in *.
      assert (LE: nz <= mz).
      { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
        unfold mz. eapply Nat2Z.is_nonneg.
        rewrite <- AL. rewrite <- COMPAL.
        eapply alignof_composite_max. eauto. }
      exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
      rewrite MZEQ. erewrite Z.pow_add_r; auto.
      eapply Z.divide_factor_r.
      unfold nz. eapply Nat2Z.is_nonneg.
    (* show that the offset of body field is align with the alignment
    of field type. It is correct because the alignment is computed
    from the alignment of the whole enum *)
    + unfold variant_field_offset in FOFS.
      destruct existsb in FOFS; try congruence. inv FOFS.
      unfold align. erewrite Z.mul_assoc.
      rewrite Z.div_mul.
      assert (MUL: exists k, alignof_composite' ce (co_members co0) =  k * alignof ce fty).
      exploit alignof_two_p. intros (n & AL). erewrite AL.      
      exploit alignof_composite_two_p'. intros (m & COMPAL). erewrite COMPAL.
      do 2 rewrite two_power_nat_equiv in *.
      set (nz:= Z.of_nat n) in *.
      set (mz:= Z.of_nat m) in *.
      assert (LE: nz <= mz).
      { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
        unfold mz. eapply Nat2Z.is_nonneg.
        rewrite <- AL. rewrite <- COMPAL.
        eapply alignof_composite_max_aux. eauto. }
      exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
      rewrite MZEQ. erewrite Z.pow_add_r; auto. eauto.
      unfold nz. eapply Nat2Z.is_nonneg.
      destruct MUL as (k & MUL).
      rewrite MUL.
      rewrite Z.mul_assoc. eapply Z.divide_factor_r.
      lia.
Qed.


Lemma subplace_in_range: forall ce tenv p1 p2 fofs
    (SUBP: subplace ce p1 p2 fofs)
    (CON: composite_env_consistent ce)
    (WT: wt_place tenv ce p2),
    0 <= fofs /\ fofs + sizeof ce (typeof_place p2) <= sizeof ce (typeof_place p1).
Proof.
  intros. induction SUBP.
  - split; lia.
  - simpl.
    inv WT. rewrite TY in WT2. inv WT2. rewrite CO in WT3. inv WT3.
    assert (LE: fofs + sizeof ce fty <= sizeof ce (typeof_place p')).
    { rewrite TY. simpl. rewrite CO.
      erewrite co_consistent_sizeof; eauto.
      rewrite WT5. simpl.
      exploit field_offset_in_range;eauto.      
      assert (ALGE: co_alignof co0 > 0).
      { exploit co_alignof_two_p. intros (n & COAL).
        rewrite COAL. apply two_power_nat_pos. }
      generalize (align_le (sizeof_struct ce (co_members co0)) _ ALGE).
      lia. }
    exploit IHSUBP; eauto. intros (A & B). split.
    exploit field_offset_in_range; eauto. lia.
    lia.    
  - simpl.
    inv WT. rewrite TY in WT2. inv WT2. rewrite CO in WT3. inv WT3.
    assert (LE: fofs + sizeof ce fty <= sizeof ce (typeof_place p')).
    { rewrite TY. simpl. rewrite CO.
      erewrite co_consistent_sizeof; eauto.
      rewrite WT5. simpl.
      exploit variant_field_offset_in_range; eauto.
      assert (ALGE: co_alignof co0 > 0).
      { exploit co_alignof_two_p. intros (n & COAL).
        rewrite COAL. apply two_power_nat_pos. }
      generalize (align_le (sizeof_variant ce (co_members co0)) _ ALGE).
      lia. }
    exploit IHSUBP; eauto. intros (A & B). split.
    exploit variant_field_offset_in_range; eauto. lia.
    lia.    
Qed.

Lemma subplace_upper_bound: forall ce tenv p1 p2 fofs
    (SUBP: subplace ce p1 p2 fofs)
    (CON: composite_env_consistent ce)
    (WT: wt_place tenv ce p2)
    (PSIZE: sizeof ce (typeof_place p1) <= Ptrofs.max_unsigned),
    fofs + sizeof ce (typeof_place p2) <= Ptrofs.max_unsigned.
Proof.
  intros.
  exploit subplace_in_range; eauto.
  lia.
Qed.


(** Definition of footprint *)

(* A tree structured footprint (maybe similar to some separation logic
algebra) *)
Inductive footprint : Type :=
| fp_emp                      (* empty footprint *)
| fp_scalar (ty: type)        (* type must be scalar type  *)
| fp_box (b: block) (sz: Z) (fp: footprint) (* A heap block storing values that occupy footprint fp *)
(* (field ident, field type, field offset,field footprint) *)
| fp_struct (id: ident) (fpl: list (ident * Z * footprint))
(* orgs are not used for now but it is used to relate to the type *)
| fp_enum (id: ident) (orgs: list origin) (tag: Z) (fid: ident) (ofs: Z) (fp: footprint)
.
(* with field_footprint : Type := *)
(* | fp_field (fid: ident) (fty: type) (ofs: Z) (fp: footprint). *)

Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPscalar: forall ty, P (fp_scalar ty))
  (HPbox: forall (b : block) sz (fp : footprint), P fp -> P (fp_box b sz fp))
  (HPstruct: forall id fpl, (forall fid ofs fp, In (fid, ofs, fp) fpl -> P fp) -> P (fp_struct id fpl))
  (HPenum: forall id orgs (tag : Z) fid ofs (fp : footprint), P fp -> P (fp_enum id orgs tag fid ofs fp)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as ((fid1 & ofs1) & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid ofs fp H). 
  - apply HPenum. apply strong_footprint_ind.
Qed.
    
End FP_IND.

(* Footprint used in interface (for now, it is just defined by
support) *)
Definition flat_footprint : Type := list block.

(* Function used to flatten a footprint  *)
Fixpoint footprint_flat (fp: footprint) : flat_footprint :=
  match fp with
  | fp_emp => nil
  | fp_scalar _ => nil
  | fp_box b _ fp' =>
      b :: footprint_flat fp'
  | fp_struct _ fpl =>
      flat_map (fun '(_, _, fp) => footprint_flat fp) fpl
  | fp_enum _ _ _ _ _ fp =>
      footprint_flat fp
  end.

Definition footprint_disjoint (fp1 fp2: footprint) :=
  list_disjoint (footprint_flat fp1) (footprint_flat fp2).

Inductive footprint_disjoint_list : list footprint -> Prop :=
| fp_disjoint_nil: footprint_disjoint_list nil
| fp_disjoint_cons: forall fp fpl,
      list_disjoint (footprint_flat fp) (concat (map footprint_flat fpl)) ->
      footprint_disjoint_list fpl ->
      footprint_disjoint_list (fp::fpl)
.

(* Definition of footprint map *)

Definition fp_map := PTree.t footprint.

(* A footprint in a function frame *)

Definition flat_fp_map (fpm: fp_map) : flat_footprint :=
  concat (map (fun elt => footprint_flat (snd elt)) (PTree.elements fpm)).

(* Definiton of footprint for stack frames *)

(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* The footprint in a module (similar to continuation) *)

Inductive fp_frame : Type :=
| fpf_emp
(* we need to record the footprint of the stack *)
| fpf_func (e: env) (fpm: fp_map) (fpf: fp_frame)
(* use this to record the structure of footprint in dropplace state, rfp is the footprint of the place being dropped *)
| fpf_dropplace (e: env) (fpm: fp_map) (rfp: footprint) (fpf: fp_frame)
(* record the footprint in a drop glue: fp is the footprint being
dropped and fpl is the footprint of the members to be dropped *)
| fpf_drop (fp: footprint) (fpl: list footprint) (fpf: fp_frame)
.

Definition footprint_of_env (e: env) : flat_footprint :=
  map (fun elt => fst (snd elt)) (PTree.elements e).


Fixpoint flat_fp_frame (fpf: fp_frame) : flat_footprint :=
  match fpf with
  | fpf_emp => nil
  | fpf_func e fpm fpf =>
      footprint_of_env e ++ flat_fp_map fpm ++ flat_fp_frame fpf
  | fpf_dropplace e fpm rfp fpf =>
      footprint_of_env e ++ flat_fp_map fpm ++ footprint_flat rfp ++ flat_fp_frame fpf
  | fpf_drop fp fpl fpf =>
      footprint_flat fp ++ concat (map footprint_flat fpl) ++ flat_fp_frame fpf
  end.

Lemma in_footprint_of_env: forall b ty id le,
    le ! id = Some (b, ty) ->
    In b (footprint_of_env le).
Admitted.

Lemma in_footprint_flat_fp_map: forall b fp fpm id,
    fpm ! id = Some fp ->
    In b (footprint_flat fp) ->
    In b (flat_fp_map fpm).
Admitted.

(* Try to define new sem_wt *)

Definition find_fields (fid: ident) (fpl: list (ident * Z * footprint)) : option (ident * Z * footprint) :=
  find (fun '(fid', _, _) => if ident_eq fid fid' then true else false) fpl. 

Definition set_field (fid: ident) (vfp: footprint) (fpl: list (ident * Z * footprint)) : list (ident * Z * footprint) :=
  (map
     (fun '(fid2, fofs2, ffp2) =>
        if ident_eq fid fid2 then (fid2, fofs2, vfp) else (fid2, fofs2, ffp2)) fpl).


Lemma find_fields_some: forall fid fid1 fpl fofs ffp,
    find_fields fid fpl = Some (fid1, fofs, ffp) ->
    fid = fid1 /\ In (fid, fofs, ffp) fpl.
Proof.
  intros. unfold find_fields in H.
  exploit find_some; eauto. intros (A & B).
  destruct ident_eq in B; try congruence.
  subst. auto.
Qed.

Lemma find_fields_different_field: forall fpl fid id fofs ffp vfp,
    id <> fid ->
    find_fields fid (set_field id vfp fpl) = Some (fid, fofs, ffp) ->
    find_fields fid fpl = Some (fid, fofs, ffp).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H0.
  - subst. destruct ident_eq.
    + subst. congruence.
    + eapply IHfpl. eauto. eauto.
  - destruct ident_eq.
    + inv H0. auto.
    + eauto.
Qed.


Lemma find_fields_same_offset: forall fpl fid id fofs ffp vfp,
    find_fields fid (set_field id vfp fpl) = Some (fid, fofs, ffp) ->
    exists vfp1, find_fields fid fpl = Some (fid, fofs, vfp1).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H.
  - subst. destruct ident_eq.
    + inv H. eauto.
    + eapply IHfpl; eauto.
  - destruct ident_eq.
    + inv H. eauto.
    + eauto.
Qed.

Lemma find_fields_same_footprint: forall fpl fid fofs ffp vfp,
    find_fields fid (set_field fid vfp fpl) = Some (fid, fofs, ffp) ->
    vfp = ffp.
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H.
  - subst. destruct ident_eq; auto.
    inv H. auto. eauto.
  - destruct ident_eq.
    + congruence.
    + eauto.
Qed.

Lemma find_fields_set_spec: forall fpl fid1 fid2 fofs ffp vfp,
    find_fields fid1 fpl = Some (fid1, fofs, ffp) ->
    find_fields fid1 (set_field fid2 vfp fpl) = Some (fid1, fofs, if peq fid1 fid2 then vfp else ffp).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p.
  destruct ident_eq in H.
  - subst. inv H. destruct ident_eq; subst.
    + destruct ident_eq; try congruence.
      auto.
    + destruct ident_eq; try congruence.
      destruct peq; try congruence. auto.
  - destruct ident_eq; subst.
    + destruct ident_eq; try congruence.
      erewrite IHfpl; eauto. destruct peq; try congruence.
    + destruct ident_eq; try congruence.
      erewrite IHfpl; eauto.
Qed.

Section COMP_ENV.

Variable ce: composite_env.

(** * Definitions of semantics typedness (TODO: support user-defined semantics types) *)

Definition alignof_comp (id: ident) :=
  match ce ! id with
  | Some co => co_alignof co
  | None => 1
  end.

(* Semantics well typed location is mutually defined with semantics
well typed value *)
Inductive sem_wt_loc (m: mem) : footprint -> block -> Z -> Prop :=
| sem_wt_base: forall ty b ofs chunk v
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (* (NOTBOX: forall ty', ty <> Tbox ty') *)
    (WT: sem_wt_val m (fp_scalar ty) v),
    sem_wt_loc m (fp_scalar ty) b ofs
| sem_wt_box: forall b ofs fp b1 sz1 v
    (LOAD: Mem.load Mptr m b ofs = Some v)
    (WT: sem_wt_val m (fp_box b1 sz1 fp) v),
    sem_wt_loc m (fp_box b1 sz1 fp) b ofs
| sem_wt_struct: forall b ofs fpl id
    (* all fields are semantically well typed *)
    (FWT: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        sem_wt_loc m ffp b (ofs + fofs)),
    sem_wt_loc m (fp_struct id fpl) b ofs
| sem_wt_enum: forall fp b ofs tagz fid fofs id orgs
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc m fp b (ofs + fofs)),
    sem_wt_loc m (fp_enum id orgs tagz fid fofs fp) b ofs

with sem_wt_val (m: mem) : footprint -> val -> Prop :=
| wt_val_unit:
  sem_wt_val m (fp_scalar Tunit) (Vint Int.zero)
| wt_val_int: forall sz si n,
    Cop.cast_int_int sz si n = n ->
    sem_wt_val m (fp_scalar (Tint sz si)) (Vint n)
| wt_val_single: forall n,
    sem_wt_val m (fp_scalar (Tfloat Ctypes.F32)) (Vsingle n)
| wt_val_float: forall n,
    sem_wt_val m (fp_scalar (Tfloat Ctypes.F64)) (Vfloat n)
| wt_val_long: forall si n,
    sem_wt_val m (fp_scalar (Tlong si)) (Vlong n)
| wt_val_box: forall b fp sz
    (** Box pointer must be in the starting point of a block *)
    (* The value stored in (b,0) has type ty and occupies footprint fp *)
    (WTLOC: sem_wt_loc m fp b 0)
    (VALID: Mem.range_perm m b (- size_chunk Mptr) sz Cur Freeable)
    (SIZE: Mem.load Mptr m b (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz))),
    sem_wt_val m (fp_box b sz fp) (Vptr b Ptrofs.zero)
(* TODO *)
(* | wt_val_ref: forall b ofs ty org mut, *)
(*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *)
| wt_val_struct: forall b ofs id fpl
    (WTLOC: sem_wt_loc m (fp_struct id fpl) b (Ptrofs.unsigned ofs))
    (AL: (alignof_comp id | Ptrofs.unsigned ofs)),
    sem_wt_val m (fp_struct id fpl) (Vptr b ofs)
| wt_val_enum: forall b ofs fp tagz fid fofs id orgs
    (WTLOC: sem_wt_loc m (fp_enum id orgs tagz fid fofs fp) b (Ptrofs.unsigned ofs))
    (AL: (alignof_comp id | Ptrofs.unsigned ofs)),
    sem_wt_val m (fp_enum id orgs tagz fid fofs fp) (Vptr b ofs)
.


Inductive sem_wt_val_list (m: mem) : list footprint -> list val -> Prop :=
| sem_wt_val_nil:
  sem_wt_val_list m nil nil
| sem_wt_val_cons: forall fpl fp vl v,
    sem_wt_val_list m fpl vl ->
    sem_wt_val m fp v ->
    sem_wt_val_list m (fp::fpl) (v::vl)
.

Definition member_footprint_rel (wtfp: type -> footprint -> Prop) (co: composite) (memb: member) (f: ident * type * Z * footprint) : Prop :=
  let '(fid, fty, fofs, fp) := f in
  match memb with
  | Member_plain fid1 fty1 => fid = fid1 /\ fty = fty1
                             /\ field_type fid co.(co_members) = OK fty
                             /\ field_offset ce fid co.(co_members) = OK fofs
                             /\ wtfp fty fp
  end.


(* Definition of wt_footprint (well-typed footprint). Intuitively, it
says that the footprint is an abstract form of the syntactic type
ty. We need an intermediate composite_env to act as the recursive
guard to simulate the move checking because we do not allow unbounded
appearence of shallow struct. What if we allow recursive struct in the
footprint but if can be rule out in move checking? *)
Inductive wt_footprint : type -> footprint -> Prop :=
| wt_fp_emp: forall ty
    (* It means that the location with this type is not
        initialized or this location is scalar type *)
    (WF: forall orgs id, ty <> Tstruct orgs id),
    wt_footprint ty fp_emp
| wt_fp_scalar: forall ty
    (WF: scalar_type ty = true),
    wt_footprint ty (fp_scalar ty)
| wt_fp_struct: forall orgs id fpl co
    (CO: ce ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (** TODO: combine WT1 and WT2 elegantly. WT1 is used in getting
    the sub-field's footprint. WT2 is used in proving the properties
    of sub-field's footprint *)
    (WT1: forall fid fty,
        field_type fid co.(co_members) = OK fty ->
        (* For simplicity, use find_field instead of In predicate *)
        exists ffp fofs,
          find_fields fid fpl = Some (fid, fofs, ffp)
          /\ field_offset ce fid co.(co_members) = OK fofs
          (* bound condition *)
          /\ wt_footprint fty ffp)
    (WT2: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        exists fty,
          field_type fid co.(co_members) = OK fty
          /\ field_offset ce fid co.(co_members) = OK fofs
          /\ wt_footprint fty ffp),
    wt_footprint (Tstruct orgs id) (fp_struct id fpl)
| wt_fp_enum: forall orgs id tagz fid fty fofs fp co
    (CO: ce ! id = Some co)
    (ENUM: co_sv co = TaggedUnion)
    (TAG: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty))
    (* avoid some norepet properties *)
    (FTY: field_type fid co.(co_members) = OK fty)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: wt_footprint fty fp),
    wt_footprint (Tvariant orgs id) (fp_enum id orgs tagz fid fofs fp)
| wt_fp_box: forall ty b fp
    (* this is ensured by bm_box *)
    (WT: wt_footprint ty fp),
    wt_footprint (Tbox ty) (fp_box b (sizeof ce ty) fp).


Inductive bmatch (m: mem) (b: block) (ofs: Z) : footprint -> Prop :=
| bm_box: forall b1 fp sz
    (LOAD: Mem.load Mptr m b ofs = Some (Vptr b1 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b1 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (VRES: Mem.range_perm m b1 (- size_chunk Mptr) sz Cur Freeable),
    bmatch m b ofs (fp_box b1 sz fp)
| bm_struct: forall fpl id
    (* all fields are semantically well typed *)
    (FMATCH: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        bmatch m b (ofs + fofs) ffp),
    bmatch m b ofs (fp_struct id fpl)
| bm_enum: forall fp id tagz fid fofs orgs 
    (* Interpret the field by the tag and prove that it is well-typed *)
    (* [p] whose value has footprint (fp_enum tagz fp) is actually has
    tag tagz *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz))) 
    (BM: bmatch m b (ofs + fofs) fp),
    bmatch m b ofs (fp_enum id orgs tagz fid fofs fp)
| bm_scalar: forall ty chunk v
    (* (TY: scalar_type ty = true) *)
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val m (fp_scalar ty) v),
    bmatch m b ofs (fp_scalar ty)
(** TODO: bm_reference  *)
.

End COMP_ENV.


(* Getter and Setter of footprint map  *)

(* Similar to ProjectElem in rustc *)
Variant path : Type :=
  | ph_deref
  | ph_field (fid: ident)
  (* type of the variant here is used in valid_owner proof !! *)
  | ph_downcast (ty: type) (fid: ident) (* (fty: type) *).

Lemma path_eq: forall (p1 p2: path), {p1 = p2} + {p1 <> p2}.
Proof.
  generalize ident_eq type_eq. intros.
  destruct p1; destruct p2; auto; try (right; congruence).
  destruct (ident_eq fid fid0); subst. auto. right. congruence.
  destruct (ident_eq fid fid0); destruct (type_eq ty ty0); subst; auto.
  1-3: right; congruence.
Qed.

Definition paths : Type := (ident * list path).

(* relate place and path *)
Fixpoint path_of_place (p: place) : paths :=
  match p with
  | Plocal id _ =>
      (id, nil)
  | Pderef p1 _ =>
      let (id, phl) := path_of_place p1 in
      (id, phl ++ [ph_deref])
  | Pfield p1 fid _ =>
      let (id, phl) := path_of_place p1 in
      (id, phl ++ [ph_field fid])
  | Pdowncast p1 fid fty =>
      let (id, phl) := path_of_place p1 in
      (id, phl ++ [ph_downcast (typeof_place p1) fid (* fty *)])
  end.

Inductive paths_disjoint : list path -> list path -> Prop :=
| phs_disjoint1: forall p1 p2 l1 l2,
    (* Is it enough to use neq? *)
    p1 <> p2 ->
    paths_disjoint (p1::l1) (p2::l2)
| phs_disjoint2: forall p l1 l2,
    paths_disjoint l1 l2 ->
    paths_disjoint (p::l1) (p::l2).

Lemma paths_disjoint_sym: forall phl1 phl2,
    paths_disjoint phl1 phl2 ->
    paths_disjoint phl2 phl1.
Admitted.

Inductive wt_path ce (ty: type) : list path -> type -> Prop :=
| wt_path_nil: wt_path ce ty nil ty
| wt_path_deref: forall phl ty1 ty2
    (WP1: wt_path ce ty phl ty1)
    (WP2: type_deref ty1 = OK ty2),
    wt_path ce ty (phl ++ [ph_deref]) ty2
| wt_path_field: forall phl orgs id co ty1 fid
    (WP1: wt_path ce ty phl (Tstruct orgs id))
    (WP2: ce ! id = Some co)
    (WP3: field_type fid (co_members co) = OK ty1)
    (WP4: co_sv co = Struct),
    wt_path ce ty (phl++[ph_field fid]) ty1
| wt_path_downcast: forall phl orgs id co ty1 fid
    (WP1: wt_path ce ty phl (Tvariant orgs id))
    (WP2: ce ! id = Some co)
    (WP3: field_type fid (co_members co) = OK ty1)
    (WP4: co_sv co = TaggedUnion),
    wt_path ce ty (phl++[ph_downcast (Tvariant orgs id) fid]) ty1
.

Lemma wt_path_nil_inv: forall ce ty1 ty2,
    wt_path ce ty1 nil ty2 ->
    ty1 = ty2.
Proof.
  intros. inv H. auto.
  1-3: destruct phl; inv H1.
Qed.

Lemma wt_path_deref_inv: forall ce ty1 ty2 phl,
    wt_path ce ty1 (phl ++ [ph_deref]) ty2 ->
    exists ty1', wt_path ce ty1 phl ty1'
            /\ type_deref ty1' = OK ty2.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. subst. eauto.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. congruence.
Qed.

Lemma wt_path_field_inv: forall ce ty1 ty2 phl fid,
    wt_path ce ty1 (phl ++ [ph_field fid]) ty2 ->
    exists id orgs co,
      wt_path ce ty1 phl (Tstruct orgs id)
      /\ ce ! id = Some co
      /\ field_type fid (co_members co) = OK ty2
      /\ co_sv co = Struct.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. inv H0.
  exists id, orgs, co. eauto.
  eapply app_inj_tail in H1. destruct H1. congruence.
Qed.

Lemma wt_path_downcast_inv: forall ce ty1 ty2 phl fid ty,
    wt_path ce ty1 (phl ++ [ph_downcast ty fid]) ty2 ->
    exists id orgs co,
      ty = Tvariant orgs id                    
      /\ wt_path ce ty1 phl (Tvariant orgs id)
      /\ ce ! id = Some co
      /\ field_type fid (co_members co) = OK ty2
      /\ co_sv co = TaggedUnion.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. inv H0.
  exists id, orgs, co. eauto.
Qed.


Lemma wt_path_det: forall phl ty1 ty2 ty3 ce,
    wt_path ce ty1 phl ty2 ->
    wt_path ce ty1 phl ty3 ->
    ty2 = ty3.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    eapply wt_path_nil_inv in H0. subst.
    eapply wt_path_nil_inv in H. subst. auto.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + eapply wt_path_deref_inv in H0.
      destruct H0 as (ty1' & A1 & A2).
      eapply wt_path_deref_inv in H.
      destruct H as (ty1'' & A3 & A4).
      exploit IHn. eauto. eapply A1. eapply A3. intros.
      subst. rewrite A2 in A4. inv A4. auto.
    + eapply wt_path_field_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4).
      eapply wt_path_field_inv in H as (id1 & orgs1 & co1 & B1 & B2 & B3 & B4).
      exploit IHn. eauto. eapply A1. eapply B1.
      intros. inv H. rewrite A2 in B2. inv B2. rewrite A3 in B3. inv B3.
      auto.
    + eapply wt_path_downcast_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      eapply wt_path_downcast_inv in H as (id1 & orgs1 & co1 & B1 & B2 & B3 & B4 & B5).
      rewrite A1 in B1. inv B1.
      rewrite A3 in B3. inv B3. rewrite A4 in B4. inv B4. auto.
Qed.

      
Lemma wt_path_app: forall phl2 phl1 ty1 ty2 ty3 ce,
    wt_path ce ty1 phl1 ty2 ->
    wt_path ce ty1 (phl1 ++ phl2) ty3 ->
    wt_path ce ty2 phl2 ty3.
Proof.
  intro phl2. cut (exists n, length phl2 = n); eauto. intros (n & LEN).
  generalize dependent phl2.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    rewrite app_nil_r in H0. exploit wt_path_det. eapply H. eapply H0.
    intro. subst. econstructor.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + rewrite app_assoc in H0.
      eapply wt_path_deref_inv in H0.
      destruct H0 as (ty1' & A1 & A2).
      econstructor. eapply IHn; eauto. auto.
    + rewrite app_assoc in H0.
      eapply wt_path_field_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4).
      econstructor; eauto.
    + rewrite app_assoc in H0.
      eapply wt_path_downcast_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      subst.
      econstructor; eauto.
Qed.

Lemma wt_path_app_inv: forall phl2 phl1 ty1 ty3 ce,
    wt_path ce ty1 (phl1 ++ phl2) ty3 ->
    exists ty2,
      wt_path ce ty1 phl1 ty2
      /\ wt_path ce ty2 phl2 ty3.
Proof.
  intro phl2. cut (exists n, length phl2 = n); eauto. intros (n & LEN).
  generalize dependent phl2.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    rewrite app_nil_r in H.
    exists ty3. split; auto. econstructor.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + rewrite app_assoc in H.
      eapply wt_path_deref_inv in H.
      destruct H as (ty1' & A1 & A2).
      exploit IHn; eauto. intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
    + rewrite app_assoc in H.
      eapply wt_path_field_inv in H as (id & orgs & co & A1 & A2 & A3 & A4).
      exploit IHn; eauto. intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
    + rewrite app_assoc in H.
      eapply wt_path_downcast_inv in H as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      subst.
      exploit IHn; eauto.
      intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
Qed.


Lemma wt_place_wt_local: forall p (e: env) ce,
    wt_place e ce p ->
    exists b ty, e ! (local_of_place p) = Some (b, ty).
Proof.
  induction p; intros.
  - inv H. simpl. unfold env_to_tenv in WT1. rewrite PTree.gmap1 in WT1.
    destruct (e!i) eqn: A. inv WT1. destruct p. eauto.
    inv WT1.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
Qed.

    
Lemma local_of_paths_of_place: forall p,
    local_of_place p = fst (path_of_place p).
Proof.
  induction p; simpl; auto; destruct (path_of_place p); auto.
Qed.

(** Prove some properties w.r.t list_nth_z  *)
Fixpoint list_set_nth_z {A: Type} (l: list A) (n: Z) (v: A)  {struct l}: list A :=
  match l with
  | nil => nil
  | hd :: tl => if zeq n 0 then (v :: tl) else hd :: (list_set_nth_z tl (Z.pred n) v)
  end.

(* set footprint [v] in the path [ph] of footprint [fp] *)
Fixpoint set_footprint (phl: list path) (v: footprint) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some v
  | ph :: l =>
        match ph, fp with
        | ph_deref, fp_box b sz fp1 =>
            match set_footprint l v fp1 with
            | Some fp2 =>
                Some (fp_box b sz fp2)
            | None => None
            end
        | ph_field fid, fp_struct id fpl =>
            match find_fields fid fpl with
            | Some (fid1, fofs, ffp) =>                
                match set_footprint l v ffp with
                | Some ffp1 =>
                    Some (fp_struct id (set_field fid ffp1 fpl)) 
                | None => None
                end
            | None => None
            end
        | ph_downcast pty fid (* fty *), fp_enum id orgs tagz fid1 fofs1 fp1 =>
            match pty with
            | Tvariant orgs1 id1 =>
                if ident_eq id1 id then
                  if list_eq_dec ident_eq orgs1 orgs then
                    if ident_eq fid fid1 then
                      match set_footprint l v fp1 with
                      | Some fp2 =>
                          Some (fp_enum id orgs tagz fid1 fofs1 fp2)
                      | None => None
                      end
                    else None
                  else None
                else None
            | _ => None
            end
        | _, _ => None
        end
  end.

Fixpoint clear_footprint_rec (fp: footprint) : footprint :=
  match fp with
  | fp_scalar _
  | fp_box _ _ _
  | fp_enum _ _ _ _ _ _
  | fp_emp => fp_emp
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl)
  end.

Fixpoint get_loc_footprint (phl: list path) (fp: footprint) (b: block) (ofs: Z) : option (block * Z * footprint) :=
  match phl with
  | nil => Some (b, ofs, fp)
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_loc_footprint l fp1 b 0
      | ph_field fid, fp_struct _ fpl =>
          match find_fields fid fpl with
          | Some (_, fofs, fp1) =>
              get_loc_footprint l fp1 b (ofs + fofs)
          | None => None
          end
      | ph_downcast pty fid1 (* fty1 *), fp_enum id orgs _ fid2 fofs fp1 =>
          match pty with
          | Tvariant orgs1 id1 =>
              if ident_eq id1 id then
                if list_eq_dec ident_eq orgs1 orgs then
                if ident_eq fid1 fid2  then
                  get_loc_footprint l fp1 b (ofs + fofs)
                else
                  None
                else None
              else None
          | _ => None
          end
      | _, _  => None
      end
  end.

(* non-loc version: use it to get some internal footprint *)
Fixpoint get_footprint (phl: list path) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some fp
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_footprint l fp1
      | ph_field fid, fp_struct _ fpl =>
          match find_fields fid fpl with
          | Some (_, fofs, fp1) =>
              get_footprint l fp1
          | None => None
          end
      | ph_downcast pty fid1 (* fty1 *), fp_enum id orgs _ fid2 fofs fp1 =>
          match pty with
          | Tvariant orgs1 id1 =>
              if ident_eq id1 id then
                if list_eq_dec ident_eq orgs1 orgs then
                  if ident_eq fid1 fid2 then
                    get_footprint l fp1
                  else
                    None
                else None
              else None
          | _ => None
          end
      | _, _  => None
      end
  end.


(* Definition clear_footprint (phl: list path) (fp: footprint) : option footprint := *)
(*   match get_footprint phl fp with *)
(*   | Some fp1 => *)
(*       set_footprint phl (clear_footprint_rec fp1) fp *)
(*   | None => None *)
(*   end. *)


Definition set_footprint_map (ps: paths) (v: footprint) (fpm: fp_map) : option fp_map :=
  let (id, phl) := ps in
  match fpm!id with
  | Some fp1 =>
      match set_footprint phl v fp1 with
      | Some fp2 =>
          Some (PTree.set id fp2 fpm)
      | None =>
          None
      end
  | None => None
  end.


Definition get_loc_footprint_map (e: env) (ps: paths) (fpm: fp_map) : option (block * Z * footprint) :=
  let (id, phl) := ps in
  match e!id, fpm!id with
  | Some (b, ty), Some fp =>
      get_loc_footprint phl fp b 0
  | _, _ => None
  end.


(* Definition get_footprint_map (ps: paths) (fpm: fp_map) : option footprint := *)
(*   let (id, phl) := ps in *)
(*   match fpm!id with *)
(*   | Some fp => *)
(*       get_footprint phl fp *)
(*   | None => None *)
(*   end. *)

Definition clear_footprint_map e (ps: paths) (fpm: fp_map) : option fp_map :=
  match get_loc_footprint_map e ps fpm with
  | Some (_, _, fp1) =>
      set_footprint_map ps (clear_footprint_rec fp1) fpm
  | None => None
  end.

(* Useful tactic to destruct get_loc_footprint *)
Ltac destr_fp_enum fp ty :=
  destruct fp; try congruence;
  destruct ty; try congruence;
  destruct ident_eq; try congruence;
  destruct list_eq_dec; try congruence;
  destruct ident_eq; try congruence; subst.



Lemma get_loc_footprint_app: forall phl2 phl1 fp fp1 b ofs b1 ofs1 b2 ofs2 fp2,
    get_loc_footprint phl1 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint phl2 fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    get_loc_footprint (phl1 ++ phl2) fp b ofs = Some (b2, ofs2, fp2).
Admitted.

Lemma get_loc_footprint_map_app: forall phl2 phl1 id e fpm b ofs fp b1 ofs1 fp1,
    get_loc_footprint_map e (id, phl1) fpm = Some (b, ofs, fp) ->
    get_loc_footprint phl2 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint_map e (id, phl1 ++ phl2) fpm = Some (b1, ofs1, fp1).
Proof.
  induction phl2; intros.
  - simpl in H0. inv H0. rewrite app_nil_r. auto.
  - unfold get_loc_footprint_map in H.
    destruct (e ! id) eqn: ID; try congruence. destruct p.
    destruct (fpm ! id) eqn: FPM; try congruence.     
    replace (a :: phl2) with ((a::nil) ++ phl2) by auto.
    rewrite app_assoc.
    simpl in H0. destruct a.
    + destruct fp; try congruence.          
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. eauto. auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. rewrite FIND. eauto. auto.
    + destruct fp; try congruence.
      destruct ty; try congruence. destruct ident_eq in H0; try congruence. subst.
      destruct list_eq_dec in H0; try congruence.
      destruct ident_eq in H0; simpl in H0; try congruence. subst.            
      (* destruct type_eq in H0; simpl in H0; try congruence. subst. *)
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. destruct ident_eq; simpl; try congruence.
      destruct ident_eq; simpl; try congruence.
      destruct list_eq_dec; try congruence.
      (* destruct type_eq; simpl; try congruence. *)
      eauto. auto.
Qed.


Lemma get_loc_footprint_app_inv: forall phl2 phl1 b1 b2 ofs1 ofs2 fp1 fp2,
    get_loc_footprint (phl1 ++ phl2) fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    exists b3 ofs3 fp3,
      get_loc_footprint phl1 fp1 b1 ofs1 = Some (b3, ofs3, fp3)
      /\ get_loc_footprint phl2 fp3 b3 ofs3 = Some (b2, ofs2, fp2).
Admitted.


Lemma get_loc_footprint_map_app_inv: forall phl2 phl1 id e fpm b1 ofs1 fp1,
    get_loc_footprint_map e (id, phl1 ++ phl2) fpm = Some (b1, ofs1, fp1) ->
    exists b ofs fp,
      get_loc_footprint_map e (id, phl1) fpm = Some (b, ofs, fp)
      /\ get_loc_footprint phl2 fp b ofs = Some (b1, ofs1, fp1).
Admitted.

Lemma get_set_footprint_map_exists: forall phl id fp fp1 fpm1 b ofs le,
    get_loc_footprint_map le (id, phl) fpm1 = Some (b, ofs, fp1) ->
    exists fpm2, set_footprint_map (id, phl) fp fpm1 = Some fpm2
            /\ get_loc_footprint_map le (id, phl) fpm2 = Some (b, ofs, fp).
Admitted.


Lemma get_set_footprint_map: forall phl id fp fp1 fpm1 fpm2 b ofs le,
    get_loc_footprint_map le (id, phl) fpm1 = Some (b, ofs, fp1) ->
    set_footprint_map (id, phl) fp fpm1 = Some fpm2 ->
    get_loc_footprint_map le (id, phl) fpm2 = Some (b, ofs, fp).
Admitted.

Lemma get_set_footprint_map_app_inv: forall phl2 phl1 id fpm1 fpm2 fp1 fp2 b1 ofs1 le,
    get_loc_footprint_map le (id, phl1) fpm1 = Some (b1, ofs1, fp1) ->
    set_footprint_map (id, phl1++phl2) fp2 fpm1 = Some fpm2 ->
    exists fp3,
      get_loc_footprint_map le (id, phl1) fpm2 = Some (b1, ofs1, fp3)
      /\ set_footprint phl2 fp2 fp1 = Some fp3.
Admitted.

Lemma set_footprint_app: forall l1 l2 fp1 fp1' fp2 fp fp',
        get_footprint l1 fp = Some fp1 ->
        set_footprint l2 fp2 fp1 = Some fp1' ->
        set_footprint l1 fp1' fp = Some fp' ->
        set_footprint (l1++l2) fp2 fp = Some fp'.
Proof.
  induction l1; intros.
  - simpl in *. inv H. inv H1. auto.
  - simpl in *. destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint l1 fp1' fp) eqn: A; try congruence.
      inv H1. erewrite IHl1; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint l1 fp1' f) eqn: SET; try congruence.
      inv H1. erewrite IHl1; eauto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      destruct (set_footprint l1 fp1' fp) eqn: SET; try congruence.
      erewrite IHl1; eauto.
Qed.

(** IMPORTANT TODO *)
Lemma set_footprint_app_inv : forall l1 l2 fp fp' vfp1,
    set_footprint (l1++l2) vfp1 fp = Some fp' ->
    exists fp'' vfp2,
      get_footprint l1 fp = Some fp''                                       
      /\ set_footprint l2 vfp1 fp'' = Some vfp2
      /\ set_footprint l1 vfp2 fp = Some fp'.
Proof.
  induction l1; intros.
  - simpl in H. exists fp, fp'. simpl.
    repeat apply conj; auto.
  - simpl in H. destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint (l1 ++ l2) vfp1 fp) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl.
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint (l1 ++ l2) vfp1 f) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl. rewrite FIND.
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      simpl.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      destruct (set_footprint (l1 ++ l2) vfp1 fp) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl.      
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
Qed.

      
(* non-loc version of get_footprint_app *)
Lemma get_footprint_app: forall l1 l2 fp1 fp2 fp3,
    get_footprint l1 fp1 = Some fp2 ->
    get_footprint l2 fp2 = Some fp3 ->
    get_footprint (l1 ++ l2) fp1 = Some fp3.
Proof.
  induction l1; intros; simpl in *.
  - inv H. auto.
  - destruct a.
    + destruct fp1; try congruence.
      eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. eauto.
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      eauto.
Qed.

Lemma get_footprint_app_inv: forall phl2 phl1 fp1 fp2,
    get_footprint (phl1 ++ phl2) fp1 = Some fp2 ->
    exists fp3,
      get_footprint phl1 fp1 = Some fp3
      /\ get_footprint phl2 fp3 = Some fp2.
Admitted.


Lemma get_loc_footprint_eq: forall l fp b ofs b1 ofs1 fp1,
    get_loc_footprint l fp b ofs = Some (b1, ofs1, fp1) ->
    get_footprint l fp = Some fp1.
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in *. destruct a.
    + destruct fp; try congruence.
      eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. eauto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      eauto.
Qed.

      
Lemma get_set_disjoint_paths : forall phl1 phl2 id e fpm1 fpm2 fp,
    paths_disjoint phl1 phl2 ->
    set_footprint_map (id, phl1) fp fpm1 = Some fpm2 ->
    get_loc_footprint_map e (id, phl2) fpm1 = get_loc_footprint_map e (id, phl2) fpm2.
Admitted.

Lemma get_set_different_local : forall phl1 phl2 id1 id2 e fpm1 fpm2 fp,
    id1 <> id2 ->
    set_footprint_map (id1, phl1) fp fpm1 = Some fpm2 ->
    get_loc_footprint_map e (id2, phl2) fpm1 = get_loc_footprint_map e (id2, phl2) fpm2.
Admitted.

(* The footprints of two different subfields are disjoint *)
Lemma footprint_norepet_fields_disjoint: forall (fpl: list (ident * Z * footprint)) id1 id2 fofs1 fofs2 fp1 fp2,
    list_norepet (flat_map (fun '(_, _, fp) => footprint_flat fp) fpl) ->
    In (id1, fofs1, fp1) fpl ->
    In (id2, fofs2, fp2) fpl ->
    id1 <> id2 ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  induction fpl; simpl; intros; try contradiction.
  destruct a. destruct p. 
  eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
  destruct H0; destruct H1.
  - inv H. inv H0. congruence.
  - inv H. red. intros. intro.
    eapply A3. eauto.
    eapply in_flat_map. exists (id2, fofs2, fp2). eauto. auto.
  - inv H0. red. intros. intro.
    eapply A3. eauto.
    eapply in_flat_map. exists (id1, fofs1, fp1). eauto. auto.
  - eauto.
Qed.

    
Lemma footprint_norepet_fields_norepet: forall (fpl: list (ident * Z * footprint)) id fofs fp,
    list_norepet (flat_map (fun '(_, _, fp) => footprint_flat fp) fpl) ->
    In (id, fofs, fp) fpl ->
    list_norepet (footprint_flat fp).
Proof.
  induction fpl; simpl; intros; try contradiction.
  destruct a. destruct p. destruct H0.
  - inv H0. eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
    auto.
  - eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
    eauto.
Qed.


(* This lemma indicates that the footprint is a non-cyclic tree. *)
Lemma get_loc_footprint_norepet: forall phl fp b ofs b1 ofs1 fp1,
    list_norepet (footprint_flat fp) ->
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    ~ In b (footprint_flat fp) ->
    list_norepet (footprint_flat fp1)
    /\ ~ In b1 (footprint_flat fp1).
Proof.
  induction phl; intros until fp1; intros NOREP1 GFP NIN; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + destruct fp; try congruence.
      simpl in *. inv NOREP1.
      eapply IHphl; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      eapply IHphl. 2: eapply GFP.
      eapply footprint_norepet_fields_norepet; eauto.
      intro. eapply NIN. simpl.
      eapply in_flat_map; eauto.
    + destr_fp_enum fp ty.
      simpl in *. eauto.
Qed.

Lemma norepet_flat_fp_map_element: forall fpm id fp,
    fpm ! id = Some fp ->
    list_norepet (flat_fp_map fpm) ->
    list_norepet (footprint_flat fp).
Proof.
  intros. eapply PTree.elements_remove in H.
  destruct H as (l1 & L2 & A & B).
  unfold flat_fp_map in H0.
  rewrite A in H0.
  erewrite map_app in H0. erewrite concat_app in H0.
  eapply list_norepet_app in H0. destruct H0 as (C & D & E).
  simpl in D. eapply list_norepet_app in D. destruct D.
  auto.
Qed.

Lemma norepet_flat_fp_map_element_disjoint: forall fpm id1 id2 fp1 fp2,
    fpm ! id1 = Some fp1 ->
    fpm ! id2 = Some fp2 ->
    id1 <> id2 ->
    list_norepet (flat_fp_map fpm) ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  intros. unfold flat_fp_map in H2.
  eapply PTree.elements_correct in H.
  eapply PTree.elements_correct in H0.
  generalize dependent (PTree.elements fpm).
  induction l; intros; simpl in *; try contradiction.
  destruct a. destruct H.
  - inv H. destruct H0. inv H. try congruence.
    eapply list_norepet_app in H2 as (N1 & N2 & N3).
    simpl in *. red. intros.
    eapply N3; auto.
    eapply in_concat; eauto.
    exists (footprint_flat fp2). split; auto.
    eapply in_map_iff.
    exists (id2, fp2). eauto.
  - destruct H0. inv H0.
    + eapply list_norepet_app in H2 as (N1 & N2 & N3).
      simpl in *. eapply list_disjoint_sym. red. intros.
      eapply N3; auto.
      eapply in_concat; eauto.
      exists (footprint_flat fp1). split; auto.
      eapply in_map_iff.
      exists (id1, fp1). eauto.
    + eapply list_norepet_app in H2 as (N1 & N2 & N3).
      eauto.
Qed.

    
(** separating a footprint from the well-formed
footprint map *)
Lemma get_loc_footprint_map_norepet: forall phl id fpm b1 ofs1 fp1 e,
    list_norepet (flat_fp_map fpm) ->
    get_loc_footprint_map e (id, phl) fpm = Some (b1, ofs1, fp1) ->
    (* we require that the stack blocks and the blocks in fpm are disjoint *)
    list_disjoint (footprint_of_env e) (flat_fp_map fpm) ->
    list_norepet (footprint_flat fp1)
    /\ ~ In b1 (footprint_flat fp1).
Proof.
  intros until e. intros NOREP1 GFP DIS.
  unfold get_loc_footprint_map in GFP.
  destruct (e!id) eqn: A; try congruence.
  destruct p.
  destruct (fpm!id) eqn: B; try congruence.
  eapply get_loc_footprint_norepet; eauto.
  eapply norepet_flat_fp_map_element; eauto.
  intro. eapply DIS. eapply in_footprint_of_env; eauto.
  eapply in_footprint_flat_fp_map; eauto. auto.
Qed.  
  
(* norepet (l ++ fpm) where l is a general list which can
    represent other elements in the frame *)
Lemma set_disjoint_footprint_norepet: forall fpm1 fpm2 vfp id phl,
    list_norepet (flat_fp_map fpm1) ->
    set_footprint_map (id, phl) vfp fpm1 = Some fpm2 ->
    list_disjoint (flat_fp_map fpm1) (footprint_flat vfp) ->
    list_norepet (flat_fp_map fpm2).
Admitted.

Lemma empty_footprint_flat: forall fp,
    footprint_flat (clear_footprint_rec fp) = nil.
Admitted.

Lemma empty_footprint_disjoint: forall fp1 fp2,
    list_disjoint fp1 (footprint_flat (clear_footprint_rec fp2)).
Proof.
  intros. rewrite empty_footprint_flat. red. intros. inv H0.
Qed.

Lemma get_footprint_incl: forall phl fp fp1,
    get_footprint phl fp = Some fp1 ->
    incl (footprint_flat fp1) (footprint_flat fp).
Proof.
  induction phl; intros; simpl in *.
  - inv H. eapply incl_refl.
  - destruct a.
    + destruct fp; try congruence.
      simpl. red.
      intros. eapply in_cons. eapply IHphl; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      simpl. red. intros. eapply in_flat_map.
      eapply IHphl in H0; eauto.
      eapply find_fields_some in FIND. destruct FIND. subst.
      exists (i, z, f). auto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; subst; try congruence.
      destruct list_eq_dec; subst; try congruence.
      destruct ident_eq; subst; try congruence.
      simpl. eauto.
Qed.


(* The footprint is included in the source footprint *)
Lemma get_loc_footprint_incl: forall phl fp b ofs b1 ofs1 fp1,
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    incl (footprint_flat fp1) (footprint_flat fp).
Proof.
  intros. eapply get_footprint_incl.
  eapply get_loc_footprint_eq. eauto.
Qed.  

Lemma get_loc_footprint_map_incl: forall phl fpm b1 ofs1 fp1 le id,
    get_loc_footprint_map le (id, phl) fpm = Some (b1, ofs1, fp1) ->
    incl (footprint_flat fp1) (flat_fp_map fpm).
Proof.
  intros. simpl in H. destruct (le!id) in H; try congruence.
  destruct p. destruct (fpm!id) eqn: FPM; try congruence.
  red. intros. eapply get_loc_footprint_incl in H0; eauto.
  unfold flat_fp_map. eapply in_concat.
  exists (footprint_flat f). split; auto.
  eapply in_map_iff. exists (id, f). simpl. split; auto.
  eapply PTree.elements_correct. auto.
Qed.


Lemma set_footprint_incl: forall fp1 fp2 fp  phl b,
    set_footprint phl fp fp1 = Some fp2 ->
    In b (footprint_flat fp2) ->
    In b (footprint_flat fp1)
    \/ In b (footprint_flat fp).
Admitted.

(* TODO *)
Lemma set_footprint_map_incl: forall fpm1 fpm2 fp id phl b,
    set_footprint_map (id, phl) fp fpm1 = Some fpm2 ->
    In b (flat_fp_map fpm2) ->
    In b (flat_fp_map fpm1) \/ In b (footprint_flat fp).
Admitted.

Lemma set_footprint_norepet: forall phl fp1 fp2 vfp,
    set_footprint phl vfp fp1 = Some fp2 ->
    list_norepet (footprint_flat fp1) ->
    list_norepet (footprint_flat vfp) ->
    list_disjoint (footprint_flat fp1) (footprint_flat vfp) ->
    list_norepet (footprint_flat fp2).
Admitted.

Lemma get_set_disjoint_footprint: forall phl fp fp' fp1 fp2,
    get_footprint phl fp = Some fp1 ->
    set_footprint phl fp2 fp = Some fp' ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (footprint_flat fp) ->
    list_disjoint (footprint_flat fp') (footprint_flat fp1).
Proof.
  induction phl; intros until fp2; intros GFP SFP DIS NOREP; simpl in *.
  - inv GFP. inv SFP.
    eapply list_disjoint_sym. auto.
  - destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint phl fp2 fp) eqn: S1; try congruence.
      inv SFP. simpl in *.
      red. intros. inv H.
      * inv NOREP. intro. subst. eapply H2.
        eapply get_footprint_incl; eauto.
      * eapply IHphl; eauto.
        inv NOREP; auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some. eapply FIND. intros (A1 & A2). subst.
      destruct (set_footprint phl fp2 f) eqn: S1; try congruence.
      inv SFP. simpl in *.
      red. intros.
      eapply in_flat_map in H.
      destruct H as (((fid1 & fofs1) & ffp1) & IN1 & IN2).
      eapply in_map_iff in IN1.
      destruct IN1 as (((fid2 & fofs2) & ffp2) & IN3 & IN4).
      destruct ident_eq in IN3.
      * inv IN3. eapply IHphl; eauto.
        eapply footprint_norepet_fields_norepet; eauto.
      * inv IN3.
        eapply footprint_norepet_fields_disjoint. eauto.
        eapply IN4. eapply A2. auto. auto.
        eapply get_footprint_incl; eauto.
    + destr_fp_enum fp ty.
      destruct (set_footprint phl fp2 fp) eqn: S1; try congruence.
      inv SFP. simpl in *. eapply IHphl; eauto.
Qed.

(* Set a footprint also remove the original one out. This removed
   footprint is disjoint with the updated footprint map *)
Lemma get_set_disjoint_footprint_map: forall l i fpm1 fpm2 b ofs fp1 fp2 le,
    get_loc_footprint_map le (i, l) fpm1 = Some (b, ofs, fp1) ->
    set_footprint_map (i, l) fp2 fpm1 = Some fpm2 ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (flat_fp_map fpm1) ->
    list_disjoint (flat_fp_map fpm2) (footprint_flat fp1).
Proof.
  intros. simpl in *.
  destruct (le ! i) eqn: A1; try congruence. destruct p.
  destruct (fpm1 ! i) eqn: A2; try congruence.
  destruct (set_footprint l fp2 f) eqn: A3; try congruence. inv H0.
  red. intros.
  eapply in_concat in H0.
  destruct H0 as (bs & IN1 & IN2). eapply in_map_iff in IN1.
  destruct IN1 as ((id & fp) & B1 & B2). simpl in *. subst.
  eapply PTree.elements_complete in B2. rewrite PTree.gsspec in B2.
  destruct peq in B2.
  - inv B2.
    eapply get_set_disjoint_footprint; eauto.
    eapply get_loc_footprint_eq; eauto.
    eapply norepet_flat_fp_map_element; eauto.
  - eapply norepet_flat_fp_map_element_disjoint. eapply B2. eapply A2.
    auto. auto. auto.
    eapply get_loc_footprint_incl; eauto.
Qed.      
    
    
(* (fpm\fp) * fp = fpm *)
Lemma get_clear_footprint_equiv: forall fpm1 fpm2 fp le id phl b ofs,
    get_loc_footprint_map le (id, phl) fpm1 = Some (b, ofs, fp) ->
    clear_footprint_map le (id, phl) fpm1 = Some fpm2 ->
    list_equiv (footprint_flat fp ++ flat_fp_map fpm2) (flat_fp_map fpm1).
Admitted.



(** * Semantics Interface *)

(* Similar to inject_separated: m contains footprint fp1 and fp2 is
the extended footprint which is not in m *)
Definition flat_footprint_separated (fp1 fp2: flat_footprint) (m : mem) : Prop :=
  forall b, ~ In b fp1 ->
       In b fp2 ->
       ~ Mem.valid_block m b.

(** Unused because it is equivalent to
flat_footprint_separated. footprint which not in fp1 and valid in m is
not in fp2 *)
Definition flat_footprint_incr (fp1 fp2: flat_footprint) (m: mem) : Prop :=
  forall b, ~ In b fp1 ->
       Mem.valid_block m b ->
       ~ In b fp2.
  
Lemma flat_footprint_separated_refl: forall fp m,
    flat_footprint_separated fp fp m.
Proof.
  intros. red. intros. congruence.
Qed.


Inductive wt_rs_world :=
  rsw (sg: rust_signature)
    (fp: flat_footprint)
    (m: mem).
    (* (Hm: Mem.sup_include fp (Mem.support m)). *)

(** The footprint may be unique *)
Inductive wt_rs_query : wt_rs_world -> rust_query -> Prop :=
| wt_rs_query_intro: forall sg m vf args fpl fp,
    let ce := rs_sig_comp_env sg in
    forall (DIS: footprint_disjoint_list fpl)
    (SEMWT: sem_wt_val_list ce m fpl args)
    (* footprints are well-typed *)
    (WTFP: list_forall2 (fun argty fp => wt_footprint (rs_sig_comp_env sg) argty fp) (rs_sig_args sg) fpl)
    (* structured footprint is equivalent with the flat footprint in the interface *)
    (EQ: list_equiv fp (concat (map footprint_flat fpl))),
    wt_rs_query (rsw sg fp m) (rsq vf sg args m)
.

(* Only consider ownership transfer for now. The footprints of generic
origins are more complicated *)
Inductive rsw_acc : wt_rs_world -> wt_rs_world -> Prop :=
| rsw_acc_intro: forall sg fp fp' m m'
    (UNC: Mem.unchanged_on (fun b ofs => ~ In b fp) m m')
    (* new footprint is separated *)
    (SEP: flat_footprint_separated fp fp' m),
    (* block not in fp must be not in fp' otherwise it is not a frame rule *)
    (* (INCR: flat_footprint_incr fp fp' m), *)
    rsw_acc (rsw sg fp m) (rsw sg fp' m').

Inductive wt_rs_reply : wt_rs_world -> rust_reply -> Prop :=
| wt_rs_reply_intro: forall rfp m rv sg fp,
    let ce := rs_sig_comp_env sg in
    forall (SEMWT: sem_wt_val ce m rfp rv)
    (WTFP: wt_footprint (rs_sig_comp_env sg) (rs_sig_res sg) rfp)
    (* rfp is separated from fpl *)
    (SEP: list_disjoint (footprint_flat rfp) fp),
    wt_rs_reply (rsw sg fp m) (rsr rv m)
.

Definition wt_rs : invariant li_rs :=
  {|
    inv_world := Genv.symtbl * wt_rs_world;
    symtbl_inv := fun '(se, _) => eq se;
    query_inv := fun '(_, w) q => wt_rs_query w q;
    reply_inv := fun '(_, w) r => exists w', rsw_acc w w' /\ wt_rs_reply w' r |}.


(* Unused: Rust type used in interface *)
Inductive rtype : Type :=
(* primitive types excluding struct and enum *)
| rt_int (sz: Ctypes.intsize) (sg: Ctypes.signedness)
| rt_box (ty: rtype)
| rt_comp
    (id: ident)
    (sv: struct_or_variant)
    (fields: list (ident * rtype))
    (attr: Ctypes.attr)
    (orgs: list origin)
    (rels: list origin_rel)
(* used in recursive type  *)
| rt_comp_rec (id: ident)
.

(* Property of rsw_acc *)

Lemma rsw_acc_refl: forall w,
    rsw_acc w w.
Proof.
  intros. destruct w.
  econstructor.
  eapply Mem.unchanged_on_refl.
  red. intros. congruence.
Qed.
  
Lemma rsw_acc_trans: forall w1 w2 w3,
    rsw_acc w1 w2 ->
    rsw_acc w2 w3 ->
    rsw_acc w1 w3.
Proof.
  intros. inv H. inv H0.
  econstructor.
  - (* cannot use unchanged_on_trans because fp is not useful in m' *)
    inv UNC. inv UNC0.
    econstructor.
    + eauto with mem.
    (* perm *)
    + intros.
      assert (A: ~ In b fp').
      { intro. eapply SEP; eauto. }
      split; intros.
      * eapply unchanged_on_perm0; eauto.
        eapply unchanged_on_support; auto.
        eapply unchanged_on_perm; eauto.
      * eapply unchanged_on_perm; eauto.
        eapply unchanged_on_perm0; eauto.
        eapply Mem.perm_valid_block.
        eapply unchanged_on_perm0 in H1; eauto.
        eapply unchanged_on_support. eauto.
    (* contents *)
    + intros.
      assert (A: Mem.valid_block m b).
      eapply Mem.perm_valid_block. eauto.
      assert (B: ~ In b fp').
      { intro. eapply SEP; eauto. }
      erewrite unchanged_on_contents0; eauto.
      eapply unchanged_on_perm; eauto.
  (* flat_footprint_separated *)
  - red. intros.
    destruct (Mem.sup_dec b (Mem.support m)); auto.
    (* impossible *)
    (* 1. b is in not fp' (by SEP) ; 2. b is in fp'0; 3. so b is not
    in m' support (by SEP0) *)
    assert (A: ~ In b fp').
    { intro. eapply SEP; eauto. }
    intro. eapply Mem.unchanged_on_support in H1; eauto.
    eapply SEP0; eauto.
Qed.    
      
Section FPM.

Variable fpm : fp_map.
  
Definition mmatch ce (m: mem) (e: env) (own: own_env): Prop :=
  forall p b ofs fp,
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) ->
    is_init own p = true ->
    bmatch ce m b ofs fp
    /\ (is_full own.(own_universe) p = true ->
       sem_wt_loc ce m fp b ofs).


Record wf_env (ce: composite_env) (e: env): Prop := {
    wf_env_footprint: forall id b ty,
      e!id = Some (b, ty) ->
      (* Do we need to ensure the location is sem_wt? *)
      exists fp, fpm!id = Some fp
            /\ wt_footprint ce ty fp;
    
    (* stack blocks and the blocks in footprint map are disjoint. This
    property can be expressed in sound_state *)
    (* wf_env_disjoint: *)
    (* list_disjoint (footprint_of_env e) (flat_fp_map fpm) *)
    
  }.

End FPM.

Definition ce_extends (env env': composite_env) : Prop := forall id co, env!id = Some co -> env'!id = Some co.

Lemma ce_extends_remove: forall ce1 ce2 id,
    ce_extends ce1 ce2 ->
    ce_extends (PTree.remove id ce1) ce2.
Admitted.

(* Some useful invariant of the own_env in the move checking, such as
if a place p is init, then all its dominators is init. Those
properties are only guaranteed by the move checking, so we cannot
prove it in the semantics. One problem is how to establish and
preserve this invariant in the function entry and every step. May be
we should do some checking for each function *)

Record wf_own_env (own: own_env) : Prop := {
    wf_own_dominators: forall p,
      is_init own p = true ->
      dominators_is_init own p = true;

    (* validation property *)
    wf_own_universe_shallow: forall p1 p2,
      in_universe own p1 = true ->      
      in_universe own p2 = true ->
      is_shallow_prefix p1 p2 = false;

    (* all place in the universe has no downcast *)
    wf_own_no_downcast: forall p fid ty,
      in_universe own p = true ->
      ~ In (ph_downcast ty fid) (snd (path_of_place p));

    (* if a place is not full, it must be box type. Remember that if a
    struct/or some other scalar place is in the universe, it must be
    full. *)
    wf_own_type: forall p,
      in_universe own p = true ->
      is_full (own_universe own) p = false ->
      exists ty, typeof_place p = Tbox ty;
  }.

(* easy because none of the property in wf_own_env rely on some place
in init set *)
Lemma wf_own_env_move_place: forall own p,
    wf_own_env own ->
    wf_own_env (move_place own p).
Admitted.

Lemma wf_own_env_init_place: forall own p,
    dominators_is_init own p = true ->
    wf_own_env own ->
    wf_own_env (init_place own p).
Admitted.

Lemma dominators_is_init_field: forall own p fid fty,
    dominators_is_init own (Pfield p fid fty) = true ->
    dominators_is_init own p = true.
Proof.
  intros. unfold dominators_is_init in *. simpl in H. auto.
Qed.

Section COMP_ENV.

Variable ce: composite_env.

(* Lemma downcaset_dominators_eq: forall p fid fty, *)
(*     place_dominators p = place_dominators (Pdowncast p fid fty). *)
(* Proof. *)
(*   induction p; intros; simpl; auto. *)

Inductive valid_owner_offset_footprint : place -> Z -> footprint -> footprint -> Prop :=
| valid_owner_local: forall id ty fp,
    valid_owner_offset_footprint (Plocal id ty) 0 fp fp
| valid_owner_deref: forall p ty fp,
    valid_owner_offset_footprint (Pderef p ty) 0 fp fp
| valid_owner_field: forall p fty fid fp,
    valid_owner_offset_footprint (Pfield p fid fty) 0 fp fp
| valid_owner_downcast: forall p fid fty fp fp1 tagz fofs ofs id orgs
    (PTY: typeof_place p = Tvariant orgs id)
    (* (CO: ce ! id = Some co) *)
    (* (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs) *)
    (* (TAG: field_tag fid co.(co_members) = Some tagz) *)
    (VOWN: valid_owner_offset_footprint p ofs (fp_enum id orgs tagz fid fofs fp) fp1),
    valid_owner_offset_footprint (Pdowncast p fid fty) (ofs + fofs) fp fp1.

Lemma valid_owner_footprint_flat_eq: forall fp1 fp2 p ofs,
    valid_owner_offset_footprint p ofs fp1 fp2 ->
    footprint_flat fp1 = footprint_flat fp2.
Proof.
  induction 1; auto.
Qed.


(** So adhoc soluation: define a non-sense valid_owner_offset_footprint to prove the following two lemmas *)
Lemma valid_owner_place_footprint: forall p fpm e b ofs fp
    (PFP: get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp))
    (WT: wt_place e ce p),
  exists fp' ofs' fofs,
    get_loc_footprint_map e (path_of_place (valid_owner p)) fpm = Some (b, ofs', fp')
    /\ valid_owner_offset_footprint p fofs fp fp'
    /\ ofs = ofs' + fofs.
(* relationship between fp and fp'? *)
                          (* get_footprint *)
Proof.
  induction p; intros; simpl in *.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app_inv in PFP.
    destruct PFP as (b1 & ofs1 & fp1 & GET1 & GET2).
    inv WT.
    exploit IHp; eauto.
    intros (fp2 & ofs2 & fofs2 & PFP1 & VOFS1 & OFSEQ).
    simpl in GET2. destruct fp1; try congruence.
    rewrite WT2 in GET2.
    destruct ident_eq in GET2; simpl in GET2; try congruence. subst.
    destruct list_eq_dec in GET2; simpl in GET2; try congruence. subst.
    destruct ident_eq in GET2; simpl in GET2; try congruence. subst.
    (* destruct type_eq in GET2; simpl in GET2; try congruence. *)
    inv GET2.
    do 3 eexists. repeat apply conj.
    eauto. econstructor; eauto.    lia.
    (* ??? use the fact that variant_field_offset is constant to prove *)
Qed.

Lemma valid_owner_bmatch: forall p m b ofs1 fofs1 fp1 fp,
    bmatch ce m b ofs1 fp1 ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    bmatch ce m b (ofs1 + fofs1) fp.
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  (* rewrite PTY in H0. inv H0. *)
  inv H0.
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.

Lemma valid_owner_sem_wt_loc: forall p m b ofs1 fofs1 fp1 fp,
    sem_wt_loc ce m fp1 b ofs1 ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    sem_wt_loc ce m fp b (ofs1 + fofs1).
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  inv H0. simpl in *. try congruence. 
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.

Lemma wt_place_wt_path: forall p e ce id l ty b,
    wt_place (env_to_tenv e) ce p ->
    path_of_place p = (id, l) ->
    e ! id = Some (b, ty) ->
    wt_path ce ty l (typeof_place p).
Proof.
  induction p; simpl; intros.
  - inv H0. inv H.
    unfold env_to_tenv in WT1.
    rewrite PTree.gmap1 in WT1. rewrite H1 in WT1. inv WT1.
    constructor.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. econstructor; eauto.
    rewrite <- WT2. eauto.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. econstructor; eauto.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. rewrite WT2. econstructor; eauto.
    rewrite <- WT2. eauto.
Qed.    


(** IMPORTANT TODO *)
Lemma get_wt_footprint_wt: forall phl ty1 ty2 (WTPH: wt_path ce ty1 phl ty2) fp1 fp2,
    wt_footprint ce ty1 fp1 ->
    get_footprint phl fp1 = Some fp2 ->
    wt_footprint ce ty2 fp2.
Proof.
  induction 1; intros; simpl in *.
  - inv H0. auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    inv A2. exploit IHWTPH; eauto.
    intros A2. inv A2. simpl in WP2. inv WP2. auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    destruct (find_fields fid fpl) eqn: FIND; try congruence.
    repeat destruct p. inv A2.
    exploit IHWTPH; eauto. intros A3. inv A3.
    exploit find_fields_some; eauto.
    intros (B1 & B2). subst.
    exploit WT2; eauto.
    intros (fty & C1 & C2 & C3).
    rewrite WP2 in CO. inv CO.
    rewrite WP3 in C1. inv C1.
    auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    destruct ident_eq in A2; try congruence.
    destruct list_eq_dec in A2; try congruence.
    destruct ident_eq in A2; try congruence.
    inv A2.
    exploit IHWTPH; eauto. intros A3. inv A3.
    rewrite WP2 in CO. inv CO.
    rewrite WP3 in FTY. inv FTY. auto.
Qed.    
    
(** IMPRTANT TODO: use this lemma to prove eval_place_sound. Think
about the field type in wt_footprint is correct or not? *)
Lemma get_wt_place_footprint_wt: forall p fpm e b ofs fp,
    wf_env fpm ce e ->
    wt_place e ce p ->
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) ->
    wt_footprint ce (typeof_place p) fp.
Proof.
  intros until fp. intros WFENV WTP GFP.
  destruct (path_of_place p) eqn: POP.
  simpl in *.
  destruct (e!i) eqn: A; try congruence.
  destruct p0.
  destruct (fpm ! i) eqn: B; try congruence.
  exploit wf_env_footprint; eauto. intros (fp1 & C1 & C2).
  rewrite B in C1. inv C1.
  eapply get_loc_footprint_eq in GFP.
  eapply get_wt_footprint_wt; eauto.
  eapply wt_place_wt_path; eauto.
Qed.

(* A well typed footprint can imply all the sub-footprint's
well-typedness and the path to htis footprint also is well-typed *) 
Lemma get_wt_footprint_exists_wt: forall phl fp b ofs b1 ofs1 fp1 ty,
    wt_footprint ce ty fp ->
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    exists ty1, wt_footprint ce ty1 fp1
           /\ wt_path ce ty phl ty1.
Proof.
  intros phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    simpl in *. inv H0.
    exists ty. split; eauto.
    econstructor.
  - exploit length_S_inv; eauto.
    intros (phl' & a & TYS & LEN1). subst.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    simpl in G2.
    destruct a.
    + destruct fp3; try congruence.
      inv G2. exploit IHn; eauto.
      intros (ty1 & A1 & A2).
      inv A1.
      exists ty0. split; auto. econstructor; eauto.      
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: A; try congruence.
      repeat destruct p.
      inv G2.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit IHn; eauto. intros (ty1 & W1 & W2).
      inv W1.      
      exploit WT2; eauto.
      intros (fty & B1 & B2 & B3).
      exists fty. split; auto.
      econstructor; eauto. 
    + destruct fp3; try congruence.
      destruct ty0; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence. subst.
      inv G2. exploit IHn; eauto.
      intros (ty1 & A1 & A2).
      inv A1. exists fty. split; auto.
      econstructor; eauto.
Qed.

      
(* get_loc_footprint_map can succeed if the place is well-typed, the
footprint is well-typed and the footprint is well shaped by
mmatch. This lemma is used in dropplace state soundness. Because there
is no static analysis result in dropplace, we need to use own_env to
show p's dominators are init *)
Lemma get_loc_footprint_map_progress: forall e m p own fpm
    (MM: mmatch fpm ce m e own)
    (WFOWN: wf_env fpm ce e)
    (WT: wt_place (env_to_tenv e) ce p)
    (POWN: dominators_is_init own p = true)
    (** No downcast in the places *)
    (WF: forall fid ty, ~ In (ph_downcast ty fid) (snd (path_of_place p))),
  exists b ofs fp,
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp)
    /\ wt_footprint ce (typeof_place p) fp.
Proof.
  induction p; intros.
  (* Plocal *)
  - inv WT. exploit get_tenv_some; eauto. intros (b0 & A).    
    exploit wf_env_footprint; eauto. intros (fp & FP & WTFP).
    exists b0, 0, fp. repeat apply conj. simpl. rewrite A. rewrite FP. auto.
    simpl. auto.
  (* Pfield *)
  - inv WT.
    (** TODO: make it a lemma: prove p's dominators are init *)
    assert (PDOM: dominators_is_init own p = true).
    { eapply dominators_is_init_field. eauto. }             
    assert (IHWF: forall (fid : ident) (ty : type),
               ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. intro. eapply WF. simpl. destruct (path_of_place p) eqn: POP. simpl in *.
      eapply in_app. eauto. }
    exploit IHp; eauto.        
    intros (b & ofs & fp & PFP & WTFP).
    (* exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN). *)
    (** Inversion of WTFP *)
    rewrite WT2 in WTFP. inv WTFP; simpl in *; try congruence.
    rewrite WT3 in CO. inv CO.
    exploit WT0; eauto. intros (ffp & fofs & INFPL & FOFS& WTFP1).
    exists b, (ofs+fofs), ffp. repeat apply conj; auto.
    (* get_loc_footprint_map *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl.  rewrite INFPL. auto.        
  (* Pderef *)
  - inv WT.
    unfold dominators_is_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).
    assert (IHWF: forall (fid : ident) (ty : type),
               ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. intro. eapply WF. simpl. destruct (path_of_place p) eqn: POP. simpl in *.
      eapply in_app. eauto. }
    exploit IHp; eauto.
    intros (b & ofs & fp & PFP & WTFP).
    exploit MM. eauto. eauto.
    intros (BM & FULL).
    destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2.
    (* fp must not be fp_emp that is why we need mmatch *)
    inv WTFP; inv BM; simpl in *; try congruence.
    exists b0, 0, fp0. repeat apply conj.    
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl. auto.
    (* wt_footprint *)
    simpl. auto.
  (* Pdowncast: impossible *)
  - exfalso. eapply WF.
    simpl. destruct (path_of_place p) eqn: POP. simpl. eapply in_app.
    right. econstructor. eauto.
Qed.

(* Lemma wt_footprint_extend_ce: forall ce1 ce2 ty fp, *)
(*     wt_footprint ce ce1 ty fp -> *)
(*     ce_extends ce1 ce2 -> *)
(*     wt_footprint ce ce2 ty fp. *)
(* Admitted. *)


(* The locations evaluated by get_loc_footprint_map and eval_place are
the same. *)
Lemma eval_place_get_loc_footprint_map_equal: forall m le p fpm fp b1 ofs1 b2 ofs2 own
    (GFP: get_loc_footprint_map le (path_of_place p) fpm = Some (b1, ofs1, fp))
    (WT: wt_place le ce p)
    (WFENV: wf_env fpm ce le)
    (EVAL: eval_place ce le m p b2 ofs2)
    (MM: mmatch fpm ce m le own)
    (DOM: dominators_is_init own p = true),
    b1 = b2
    /\ ofs1 = Ptrofs.unsigned ofs2
    (* It is used to strengthen this lemma *)
    /\ wt_footprint ce (typeof_place p) fp.
Proof.
  induction p; intros.
  - inv EVAL. simpl in GFP. rewrite H3 in GFP.
    destruct (fpm ! i) eqn: FP; try congruence. inv GFP.
    repeat apply conj; auto.
    simpl. exploit wf_env_footprint; eauto.
    intros (fp0 & A1 & A2). rewrite FP in A1. inv A1. auto.    
  - inv EVAL. simpl in GFP. destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    exploit IHp; eauto. inv WT. eauto.
    intros (A1 & A2 & A3). subst.
    simpl in G2. destruct fp3; try congruence.
    destruct (find_fields i fpl) eqn: FIND; try congruence. repeat destruct p0.
    inv G2. inv A3. rewrite H3 in H0. inv H0.
    exploit find_fields_some; eauto. intros (B1 & B2). subst.
    exploit WT2; eauto.
    intros (fty & C1 & C2 & C3).
    rewrite H6 in CO. inv CO.
    rewrite H7 in C2. inv C2.
    repeat apply conj; auto.
    rewrite Ptrofs.add_unsigned.
    (** range proof obligation *)
    rewrite !Ptrofs.unsigned_repr. auto.
    admit. admit.
    inv WT. rewrite H3 in WT3. inv WT3.
    rewrite H6 in WT4. inv WT4.
    rewrite C1 in WT5. inv WT5. 
    simpl. eauto.
  - inv EVAL. inv WT. destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2. inv H4; simpl in *; try congruence. inv H.
    destruct (path_of_place p) eqn: POP. 
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    unfold dominators_is_init in DOM. simpl in DOM.
    eapply andb_true_iff in DOM. destruct DOM as (D1 & D2).
    exploit IHp; eauto.
    intros (A1 & A2 & A3). subst.
    simpl in G2. destruct fp3; try congruence. inv G2.
    inv A3.
    exploit MM. erewrite POP. eauto. auto. intros (BM & FULL).
    inv BM. rewrite H0 in LOAD. inv LOAD.
    repeat apply conj; auto.    
  - inv EVAL. simpl in GFP. destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    unfold dominators_is_init in *. simpl in DOM.
    eapply andb_true_iff in DOM. destruct DOM as (A & B).
      assert (DOM1: dominators_is_init own p = true).
    { destruct p; simpl in *; auto.
      eapply andb_true_iff. auto. }
    exploit IHp; eauto. inv WT. eauto.
    intros (A1 & A2 & A3). subst.
    simpl in G2. destruct fp3; try congruence. rewrite H3 in G2.
    destruct ident_eq in G2; try congruence.
    destruct list_eq_dec in G2; try congruence.
    destruct ident_eq in G2; try congruence. inv G2.
    rewrite H3 in A3. inv A3.
    rewrite H4 in CO. inv CO.
    rewrite H9 in FOFS. inv FOFS.
    repeat apply conj; auto.
    rewrite Ptrofs.add_unsigned.
    (** range proof obligation *)
    rewrite !Ptrofs.unsigned_repr. auto.
    admit. admit.
    inv WT. rewrite H3 in WT2. inv WT2.
    rewrite H4 in WT3. inv WT3.
    exploit valid_owner_place_footprint. erewrite POP. eauto. auto.
    intros (fp' & ofs' & ofs1 & G2 & VFP & OFS).
    exploit MM. eapply G2. auto.
    intros (BM' & FULL').
    assert (BM1: bmatch ce m b1 (Ptrofs.unsigned ofs) (fp_enum id orgs tag0 fid ofs0 fp)).
    { rewrite OFS. eapply valid_owner_bmatch. eauto. eauto. }
    inv BM1.
    simpl in H5. rewrite H5 in TAG0. inv TAG0.
    rewrite Int.unsigned_repr in H8. rewrite H8 in TAG. inv TAG.
    simpl. auto.
    (* tag is in range *)
    admit.
Admitted.

(* The footprint contained in the location of a place *)
Lemma eval_place_sound: forall e m p b ofs own fpm init uninit universe
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch fpm ce m e own)
    (WFOWN: wf_env fpm ce e)
    (WT: wt_place (env_to_tenv e) ce p)
    (SOWN: sound_own own init uninit universe)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: dominators_must_init init uninit universe p = true),
  (* Do we need to specify the properties of fp? Do we need to show
  the permission of the location of p? *)
  exists fp (* ce' *) (* phl *), get_loc_footprint_map e (path_of_place p) fpm = Some (b, (Ptrofs.unsigned ofs), fp)
                      /\ wt_footprint ce (typeof_place p) fp.
                      (* /\ ce_extends ce' ce. *)
            (* /\ path_of_place ce p (local_of_place p, phl) *)
            (* /\ get_footprint_map (local_of_place p, phl) fpm = Some fp. *)
        (* /\ wt_footprint ce (typeof_place p) fp. *)
    (* if consider reference, we cannot say that p is a subplace of
    p', instead we need to state that the owner p points to is a
    subplace of p' *)
Proof.
  induction 1; intros.
  (* Plocal *)
  - rewrite Ptrofs.unsigned_zero.
    exploit wf_env_footprint; eauto. intros (fp & FP & WTFP).
    exists fp. repeat apply conj. simpl. rewrite H. rewrite FP. auto.
    simpl. auto.
  (* Pfield *)
  - inv WT.
    (* two type facts, reduce one *)
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    (** TODO: make it a lemma: prove p's dominators are init *)
    assert (PDOM: dominators_must_init init uninit universe p = true) by admit.    
    exploit IHEVAL. 1-5: auto.
    intros (fp & PFP & WTFP).
    (* exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN). *)
    (** TODO: produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr.
    (** Inversion of WTFP *)
    rewrite H in WTFP. inv WTFP; simpl in *; try congruence.
    rewrite H0 in CO. inv CO.
    exploit WT0; eauto. intros (ffp & fofs & INFPL & FOFS& WTFP1).
    exists ffp. repeat apply conj; auto.
    (* get_loc_footprint_map *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl.  rewrite INFPL. rewrite H1 in FOFS. inv FOFS. auto.        
    (* simpl. auto. *)
    (** *** TODO: Begin range proof *** *)
    (* Can we require that the size of p' is in the range of *)
(*     Ptrofs.max_unsigned, so that any subplace is in this range *)
(*     (including its successor) *)
    (* exploit wf_place_size; eauto. intros PSIZE. *)
    (* generalize (subplace_upper_bound _ _ _ _ _ SUBP CONSISTENT H5 (Z.lt_le_incl _ _ PSIZE)).    rewrite H. simpl. rewrite H0. *)
    (* erewrite co_consistent_sizeof; eauto. rewrite H9. simpl. *)
    (* assert (ALPOS: co_alignof co0 > 0). *)
    (* { exploit co_alignof_two_p. intros (n & ALPOW). *)
    (*   rewrite ALPOW. rewrite two_power_nat_equiv. *)
    (*   generalize (Nat2Z.is_nonneg n). intros A. *)
    (*   exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia. *)
    (*   eauto. lia. } *)
    (* generalize (align_le (sizeof_struct ce (co_members co0)) _ ALPOS). *)
    (* intros STRUCTSZ BOUND. *)
    (* exploit field_offset_in_range; eauto. intros (RANGE1 & RANGE2). *)
    (* generalize (Ptrofs.unsigned_range ofs). intros OFSRANGE. *)
    (* generalize (sizeof_pos ce ty). intros TYSZPOS. *)
    (* (* *** End range proof *** *) *)
    (* rewrite Ptrofs.add_unsigned. *)
    (* do 2 rewrite Ptrofs.unsigned_repr. *)
    (* econstructor. auto. eauto. eauto. *)
    (* eauto. *)
    (* (** dirty work: specify the requirement to prevent overflow *) *)
    (* lia. lia. lia. *)
    (* unfold is_shallow_prefix. eapply orb_true_intro. *)
  (* right. simpl. destruct (place_eq p p). auto. congruence. *)
    admit. admit. admit.
  (* Pdowncast *)
  - inv WT.
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    (** TODO: make it a lemma: prove p's dominators are init *)
    (** It is impossible to be proved  *)
    assert (PDOM: dominators_must_init init uninit universe p = true).
    { unfold dominators_must_init in *. simpl in *.
      eapply andb_true_iff in POWN. destruct POWN as (A & B).
      destruct p; simpl in *; auto.
      eapply andb_true_iff. auto. }
    (** Prove that p is_init  *)
    exploit IHEVAL. 1-5: auto.
    intros (fp & PFP & WTFP).
    (** TODO: produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr.
    (** Prove that p is_init: NO!! We can only show that (valid_owner
    p) is init *)
    exploit valid_owner_place_footprint. eauto. eauto. intros (fp1 & ofs1 & fofs1 & PFP1 & VOFS1 & OFSEQ).
    unfold dominators_must_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).
    exploit MM. eauto.
    eapply must_init_sound; eauto.        
    (* valid owner's bmatch implies subfield bmatch *)
    intros (BM & FULL).
    assert (BM1: bmatch ce m b (Ptrofs.unsigned ofs) fp).
    { rewrite OFSEQ. eapply valid_owner_bmatch. eauto. eauto. }
    rewrite H in WTFP. (* inv BM1. *)
    (* rewrite some redundant premises *)
    simpl in H1. 
    inv WTFP; simpl in *; try congruence. inv BM1.
    inv BM1. rewrite H1 in TAG0. inv TAG0. rewrite Int.unsigned_repr in H2.
    (* do some rewrting *)
    rewrite H0 in CO. inv CO.
    rewrite H2 in TAG. inv TAG. simpl.
    rewrite H3 in FOFS. inv FOFS.
    exists fp0. repeat apply conj.
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto. simpl.
    rewrite H. repeat destruct ident_eq; simpl; try congruence.
    destruct list_eq_dec; simpl; try congruence.
    (* destruct type_eq; simpl; try congruence.  *) auto.    
    (** *** TODO: Begin range proof *** *)
    (* exploit wf_place_size; eauto. intros PSIZE. *)
    (* generalize (subplace_upper_bound _ _ _ _ _ SUBP CONSISTENT H7 (Z.lt_le_incl _ _ PSIZE)).    rewrite H. simpl. rewrite H0. *)
    (* erewrite co_consistent_sizeof; eauto. rewrite H11. simpl. *)
    (* assert (ALPOS: co_alignof co0 > 0). *)
    (* { exploit co_alignof_two_p. intros (n & ALPOW). *)
    (*   rewrite ALPOW. rewrite two_power_nat_equiv. *)
    (*   generalize (Nat2Z.is_nonneg n). intros A. *)
    (*   exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia. *)
    (*   eauto. lia. } *)
    (* generalize (align_le (sizeof_variant ce (co_members co0)) _ ALPOS). *)
    (* intros ENUMSZ BOUND. *)
    (* exploit variant_field_offset_in_range; eauto. intros (RANGE1 & RANGE2). *)
    (* generalize (Ptrofs.unsigned_range ofs). intros OFSRANGE. *)
    (* generalize (sizeof_pos ce ty). intros TYSZPOS. *)
    (* (* *** End range proof *** *) *)
    (* rewrite Ptrofs.add_unsigned. *)
    (* do 2 rewrite Ptrofs.unsigned_repr. *)
    (* econstructor. auto. eauto. eauto. *)
    (* eauto. *)
    (* (** dirty work: specify the requirement to prevent overflow *) *)
    (* lia. lia. lia. *)
    (* (* shallow prefix *) *)
    (* unfold is_shallow_prefix. eapply orb_true_intro. *)
  (* right. simpl. destruct (place_eq p p). auto. congruence. *)
    1-4: admit. 
  (* Pderef *)
  - inv WT.
    unfold dominators_must_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).    
    exploit IHEVAL; eauto.
    intros (fp & PFP & WTFP).
    exploit MM. eauto.
    eapply must_init_sound; eauto.
    intros (BM & FULL). destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2.
    inv WTFP; inv BM; simpl in *; try congruence.
    exists fp0. repeat apply conj.    
    (* prove ofs' = 0 *)
    inv H; simpl in *; try congruence.
    simpl in *. inv H0. rewrite LOAD in H1. inv H1.
    rewrite Ptrofs.unsigned_zero.    
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl. auto.
    (* wt_footprint *)
    simpl. auto.
    (* eapply place_footprint_wt in FP. rewrite PTY in FP. inv FP.  *)
    (* simpl. auto. *)
Admitted.

End COMP_ENV.


(* if a place passes must_movable checking, then the location of this
place is sem_wt_loc. wt_footprint here is used to make sure that the
footprint of this place (obtained by get_loc_footprint_map) has the
same structure as its type, which is used to prevent dynamic footprint
splitting! *)
Lemma movable_place_sem_wt: forall ce ce1 fp fpm m e own p b ofs init uninit universe
    (MM: mmatch fpm ce m e own)    
    (* p owns the ownership chain. To finish this proof, we need to
    first fix some error in must_movable *)    
    (POWN: must_movable ce1 init uninit universe p = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp))
    (WTFP: wt_footprint ce (typeof_place p) fp)
    (EXTEND: ce_extends ce1 ce),
    sem_wt_loc ce m fp b ofs
.
Proof.
  intros ce. intros c. pattern c. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold must_movable, must_movable_fix in *.
  erewrite unroll_Fix in *.
  destruct (typeof_place p) eqn: PTY; simpl in POWN; try congruence.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  (* Tbox *)
  - destruct (must_init init uninit universe p) eqn: INIT; try congruence.
    destruct (is_full universe p) eqn: PFULL.
    (* p is full: it must be sem_wt *)
    eapply MM. eauto. eapply must_init_sound; eauto.
    erewrite <- is_full_same; eauto. eapply sound_own_universe. eauto.
    (* adhoc generalization *)
    clear PFULL.
    generalize dependent p. generalize dependent b.
    generalize dependent fp. generalize dependent ofs.
    induction t; intros; simpl in *; try congruence.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p Tunit)) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). inv WT; inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    (* The same as Tunit case *)
    + admit.
    + admit.
    + admit.
    (* Induction case *)
    + destruct (must_init init uninit universe (Pderef p (Tbox t))) eqn: INIT2; try congruence.
      destruct (is_full universe (Pderef p (Tbox t))) eqn: PFULL1.
      (* case1: deref p is full: it must be sem_wt *)
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor; eauto. econstructor; eauto.
      destruct (path_of_place p) eqn: POP.
      eapply MM. instantiate (1 := Pderef p (Tbox t)).
      simpl. rewrite POP. erewrite get_loc_footprint_map_app. eauto.
      eauto. simpl. auto.
      eapply must_init_sound; eauto.
      erewrite <- is_full_same; eauto. eapply sound_own_universe. eauto.
      (* case2: deref p is not full *)      
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      eapply IHt; eauto. simpl. auto.
      (* get_loc_footprint_map *)
      simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto.
    (* Tstruct *)
    + destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
      (* fp is not empty *)
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      clear GCO. generalize P as P1. intros P1. eapply EXTEND in P. rewrite P in *.
      econstructor. simpl. eauto. eauto. econstructor; eauto.
      (* two cases *)
      destruct (must_init init uninit universe (Pderef p (Tstruct l id1))) eqn: INIT1; try congruence.
      (** Case1 check that p is full so we can derive sem_wt_loc by mmatch *)
      destruct (is_full universe (Pderef p (Tstruct l id1))) eqn: FULL; try congruence.
      (* construct footprint of Pderef p to use mmatch *)
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tstruct l id1))) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). simpl in *.
      (* prove sem_wt_loc: first eliminate Tbox *)
      eapply WTLOC1.
      erewrite <- is_full_same. eauto. eapply sound_own_universe; eauto.
      eauto.
      (** Case2: p is not in the universe *)
      erewrite forallb_forall in POWN.
      (** Get the structure of fp by wt_footprint *)
      inv WT; simpl in *; try congruence. 
      eapply sem_wt_struct. intros.
      (* replace fty with (typeof_place (Pfield (Pderef p (Tstruct l id1)) fid fty)) by auto. *)
      (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
      exploit WT2; eauto. intros (fty & A & B & C).
      eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
      eapply PTree_removeR. eauto. eauto.
      assert (INMEM: In (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield (Pderef p (Tstruct l id1)) fid fty, fty)) (co_members co))).
      (** TODO *)
      { admit. }
      generalize (POWN (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) INMEM).
      instantiate (1 := Pfield (Pderef p (Tstruct l id1)) fid fty).
      eauto.
      auto.
      (* get_loc_footprint_map *)
      simpl. destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_app; eauto.
      eapply get_loc_footprint_map_app; eauto.
      simpl. eauto. simpl. rewrite H. auto.
      (* wt_footprint *)
      simpl. auto.
      (* ce_extend *)
      admit.
    (* Tvariant *)
    + destruct (ce1 ! i) eqn: CO; try congruence.      
      eapply andb_true_iff in POWN. destruct POWN as (INIT1 & FULL).
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). (* rewrite PTY in *. *)
      inv WTFP; inv BM; simpl in *; try congruence.
      eapply EXTEND in CO. rewrite CO in *.      
      econstructor; eauto. 
      econstructor; eauto.
      cut (is_full own.(own_universe) (Pderef p (Tvariant l i)) = true).
      eapply MM.
      simpl. destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_app; eauto.      
      eapply must_init_sound; eauto.
      erewrite <- is_full_same; eauto.
      eapply sound_own_universe; eauto.
      
  (* Tstruct *)
  - destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
    destruct (must_init init uninit universe p) eqn: INIT; try congruence.
    (** Case1 check that p is full so we can derive sem_wt_loc by mmatch *)
    destruct (is_full universe p) eqn: FULL; try congruence.
    exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & WTLOC).  eapply WTLOC.
    erewrite <- is_full_same. eauto. eapply sound_own_universe; eauto.
    (** Case2: p is not in the universe *)
    erewrite forallb_forall in POWN.
    (** Get the structure of fp by wt_footprint *)
    inv WTFP; simpl in *; try congruence.
    eapply sem_wt_struct. intros.
    (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
    exploit WT2; eauto. intros (fty & A & B & C).
    eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
    eapply PTree_removeR. eauto. eauto.
    assert (INMEM: In (Pfield p fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield p fid fty, fty)) (co_members co))).
    (** TODO *)
    { admit. }
    generalize (POWN (Pfield p fid fty, fty) INMEM).
    instantiate (1 := (Pfield p fid fty)). eauto.    
    auto.
    (* place_footprint *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app; eauto.
    simpl. rewrite H. auto.
    (* wt_footprint *)
    simpl. auto.
    (* ce_extend *)
    admit.
  (* Tvariant *)
  - destruct (ce1 ! i) eqn: CO; try congruence.
    eapply andb_true_iff in POWN. destruct POWN as (INIT & FULL).
    exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & WTLOC). 
    inv WTFP; inv BM; simpl in *; try congruence. 
    eapply WTLOC.
    erewrite <- is_full_same; eauto.
    eapply sound_own_universe; eauto.
Admitted.

   
(* properties of place_dominator *)

Lemma place_dominator_local: forall p p',
    place_dominator p = Some p' ->
    local_of_place p = local_of_place p'.
Proof.
  induction p; simpl; auto.
  congruence.
  intros. inv H. auto.
  intros. inv H. auto.
Qed.

Lemma place_dominator_strict_prefix: forall p p',
    place_dominator p = Some p' ->
    is_prefix_strict p' p = true.
Proof.
  induction p; simpl; auto; try congruence; intros.
  - exploit IHp. eauto. intros A. eapply is_prefix_strict_trans. eauto.
    unfold is_prefix_strict. simpl. destruct (place_eq p p). auto. congruence.
  - inv H.
    unfold is_prefix_strict. simpl. destruct (place_eq p' p'). auto. congruence.
  - inv H.
    unfold is_prefix_strict. simpl. destruct (place_eq p' p'). auto. congruence.
Qed.


Section MOVE_CHECK.

Variable prog: program.
Variable w: wt_rs_world.
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Let L := semantics prog se.
Let ge := globalenv se prog.

(* composite environment *)
Let ce := ge.(genv_cenv).

Let AN : Type := (PMap.t IM.t * PMap.t IM.t * PathsMap.t).
                                                                  
Let match_stmt (ae: AN) body cfg s := match_stmt get_init_info ae (move_check_stmt ce) (check_expr ce) body cfg s s.

Hypothesis CONSISTENT: composite_env_consistent ce.

(** Try to prove eval_expr_sem_wt  *)

Lemma is_prefix_paths_app: forall p1 p2,
    is_prefix p1 p2 = true ->
    fst (path_of_place p1) = fst (path_of_place p2)
    /\ exists phl, snd (path_of_place p2) = snd (path_of_place p1) ++ phl.
Admitted.

Lemma move_place_init_is_init: forall p p1 own,
    is_init (move_place own p1) p = true ->
    is_init own p = true.
Admitted.

Lemma move_children_still_init: forall own p1 p2 p3,
    is_init (move_place own p1) p3 = true ->
    is_prefix p1 p2 = true ->
    is_init (move_place own p2) p3 = true.
Admitted.

Lemma place_dominators_valid_owner_incl: forall p,
    incl (place_dominators (valid_owner p)) (place_dominators p).
Proof.
  induction p; simpl; auto; try apply incl_refl.
  - red. intros. simpl. right. auto.
Qed.

Lemma place_dominators_downcast_incl: forall p fid fty,
    incl (place_dominators p) (place_dominators (Pdowncast p fid fty)).
Proof.
  induction p; simpl; auto; intros; try apply incl_nil_l.
  - red. intros. simpl. right; auto.
  - red. intros. simpl. right; auto.
  - apply incl_refl.
Qed.
  
(* what if move out a downcast? Use place_dominators_valid_owner_incl
and place_dominators_downcast_incl ! *)
Lemma move_place_dominator_still_init: forall p own,    
    dominators_is_init own p = true ->
    dominators_is_init (move_place own p) p = true.
Proof.
  induction p; intros; unfold dominators_is_init in *; auto.
  - simpl in H. 
    exploit IHp.
    eauto. intros.
    eapply forallb_forall. intros.
    eapply forallb_forall in H0. 2: eauto.
    eapply move_children_still_init. eauto.
    unfold is_prefix. simpl. destruct (place_eq p p); try congruence.
    eapply orb_true_r.
  - simpl in H.
    eapply andb_true_iff in H. destruct H.
    exploit IHp.
    eauto. intros.
    eapply forallb_forall. intros.
    simpl in H2. destruct H2; subst.
    (* case1 *)
    eapply move_irrelavent_place_still_owned. auto.
    eapply is_prefix_antisym. unfold is_prefix_strict. simpl.
    destruct place_eq. auto. congruence.
    (* case2 *)
    eapply forallb_forall in H1. 2: eauto.
    eapply move_children_still_init. eauto.
    unfold is_prefix. simpl. destruct (place_eq p p); try congruence.
    eapply orb_true_r.
  - exploit IHp. 
    (* H can imply the premise of IHp *)
    eapply forallb_forall. intros.
    eapply forallb_forall in H. eauto. eapply place_dominators_downcast_incl. auto.
    intros A.
    (* valid_owner p is init *)
    simpl in H.  eapply andb_true_iff in H. destruct H.
    simpl. eapply andb_true_iff. split.
    eapply move_irrelavent_place_still_owned. eauto.
    eapply is_prefix_antisym.
    eapply is_prefix_strict_trans_prefix2. eapply is_prefix_valid_owner.
    unfold is_prefix_strict. simpl.
    destruct (place_eq p p); try congruence. auto.    
    (* p's dominators are init so the dominators of (valid_owner p) are init *)
    eapply forallb_forall. intros.
    eapply forallb_forall in A. eapply move_children_still_init. eauto.
    unfold is_prefix. simpl. destruct (place_eq p p); try congruence.
    simpl. eapply orb_true_r.
    eapply place_dominators_valid_owner_incl. auto.
Qed.


Lemma is_not_prefix_disjoint: forall p1 p2,
    is_prefix p1 p2 = false ->
    is_prefix p2 p1 = false ->
    fst (path_of_place p1) <> fst (path_of_place p2) \/
      paths_disjoint (snd (path_of_place p1)) (snd (path_of_place p2)).
Proof.
  induction p1; intros; destruct (path_of_place p2) eqn: POP2; simpl in *.
  - unfold is_prefix in *.
    simpl in *.
    admit.
  - destruct (path_of_place p1) eqn: POP1.
    unfold is_prefix in *.
    simpl in *.
    destruct (place_eq p1 p2) in H0; simpl in H0; try congruence. subst.
    erewrite orb_true_r in H0. congruence.
    destruct in_dec in H0; simpl in H0.
    erewrite orb_true_r in H0. congruence.
    (** p2 may be a children of p1 but p2 is not a children of p1.i  *)
    destruct (in_dec place_eq p1 (parent_paths p2)); simpl in *.
    (** IMPORTANT TODO: we need to say that paths of p2 is (l0 ++
    [ph_field j] ++ ...)  where j is not equal to i *)
    * admit.
    * (* use I.H. *)
      exploit IHp1. instantiate (1 := p2).
      eapply orb_false_iff. split. destruct (place_eq p1 p2); try congruence; auto.
      eapply not_true_iff_false. intro. eapply n1. eapply proj_sumbool_true. eauto.
      eapply orb_false_iff. split. destruct (place_eq p1 p2); try congruence; auto.     
      eapply not_true_iff_false. intro. eapply n2. symmetry. eapply proj_sumbool_true.
      eauto.
      eapply not_true_iff_false. intro. eapply n0. eapply proj_sumbool_true. eauto.  
      intros [A|B].
    + rewrite POP2 in A. simpl in *. auto.
    + right. rewrite POP2 in B. simpl in *.
      (** TODO: paths_disjoint_app *)
      admit.
  - admit.
  - admit.
Admitted.      

  
(* Inductive not_shallow_prefix_paths: list path -> Prop := *)
(* | not_shallow_prefix_paths1: forall phs, *)
(*     not_shallow_prefix_paths (ph_deref :: phs) *)
(* | not_shallow_prefix_paths2: forall phs ph, *)
(*     not_shallow_prefix_paths phs -> *)
(*     not_shallow_prefix_paths (ph :: phs). *)

Definition not_shallow_prefix_paths (phl: list path) : Prop :=
  In ph_deref phl.

(* Set [vfp] to the path [phl] of [fp1], if [phl] is not shallow paths
which means that if contains dereference, then [fp2] is still
bmatch *)
Lemma bmatch_set_not_shallow_paths: forall phl m b ofs fp1 fp2 vfp,
    bmatch ce m b ofs fp1 ->
    set_footprint phl vfp fp1 = Some fp2 ->
    not_shallow_prefix_paths phl ->
    bmatch ce m b ofs fp2.
Proof.
  induction phl; intros; simpl in *; try congruence.
  red in H1. inv H1.
  red in H1. inv H1.
  - destruct fp1; try congruence.
    destruct (set_footprint phl vfp fp1); try congruence. inv H0.
    inv H. econstructor; eauto.
  - destruct a; try congruence.
    + destruct fp1; try congruence.
      destruct (set_footprint phl vfp fp1) eqn: A; try congruence.      
      inv H0. inv H. econstructor; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: A; try congruence.
      repeat destruct p.
      exploit find_fields_some. eapply A.
      intros (B1 & B2). subst.
      destruct (set_footprint phl vfp f) eqn: B; try congruence.
      inv H0. inv H. econstructor.
      intros.
      exploit find_fields_some. eauto. intros (C1 & C2).
      eapply in_map_iff in C2.
      destruct C2 as (x & C2 & C3).
      destruct x. destruct p.
      destruct ident_eq in C2; inv C2.
      (* if fid is equal to i *)
      exploit find_fields_same_offset. eauto. intros (vfp' & E1).
      rewrite A in E1. inv E1.
      exploit FMATCH. eapply A. intros D1.
      eapply IHphl; eauto.
      (* if fid <> i *)
      eapply FMATCH. instantiate (1 := fid).
      (* prove that changing the footprint in i does not affect the
      footprint in fid if i <> fid *)
      eapply find_fields_different_field; eauto.
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct (ident_eq i id) in H0; try congruence; subst.
      destruct (list_eq_dec ident_eq l orgs) in H0; try congruence; subst.
      destruct (ident_eq fid fid0) in H0; try congruence; subst.
      destruct (set_footprint phl vfp fp1) eqn: S in H0; try congruence.
      inv H0. inv H.
      econstructor; eauto.
Qed.

Lemma in_parent_paths_not_empty_sufix: forall p2 p1 id l1,
    In p1 (parent_paths p2) ->
    path_of_place p1 = (id, l1) ->
    exists l2, path_of_place p2 = (id, l1 ++ l2) /\
            l2 <> nil.
Proof.
  induction p2; intros; simpl in *; try contradiction.
  - destruct H; subst.
    + rewrite H0. exists [ph_field i]. split. eauto.
      congruence.
    + destruct (path_of_place p2) eqn: POP2.
      exploit IHp2; eauto. intros (l2 & A1 & A2).
      inv A1. exists (l2 ++ [ph_field i]). split.
      f_equal. rewrite app_assoc. auto.
      destruct l2; simpl; congruence.
  - destruct H; subst.
    + rewrite H0. exists [ph_deref]. split. eauto.
      congruence.
    + destruct (path_of_place p2) eqn: POP2.
      exploit IHp2; eauto. intros (l2 & A1 & A2).
      inv A1. exists (l2 ++ [ph_deref]). split.
      f_equal. rewrite app_assoc. auto.
      destruct l2; simpl; congruence.
  - destruct H; subst.
    + rewrite H0. exists [ph_downcast (typeof_place p1) i]. split. eauto.
      congruence.
    + destruct (path_of_place p2) eqn: POP2.
      exploit IHp2; eauto. intros (l2 & A1 & A2).
      inv A1. exists (l2 ++ [ph_downcast (typeof_place p2) i]). split.
      f_equal. rewrite app_assoc. auto.
      destruct l2; simpl; congruence.
Qed.
      
Lemma not_nil_app_end {A: Type} : forall (l: list A),
    l <> nil ->
    exists a l', l = l' ++ [a].
Proof.
  induction l. congruence.
  intros. destruct l.
  exists a, nil. eauto.
  exploit IHl; eauto. congruence.
  intros (a1 & l' & A1). exists a1, (a::l'). rewrite A1. auto.
Qed.

Lemma path_of_not_shallow_prefix_aux: forall p2 p1 l1 l2 id
    (NEQ: p1 <> p2)
    (NSHA: ~ In p1 (shallow_parent_paths p2))
    (* is_prefix here is used to avoid syntatic well-typedness *)
    (PRE: In p1 (parent_paths p2))
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2))
    (NOTEMP: l2 <> nil),
    not_shallow_prefix_paths l2.
Proof.
  induction p2; simpl; intros.
  - inv POP2. symmetry in H1. eapply app_eq_nil in H1. destruct H1.
    subst. destruct p1; simpl in POP1; inv POP1; try contradiction.
  - eapply Decidable.not_or in NSHA.
    destruct NSHA as (A1 & A2); destruct PRE as [B1|B2]; subst; try congruence.
    destruct (path_of_place p2) eqn: POP3. inv POP2.
    eapply not_nil_app_end in NOTEMP.
    destruct NOTEMP as (a & l2' & C1). subst.
    erewrite app_assoc in H1. eapply app_inj_tail in H1.
    destruct H1. subst.
    (* show that l2' is also not empty *)
    exploit in_parent_paths_not_empty_sufix; eauto.
    intros (l2'' & C2 & C3). rewrite POP3 in C2. inv C2.
    eapply app_inv_head in H0. subst.
    exploit IHp2. 1-6: eauto. intros.
    red. eapply in_app. eauto.
  - destruct (path_of_place p2) eqn: POP3. inv POP2.
    destruct PRE as [B1|B2]; subst; try congruence.
    + eapply not_nil_app_end in NOTEMP.
      destruct NOTEMP as (a & l2' & C1). subst.
      erewrite app_assoc in H1. eapply app_inj_tail in H1.
      destruct H1. subst. eapply in_app; auto. right. econstructor; auto.
    + eapply not_nil_app_end in NOTEMP.
      destruct NOTEMP as (a & l2' & C1). subst.
      erewrite app_assoc in H1. eapply app_inj_tail in H1.
      destruct H1. subst.
      eapply in_app; auto. right. econstructor; auto.
  - eapply Decidable.not_or in NSHA.
    destruct NSHA as (A1 & A2); destruct PRE as [B1|B2]; subst; try congruence.
    destruct (path_of_place p2) eqn: POP3. inv POP2.
    eapply not_nil_app_end in NOTEMP.
    destruct NOTEMP as (a & l2' & C1). subst.
    erewrite app_assoc in H1. eapply app_inj_tail in H1.
    destruct H1. subst.
    (* show that l2' is also not empty *)
    exploit in_parent_paths_not_empty_sufix; eauto.
    intros (l2'' & C2 & C3). rewrite POP3 in C2. inv C2.
    eapply app_inv_head in H0. subst.
    exploit IHp2. 1-6: eauto. intros.
    red. eapply in_app. eauto.
Qed.

Lemma path_of_not_shallow_prefix: forall p1 p2 l1 l2 id
    (NSHA: is_shallow_prefix p1 p2 = false)
    (* is_prefix here is used to avoid syntatic well-typedness *)
    (PRE: is_prefix p1 p2 = true)
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2)),
    not_shallow_prefix_paths l2.
Proof.
  intros.
  unfold is_shallow_prefix in NSHA.
  unfold is_prefix in PRE.
  destruct place_eq; simpl in *; try congruence.
  destruct in_dec in *; simpl in *; try congruence.
  destruct in_dec in *; simpl in *; try congruence.
  exploit in_parent_paths_not_empty_sufix; eauto.
  intros (l3 & A1 & A2). rewrite POP2 in A1. inv A1.
  eapply app_inv_head in H0. subst.
  eapply path_of_not_shallow_prefix_aux; eauto.
Qed.

Lemma path_of_not_shallow_prefix_reverse_aux: forall p2 p1 l1 l2 id
    (NSHA: In p1 (shallow_parent_paths p2))   
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2)),
    ~ not_shallow_prefix_paths l2.
Proof.
    induction p2; simpl; intros.
  - inv POP2. symmetry in H1. eapply app_eq_nil in H1. destruct H1.
    subst. destruct p1; simpl in POP1; inv POP1; try contradiction.    
  - destruct NSHA as [A1 | A2]; subst; try congruence.
    + rewrite POP1 in POP2. inv POP2.
      eapply app_inv_head in H0. subst.
      intro. red in H. inv H; try congruence. inv H0.
    + destruct (path_of_place p2) eqn: POP3. inv POP2.
      destruct (length l2) eqn: LEN.
      * eapply length_zero_iff_nil in LEN. subst.
        intro. inv H.
      * eapply length_S_inv in LEN.
        destruct LEN as (l' & a & B1 & B2). subst.
        rewrite app_assoc in H1. eapply app_inj_tail in H1.
        destruct H1. subst.
        intro. red in H. eapply in_app in H. destruct H.
        eapply IHp2; eauto. inv H; try congruence. inv H0.
  - contradiction.
  - destruct NSHA as [A1 | A2]; subst; try congruence.
    + rewrite POP1 in POP2. inv POP2.
      eapply app_inv_head in H0. subst.
      intro. red in H. inv H; try congruence. inv H0.
    + destruct (path_of_place p2) eqn: POP3. inv POP2.
      destruct (length l2) eqn: LEN.
      * eapply length_zero_iff_nil in LEN. subst.
        intro. inv H.
      * eapply length_S_inv in LEN.
        destruct LEN as (l' & a & B1 & B2). subst.
        rewrite app_assoc in H1. eapply app_inj_tail in H1.
        destruct H1. subst.
        intro. red in H. eapply in_app in H. destruct H.
        eapply IHp2; eauto. inv H; try congruence. inv H0.
Qed.

    
(* If the path contains no deref, then p1 must be shallow prefix of
p2. This lemma is unused *)
Lemma path_of_not_shallow_prefix_reverse: forall p1 p2 l1 l2 id
    (NSHA: not_shallow_prefix_paths l2)
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2)),
    is_shallow_prefix p1 p2 = false.
Proof.
  intros.
  unfold is_shallow_prefix.
  destruct place_eq; simpl in *; try congruence.
  (* p1 = p2 *)
  subst. rewrite POP1 in POP2. inv POP2.
  rewrite (app_nil_end l1) in H0 at 1. eapply app_inv_head in H0.
  subst. inv NSHA.
  (* p1 <> p2 *)    
  destruct in_dec in *; simpl in *; try congruence.
  exfalso. eapply path_of_not_shallow_prefix_reverse_aux; eauto.
Qed.  

(* The location from a not_shallow_prefix path must be in the
        footprint being gotten *)
Lemma get_loc_footprint_not_shallow_path: forall phl fp1 b1 ofs1 b2 ofs2 fp2,
    not_shallow_prefix_paths phl ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    In b2 (footprint_flat fp1).
Admitted.


(** IMPORTANT TODO: if (own_env, fpm (or abstract memory), mem)
satisfies mmatch, then moving out the valid_owner of a place [p]
preserves mmatch properties. *)
Lemma mmatch_move_place_sound: forall p fpm1 fpm2 m le own
    (MM: mmatch fpm1 ce m le own)
    (WF: wf_own_env own)
    (* This property ensure that the place to be moved out has shallow
    prefix (its location) in the universe. This property is ensured by
    must_movable *)
    (EX: Paths.Exists (fun p1 => is_shallow_prefix (valid_owner p) p1 = true) (PathsMap.get (local_of_place p) own.(own_universe)))
    (CLR: clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2),
    (* valid_owner makes this proof difficult *)
    mmatch fpm2 ce m le (move_place own (valid_owner p)).
Proof.
  intros. red. intros until fp.
  intros PFP INIT.
  set (p1:= (valid_owner p)) in *.
  destruct (is_prefix p1 p0) eqn: PRE.
  (* impossible *)
  - unfold is_init, move_place, remove_place in INIT. simpl in INIT.
    eapply Paths.mem_2 in INIT.
    erewrite PathsMap.gsspec in INIT.
    destruct peq.
    * eapply Paths.filter_2 in INIT.
      rewrite PRE in INIT. simpl in INIT. congruence.
      red. solve_proper.
    * unfold p1 in *.
      rewrite valid_owner_same_local in n.
      erewrite <- (is_prefix_same_local (valid_owner p) p0) in n.
      erewrite valid_owner_same_local in n.
      congruence.
      auto.      
  (* valid_owner p is not a prefix of p0 *)
  -  destruct (is_prefix p0 p1) eqn: PRE1.
    (* p0 is prefix of p1 (valid_owner p). clear p's footprint also
      affects the footprint of p0 *)
    * unfold clear_footprint_map in CLR.
      destruct (get_loc_footprint_map le (path_of_place p1) fpm1) eqn: GET1; try congruence.
      repeat destruct p2.
      destruct (path_of_place p1) eqn: POP.
      exploit is_prefix_paths_app. eapply PRE1. rewrite POP.
      destruct (path_of_place p0) eqn: POP2. simpl.
      intros (A & (phl & B)). subst.
      (** set_footprint_map_app_inv is important TODO  *)
      exploit get_loc_footprint_map_app_inv. eapply GET1.
      intros (b2 & ofs2 & fp3 & A & B).
      exploit get_set_footprint_map_app_inv. eapply A. eauto.
      intros (fp4 & C & D).
      rewrite PFP in C. inv C.
      (* use mmatch *)
      exploit MM. erewrite POP2. eauto.
      eapply move_place_init_is_init. eauto.
      intros (BM & FULL).
      (* We need to say that p must not be shallow children of p0,
      otherwise moving out the valid owner of p would make p0
      partially owned. But p0 is owned from the premise of mmatch *)
      (** TODO: p0 must be not a shallow prefix of p1 because there is
      some shallow children of p1 in the universe which is guaranteed
      by the must_movable of p1 and some well-formedenss of universe
      (i.e., if p is in the universe, so p's shallow prefix is not in
      the universe) . So the extra paths [phl] must contain some
      ph_deref and updating fp3 to fp4 does not affect the bmatch in
      (b2, ofs2) because the update takes place in other block *)
      assert (NOT_SHALLOW: is_shallow_prefix p0 p1 = false).
      { destruct EX as (p2 & A1 & A2).
        destruct (is_shallow_prefix p0 p1) eqn: SHA; auto.
        exploit is_shallow_prefix_trans. eapply SHA. eauto.
        intros B1. rewrite <- B1.
        eapply wf_own_universe_shallow. eauto.
        erewrite in_universe_eq.
        eapply is_init_in_universe. eauto.
        eapply move_place_eq_universe. 
        unfold in_universe. eapply Paths.mem_1; auto.
        erewrite <- is_shallow_prefix_same_local. 2: eapply B1.
        erewrite <- valid_owner_same_local in A1.
        erewrite is_shallow_prefix_same_local. eauto.
        eauto. }
      assert (NOT_SHALLOW_PHL: not_shallow_prefix_paths phl).
      { eapply path_of_not_shallow_prefix; eauto. }
      exploit bmatch_set_not_shallow_paths; eauto. intros BM1. split.
      auto.
      (** is_full is not possible because p2 is in the universe (add
        a premise in this lemma) *)
      destruct EX as (p2 & IN & SPRE).
      intros FULL1. unfold is_full, is_full_internal in FULL1.
      eapply Paths.for_all_2 in FULL1. exploit FULL1.
      erewrite is_prefix_same_local. 2: eapply PRE1.
      unfold p1. erewrite valid_owner_same_local. eauto.
      intros NPRE.
      assert (PRE01: is_prefix_strict p0 p1 = true).
      { unfold is_prefix_strict. unfold is_prefix in PRE, PRE1.
        eapply orb_true_iff in PRE1. destruct PRE1.
        destruct (place_eq p0 p1); try congruence. subst.
        destruct (place_eq p1 p1) in PRE; simpl in PRE; try congruence.
        destruct (place_eq p1 p0); simpl in * ;try congruence.
        auto. }
      assert (PRE02: is_prefix_strict p0 p2 = true).
      { eapply is_prefix_strict_trans_prefix. eauto.
        eapply is_shallow_prefix_is_prefix. eauto. }
      rewrite PRE02 in NPRE. simpl in NPRE. congruence.
      red. solve_proper.
    (* p0 is not prefix of p1 *)
    * unfold clear_footprint_map in CLR.
      destruct (get_loc_footprint_map le (path_of_place p1) fpm1) eqn: GET1; try congruence.
      repeat destruct p2.      
      (* no relation between p0 and (valid_owner p), so two cases *)
      destruct (ident_eq (local_of_place p1) (local_of_place p0)).
     + exploit is_not_prefix_disjoint. eapply PRE. eapply PRE1.
       intros [A|B].
       -- do 2 erewrite <- local_of_paths_of_place in A. congruence.
       -- do 2 erewrite local_of_paths_of_place in e.
          destruct (path_of_place p1) eqn: C. destruct (path_of_place p0) eqn: D.
          simpl in e. subst.
          exploit get_set_disjoint_paths. eauto.
          eauto. instantiate (1:= le). intros E.
          cbn [snd] in *.
          rewrite PFP in E.
          (* use mmatch *)
          rewrite <- D in E.
          exploit MM. eauto.
          eapply move_place_init_is_init. eauto.
          intros (BM & WTLOC). auto.                  
     + destruct (path_of_place p1) eqn: B. destruct (path_of_place p0) eqn: C.       
       exploit get_set_different_local; eauto.
       replace (local_of_place p1) with i. eauto.
       erewrite local_of_paths_of_place. rewrite B. auto.
       replace (local_of_place p0) with i0.
       instantiate (1 := l0). instantiate (1 := le).
       intros D. rewrite PFP in D.
       2: { erewrite local_of_paths_of_place. rewrite C. auto. }
       (* use mmatch *)
       rewrite <- C in D.
       exploit MM. eauto.
       eapply move_place_init_is_init. eauto.
       intros (BM & WTLOC). auto.
Qed.       
    
(** dereferce a semantically well typed location produces well typed value *)
Lemma deref_sem_wt_loc_sound: forall m fp b ofs ty v               
    (WT: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs))
    (* alignment *)
    (AL: (alignof ce ty | (Ptrofs.unsigned ofs)))
    (WTFP: wt_footprint ce ty fp)
    (DE: deref_loc ty m b ofs v),
    sem_wt_val ce m fp v.
Proof.
  intros. destruct ty; inv WTFP; inv WT; simpl in *; try inv MODE;
  inv DE; simpl in *; try congruence. 
  (* struct *)
  - econstructor. eapply sem_wt_struct; eauto. auto.
  (* enum *)
  - econstructor. eapply sem_wt_enum; eauto. auto.
Qed.
  
(* The result of eval_expr is semantically well typed *)

(* The footprint must be fp_emp in pexpr *)
Lemma eval_pexpr_sem_wt: forall fpm m le own pe v init uninit universe
    (MM: mmatch fpm ce m le own)
    (EVAL: eval_pexpr ce le m pe v)
    (SOUND: sound_own own init uninit universe)
    (CHECK: move_check_pexpr init uninit universe pe = true),
    sem_wt_val ce m (fp_scalar (typeof_pexpr pe)) v.
Admitted.

(* used to prove the premise of [mmatch_move_place_sound] *)
Lemma must_movable_exists_shallow_prefix: forall ce init uninit universe p,
    must_movable ce init uninit universe p = true ->
    Paths.Exists (fun p1 : Paths.elt => is_shallow_prefix (valid_owner p) p1 = true) (PathsMap.get (local_of_place p) universe).
Admitted.

  
Lemma set_wt_footprint: forall phl ty1 vty ce (WTPH: wt_path ce ty1 phl vty) fp1 vfp fp2,
    set_footprint phl vfp fp1 = Some fp2 ->
    wt_footprint ce ty1 fp1 ->
    (* we should not say that vfp is well typed in ce! *)
    wt_footprint ce vty vfp ->
    wt_footprint ce ty1 fp2.
Proof.
  induction 1; intros until fp2; intros SET WTFP1 WTFP2.
  - simpl in *. inv SET. auto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1.
    inv B1.
    eapply IHWTPH. eauto. eauto.
    econstructor. simpl in WP2. inv WP2. auto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    destruct (find_fields fid fpl) eqn: FIND; try congruence.
    repeat destruct p. inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1.
    inv B1.
    eapply IHWTPH. eauto. eauto.
    (* prove wt_footprint of the struct footprint *)
    econstructor; eauto.
    + intros. rewrite WP2 in CO. inv CO.
      exploit WT1. eauto.
      intros (ffp & fofs & C1 & C2 & C3).
      erewrite find_fields_set_spec with (fofs:= fofs) (ffp:= ffp); eauto.
      destruct peq.
      * subst. exists vfp, fofs.
        repeat apply conj; auto.
        rewrite WP3 in H. inv H. auto.
      * eauto. 
    + intros. rewrite WP2 in CO. inv CO.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      destruct (peq i fid0).
      * subst.
        exploit WT2.  eauto. intros (fty & F1 & F2 & F3).
        erewrite find_fields_set_spec with (fofs:= z) (ffp:= f) in H; eauto.
        inv H. destruct peq; try congruence. eauto.
      * exploit find_fields_different_field. eauto. eauto.
        intros FIND1.
        exploit WT2.  eauto. intros (fty & F1 & F2 & F3).
        eauto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    destruct ident_eq in A2; try congruence.
    destruct list_eq_dec in A2; try congruence.
    destruct ident_eq in A2; try congruence.
    inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1. 
    inv B1. eapply IHWTPH. eauto. auto.
    econstructor; eauto.
    rewrite WP2 in CO. inv CO. rewrite WP3 in FTY. inv FTY.
    auto.
Qed.

(** IMPORTANT TODO: wf_env remain valid if we set a wt_footprint *)
Lemma wf_env_set_wt_footprint: forall p fpm1 fpm2 ce e fp
    (WFENV: wf_env fpm1 ce e)
    (* how to know the type match the type located in the path of the
    footprint map? *)
    (WTFP: wt_footprint ce (typeof_place p) fp)
    (WTP: wt_place e ce p)
    (SET: set_footprint_map (path_of_place p) fp fpm1 = Some fpm2),
    wf_env fpm2 ce e.
Proof.
  intros.
  destruct (path_of_place p) eqn: POP.
  unfold set_footprint_map in SET.
  destruct (fpm1 ! i) eqn: A1; try congruence.
  destruct (set_footprint l fp f) eqn: A2; try congruence.
  inv SET.
  constructor. intros. exploit wf_env_footprint; eauto.
  intros (fp1 & B1 & B2).
  rewrite PTree.gsspec.
  destruct peq; subst.
  - exists f0.
    rewrite A1 in B1. inv B1.
    split; auto.
    (* prove wt_footprint after setting *)
    eapply set_wt_footprint.
    eapply wt_place_wt_path; eauto.
    eauto. auto. auto.
  - eauto.
Qed.


Lemma find_fields_clear_footprint1: forall fpl fid fofs ffp,
    find_fields fid fpl = Some (fid, fofs, ffp) ->
    find_fields fid
      (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl) =
      Some (fid, fofs, (clear_footprint_rec ffp)).
Proof.
  induction fpl; simpl; intros; try congruence.
  destruct a. destruct p.
  destruct ident_eq.
  - subst. inv H. auto.
  - eauto.
Qed.

Lemma find_fields_clear_footprint2: forall fpl fid fofs ffp,
    find_fields fid
      (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl) =
      Some (fid, fofs, ffp) ->
    exists ffp', find_fields fid fpl = Some (fid, fofs, ffp')
            /\ ffp = clear_footprint_rec ffp'.
Proof.
  induction fpl; simpl; intros; try congruence.
  destruct a. destruct p.
  destruct ident_eq.
  - subst. inv H. eauto.
  - eauto.
Qed.

Lemma wt_footprint_clear: forall fp ce ty,
    wt_footprint ce ty fp ->
    wt_footprint ce ty (clear_footprint_rec fp).
Proof.
  induction fp using strong_footprint_ind; intros; simpl; auto.
  - inv H. econstructor. destruct ty; simpl in *; try congruence.
  - inv H. econstructor. congruence.
  - inv H0. econstructor; eauto.
    + intros. exploit WT1; eauto.
      intros (ffp & fofs & A1 & A2 & A3).
      exists (clear_footprint_rec ffp), fofs. repeat apply conj; auto.
      * eapply find_fields_clear_footprint1. eauto.
      * exploit find_fields_some; eauto.
        intros (B1 & B2).
        eapply H; eauto.
    + intros.
      exploit find_fields_clear_footprint2; eauto.
      intros (ffp' & A1 & A2). subst.
      exploit WT2; eauto.
      intros (fty & B1 & B2 & B3).
      exists fty. repeat apply conj; auto.
      exploit find_fields_some; eauto.
      intros (C1 & C2).
      eapply H; eauto.
  - inv H. econstructor. congruence.
Qed.    
      
(* clear some footprint does not affect wf_env *)
Lemma wf_env_clear_footprint: forall fpm1 fpm2 ce e id phl,
    wf_env fpm1 ce e ->
    clear_footprint_map e (id, phl) fpm1 = Some fpm2 ->
    wf_env fpm2 ce e.
Proof.
  intros until phl. intros WF CLR.
  unfold clear_footprint_map in CLR.
  destruct (get_loc_footprint_map e (id, phl) fpm1) eqn: A; try congruence.
  repeat destruct p.
  unfold set_footprint_map in CLR.
  destruct (fpm1 ! id) eqn: A1; try congruence.
  destruct (set_footprint phl (clear_footprint_rec f) f0) eqn: A2; try congruence.
  inv CLR.
  constructor. intros. exploit wf_env_footprint; eauto.
  intros (fp1 & B1 & B2).
  rewrite PTree.gsspec.
  destruct peq; subst.
  - exists f1.
    rewrite A1 in B1. inv B1.
    split; auto. 
    (* prove wt_footprint after setting *)
    unfold get_loc_footprint_map in A. rewrite H in A. rewrite A1 in A.
    exploit get_wt_footprint_exists_wt; eauto.
    intros (ty1 & T1 & T2).  
    eapply set_wt_footprint; eauto.
    (* wt_footprint remain if clear the footprint *)
    eapply wt_footprint_clear. auto.
  - eauto.
Qed.


(** IMPORTANT TODO: The alignment of subfiled divides the
      alignment of the complete composite *)
Lemma field_alignof_divide_composite: forall fty fid co ce,
    field_type fid (co_members co) = OK fty ->
    (alignof ce fty | alignof_composite ce (co_sv co) (co_members co)).
Admitted.

(** IMPORTANT TODO: the offset of the field in the enum is align with
the alignment of the field type *)
Lemma variant_field_offset_aligned:
  forall env id fld ofs ty,
  variant_field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
Admitted.


(* The location returned by get_loc_footprint is align with the type
of the footprint *)
Lemma get_loc_footprint_align: forall phl fp1 b1 ofs1 b2 ofs2 fp2 ty1 ty2,
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    wt_footprint ce ty1 fp1 ->
    wt_path ce ty1 phl ty2 ->
    (* ofs1 must be aligned first *)
    (alignof ce ty1 | ofs1) ->
    (alignof ce ty2 | ofs2).
Proof.
  intros phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros until ty2; intros GFP WTFP WTPH AL.
  - eapply length_zero_iff_nil in LEN. subst.
    simpl in *. inv GFP.
    eapply wt_path_nil_inv in WTPH. subst. auto.
  - exploit length_S_inv; eauto. 
    intros (phl' & ph & A1 & LEN1). subst.
    exploit get_loc_footprint_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2). simpl in *.
    destruct ph.
    + destruct fp3; try congruence.
      inv G2. eapply Z.divide_0_r.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv G2.
      eapply wt_path_field_inv in WTPH as (id1 & orgs & co & A1 & A2 & A3 & A4).
      exploit get_wt_footprint_wt. eauto. eauto.
      eapply get_loc_footprint_eq. eauto. intros WTFP1.
      inv WTFP1.
      exploit find_fields_some; eauto. intros (B1 & B2). subst.
      exploit WT2; eauto.
      intros (fty & FTY & FOFS & WTFP2).
      rewrite A2 in CO. inv CO. rewrite A3 in FTY. inv FTY.
      exploit IHn; eauto. intros AL1.
      eapply Z.divide_add_r.
      (* show that the alignment of field type can be divided by the
      alignment of the struct *)      
      eapply Z.divide_trans; eauto.      
      simpl. rewrite A2.
      erewrite co_consistent_alignof; eauto.
      eapply field_alignof_divide_composite. eauto.
      (* show that the field offset is aligned *)            
      eapply field_offset_aligned; eauto.
    + destr_fp_enum fp3 ty.
      inv G2.
      eapply wt_path_downcast_inv in WTPH as (id1 & orgs1 & co & A1 & A2 & A3 & A4 & A5).
      inv A1.
      exploit get_wt_footprint_wt. eauto. eauto.
      eapply get_loc_footprint_eq. eauto. intros WTFP1.
      inv WTFP1.
      rewrite A3 in CO. inv CO. rewrite A4 in FTY. inv FTY.
      exploit IHn; eauto. intros AL1.
      eapply Z.divide_add_r.
      (* show that the alignment of field type can be divided by the
      alignment of the struct *)      
      eapply Z.divide_trans; eauto.      
      simpl. rewrite A3.
      erewrite co_consistent_alignof; eauto.
      eapply field_alignof_divide_composite. eauto.
      (* show that the field offset is aligned *)            
      eapply variant_field_offset_aligned; eauto.
Qed.
      
  
(* The location returned by get_loc_footprint is align with the type
of the footprint *)  
Lemma get_loc_footprint_map_align: forall le p fpm b ofs fp,
    get_loc_footprint_map le (path_of_place p) fpm = Some (b, ofs, fp) ->
    wf_env fpm ce le ->
    wt_place le ce p ->
    (alignof ce (typeof_place p) | ofs).
Proof.
  intros until fp. intros GFP WFENV WTP.      
  destruct (path_of_place p) eqn: POP.
  exploit wt_place_wt_local. eauto. rewrite local_of_paths_of_place. erewrite POP.
  simpl. intros (b0 & ty0 & LE).
  exploit wt_place_wt_path; eauto. intros WTPH.
  simpl in GFP. rewrite LE in GFP.
  destruct (fpm ! i) eqn: A; try congruence.
  exploit wf_env_footprint; eauto.
  intros (fp1 & A1 & A2). rewrite A in A1. inv A1.  
  eapply get_loc_footprint_align; eauto.
  eapply Z.divide_0_r.
Qed.
  
  
(* The value produced by eval_expr is semantics well-typed. We need to
update the abstract memory (split the footprint of the value from
fpm1) *)
Lemma eval_expr_sem_wt: forall fpm1 m le own1 own2 e v init uninit universe
    (MM: mmatch fpm1 ce m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_of_env le) (flat_fp_map fpm1))
    (EVAL: eval_expr ce le m e v)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_expr' ce init uninit universe e = true)
    (OWN: move_place_option own1 (moved_place e) = own2)
    (WFENV: wf_env fpm1 ce le)
    (WT: wt_expr le ce e)
    (WFOWN: wf_own_env own1),
  (** TODO: how to relate fp and fpm2 ? We should show that they are disjoint *)
  exists fp fpm2,
    sem_wt_val ce m fp v
    /\ wt_footprint ce (typeof e) fp
    (** If expr is pure expr, fp is fp_emp and not from any phs *)
    (* /\ get_footprint_map phs fpm1 = Some fp *)
    (* /\ clear_footprint_map ce phs fpm1 = Some fpm2 *)
    /\ mmatch fpm2 ce m le own2
    /\ wf_env fpm2 ce le
    (* footprint disjointness *)
    /\ list_norepet (footprint_flat fp ++ flat_fp_map fpm2)
    (* we need to ensure that fp ∪ fpm2 = fpm1 to prove
    separation. Because we do not know how fpm2 is constructed (which
    is differnet in move place or pure expression), we use this
    list_equiv to relate fpm1 and fpm2 *)
    /\ list_equiv (footprint_flat fp ++ flat_fp_map fpm2) (flat_fp_map fpm1)
    (* it is satisfied trivially because we just move out a place *)
    /\ wf_own_env own2.
Proof.
  intros. destruct e.
  (* Emoveplace *)
  - simpl in *. inv EVAL. inv WT. inv H2.
    destruct (place_eq p (valid_owner p)); subst.
    (* p is not downcast *)
    + eapply andb_true_iff in CHECK. destruct CHECK as (DONW & MOVABLE).
      exploit eval_place_sound; eauto.
      intros (pfp &  PFP & WTFP).
      (** TODO: wt_footprint implication *)
      (* location of p is sem_wt *)
      exploit movable_place_sem_wt; eauto.
      red. auto.
      intros WT_LOC. 
      (* deref sem_wt location *)
      exploit deref_sem_wt_loc_sound; eauto.
      (* prove that ofs is align with the size of p's type *)
      eapply get_loc_footprint_map_align; eauto.      
      intros WT_VAL.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2).
      { unfold clear_footprint_map.
        rewrite <- e. erewrite PFP. destruct (path_of_place p) eqn: POP.        
        exploit get_set_footprint_map_exists. eauto. instantiate (1 := clear_footprint_rec pfp).
        intros (fpm2 & A1 & A2). exists fpm2. auto. }
      destruct A as (fpm2 & CLEAR).
      destruct (path_of_place p) eqn: POP.
      exists pfp, fpm2. repeat apply conj; auto.
      eapply mmatch_move_place_sound; eauto.
      (** implication of must_movable  *)
      exploit must_movable_exists_shallow_prefix; eauto.
      intros (p2 & IN & A). exists p2. split.
      eapply sound_own_universe in IN. eauto.  eauto. auto.      
      (* wf_env *)
      rewrite <- e in *.
      rewrite POP in *.
      eapply wf_env_clear_footprint; eauto.
      (** footprint norepet  *)
      rewrite <- e in *. rewrite POP in *.
      unfold clear_footprint_map in CLEAR. rewrite PFP in CLEAR.
      exploit get_loc_footprint_map_norepet; eauto.
      intros (N1 & N2).
      exploit set_disjoint_footprint_norepet; eauto.
      eapply empty_footprint_disjoint. intros N3.
      eapply list_norepet_app. repeat apply conj; auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint_map; eauto.
      eapply empty_footprint_disjoint.
      (** list_equiv  *)
      rewrite <- e in *. rewrite POP in *.
      eapply get_clear_footprint_equiv; eauto.
      (** wf_own_env  *)
      eapply wf_own_env_move_place; eauto.      
    (* p is downcast *)
    + do 2 rewrite andb_true_iff in CHECK. destruct CHECK as ((DOWN & INIT) & FULL).
      exploit eval_place_sound; eauto.
      intros (fp1 & PFP & WTFP).
      exploit valid_owner_place_footprint; eauto.
      intros (fp2 & ofs1 & fofs1 & PFP1 & VOFS & OFSEQ).
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC).      
      exploit valid_owner_sem_wt_loc. eapply WTLOC.
      erewrite <- is_full_same; eauto. eapply sound_own_universe; eauto.
      eauto. intros WTLOC1.
      rewrite <- OFSEQ in WTLOC1.
      exploit deref_sem_wt_loc_sound; eauto.
      eapply get_loc_footprint_map_align; eauto.
      intros WT_VAL.
      set (p1 := valid_owner p) in *.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place p1) fpm1 = Some fpm2).
      { unfold clear_footprint_map.
        erewrite PFP1. destruct (path_of_place p1) eqn: POP.
        exploit get_set_footprint_map_exists. eauto.
        instantiate (1 := clear_footprint_rec fp2).
        intros (fpm2 & A1 & A2). exists fpm2. auto. }     
      destruct A as (fpm2 & CLEAR).
      destruct (path_of_place p1) eqn: POP.
      (* we have to prove the flat footprint of the valid_owner p is
      the same as p. Use the property of valid_owner_offset_footprint *)
      exploit valid_owner_footprint_flat_eq; eauto.
      intros FEQ.
      exists fp1, fpm2. repeat apply conj; auto.
      eapply mmatch_move_place_sound; eauto.
      (* exists shallow prefix *)
      exists p1. split.      
      exploit is_init_in_universe. eapply must_init_sound. eauto. eauto.
      unfold in_universe. intros. eapply Paths.mem_2.
      unfold p1 in H.
      erewrite valid_owner_same_local in H. auto.
      eapply is_shallow_prefix_refl.
      fold p1.  rewrite POP. auto.
      (* wf_env *)
      eapply wf_env_clear_footprint; eauto.
      (** footprint norepet  *)
      rewrite FEQ.
      unfold clear_footprint_map in CLEAR. rewrite PFP1 in CLEAR.
      exploit get_loc_footprint_map_norepet; eauto.
      intros (N1 & N2).
      exploit set_disjoint_footprint_norepet; eauto.
      eapply empty_footprint_disjoint. intros N3.
      eapply list_norepet_app. repeat apply conj; auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint_map; eauto.
      eapply empty_footprint_disjoint.
      (** list_equiv  *)
      rewrite FEQ.      
      eapply get_clear_footprint_equiv; eauto.
      (** wf_own_env  *)
      eapply wf_own_env_move_place; eauto.
  - exists (fp_scalar (typeof_pexpr p)), fpm1. simpl in *. subst.
    inv EVAL. inv WT.
    exploit eval_pexpr_sem_wt; eauto. intros VWT.
    repeat apply conj; auto.
    econstructor. eauto.
    red. split; intros; auto.
Qed.

(* The field type must be in the range of the struct it resides
in. This lemma require consistent composite because the size of the
struct is computed by co_sizeof instead of sizeof_struct *)
Lemma field_offset_in_range_complete: forall ce co id ofs ty,
    co_sv co = Struct ->
    composite_consistent ce co ->
    field_offset ce id (co_members co) = OK ofs ->
    field_type id (co_members co) = OK ty ->
    0 <= ofs /\ ofs + sizeof ce ty <= co_sizeof co.
Proof.
  intros.
  exploit field_offset_in_range; eauto.
  intros (S1 & S2). 
  split. lia.
  (* to show that sizeof_struct ce co0 <= co_sizeof co0 *)
  erewrite co_consistent_sizeof; eauto.
  erewrite co_consistent_alignof; eauto.
  rewrite H. simpl.
  generalize (sizeof_composite_pos ce0 Struct (co_members co)). simpl.
  generalize (alignof_composite_pos ce0 (co_members co) Struct).
  intros M1 M2. simpl in M1.
  generalize (align_le (sizeof_struct ce0 (co_members co)) _ M1).
  intros M3. lia.
Qed.

Lemma variant_field_offset_in_range_complete: forall ce co id ofs ty,
    co_sv co = TaggedUnion ->
    composite_consistent ce co ->
    variant_field_offset ce id (co_members co) = OK ofs ->
    field_type id (co_members co) = OK ty ->
    4 <= ofs /\ ofs + sizeof ce ty <= co_sizeof co.
Proof.
  intros.
  exploit variant_field_offset_in_range; eauto.
  intros (S1 & S2). 
  split. lia.
  (* to show that sizeof_struct ce co0 <= co_sizeof co0 *)
  erewrite co_consistent_sizeof; eauto.
  erewrite co_consistent_alignof; eauto.
  rewrite H. simpl.
  generalize (sizeof_composite_pos ce0 TaggedUnion (co_members co)). simpl.
  generalize (alignof_composite_pos ce0 (co_members co) TaggedUnion).
  intros M1 M2. simpl in M1.
  generalize (align_le (sizeof_variant ce0 (co_members co)) _ M1).
  intros M3. lia.
Qed.


(** IMPORTANT TODO: what if b is changed? *)
Lemma sem_wt_loc_unchanged_blocks: forall fp m1 m2 b ofs
    (WT: sem_wt_loc ce m1 fp b ofs)
    (UNC: Mem.unchanged_on (fun b1 _ => In b1 (footprint_flat fp) \/ b1 = b) m1 m2),
      sem_wt_loc ce m2 fp b ofs.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv WT.
  - inv WT.
    econstructor. eauto.
    eapply Mem.load_unchanged_on; eauto. intros. simpl. auto.
    inv WT0; econstructor; eauto.
  - inv WT. inv WT0.
    econstructor. eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    econstructor.
    eapply IHfp. eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
  - inv WT. econstructor.
    intros. exploit FWT; eauto.
    intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    eapply H; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H1; auto.
    left. eapply in_flat_map. eauto.
  - inv WT. econstructor.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    eapply IHfp; eauto.
Qed.

(* A more general lemma of sem_wt_loc_unchanged_blocks but it require
wt_footprint premise: may be we can combine them into a single lemma?*)
Lemma sem_wt_loc_unchanged_loc: forall fp m1 m2 b ofs ty
    (WT: sem_wt_loc ce m1 fp b ofs)
    (WTFP: wt_footprint ce ty fp)
    (UNC: Mem.unchanged_on (fun b1 ofs1 => In b1 (footprint_flat fp) \/ (b1 = b /\ ofs <= ofs1 < ofs + sizeof ce ty)) m1 m2),
      sem_wt_loc ce m2 fp b ofs.
Proof.
    induction fp using strong_footprint_ind; intros.
  - inv WT.
  - inv WT. inv WTFP.
    econstructor. eauto.
    eapply Mem.load_unchanged_on; eauto. intros. simpl. right.
    erewrite <- sizeof_by_value; eauto.
    inv WT0; econstructor; eauto.
  - inv WT. inv WTFP. inv WT0.
    econstructor. eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    econstructor.
    eapply IHfp. eauto. eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H; auto. left. destruct H. auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
  - inv WT. inv WTFP. econstructor.
    intros. exploit FWT; eauto.
    intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    exploit WT2; eauto. intros (fty & FTY & FOFS & WTFP1).
    eapply H; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H1; auto.
    left. eapply in_flat_map. eauto.
    destruct H1. subst. right. rewrite CO. split; auto.
    exploit field_offset_in_range_complete; eauto.
    lia.
  - inv WT. inv WTFP.
    exploit variant_field_offset_in_range_complete; eauto. intros R1.
    generalize (sizeof_pos ce fty). intros R2. 
    econstructor.
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros. rewrite CO. right.
    split; auto. lia.
    eapply IHfp; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl.
    intros. rewrite CO. destruct H. auto.
    right. destruct H. subst. split; auto. lia.
Qed.

    
Definition list_interval {A: Type} (l: list A) (lo: Z) (sz: Z) :=
  firstn (Z.to_nat sz) (skipn (Z.to_nat lo) l).

Definition in_range (lo sz hi: Z) : Prop :=
  0 <= lo /\ lo + sz <= hi.


(** May be very difficult  *)
Lemma loadbytes_interval: forall m b ofs sz ofs1 sz1 bytes,
    in_range ofs1 sz1 sz ->
    Mem.loadbytes m b ofs sz = Some bytes ->
    Mem.loadbytes m b (ofs + ofs1) sz1 = Some (list_interval bytes ofs1 sz1).
Admitted.


Lemma sem_wt_loc_unchanged_on_copy: forall fp m1 m2 ty b1 ofs1 b2 ofs2 bytes,
    sem_wt_loc ce m1 fp b1 ofs1 ->
    wt_footprint ce ty fp ->
    (alignof ce ty | ofs1) ->
    (alignof ce ty | ofs2) ->
    Mem.unchanged_on (fun b _ => In b (footprint_flat fp)) m1 m2 ->
    Mem.loadbytes m1 b1 ofs1 (sizeof ce ty) = Some bytes ->
    Mem.loadbytes m2 b2 ofs2 (sizeof ce ty) = Some bytes ->
    sem_wt_loc ce m2 fp b2 ofs2.
Proof.
  induction fp using strong_footprint_ind; intros until bytes; intros SEMWT WT AL1 AL2 UNC LOAD1 LOAD2.
  - inv SEMWT.
  - inv SEMWT. inv WT.
    erewrite <- sizeof_by_value in *; eauto.
    erewrite <- alignof_by_value in *; eauto.
    eapply Mem.loadbytes_load in LOAD1; eauto.
    eapply Mem.loadbytes_load in LOAD2; eauto.
    econstructor; eauto.
    rewrite LOAD in LOAD1. inv LOAD1.
    inv WT0; econstructor; auto.    
  - inv SEMWT. inv WT. inv WT0.
    replace (sizeof ce (Tbox ty0)) with (size_chunk Mptr) in * by auto.
    eapply Mem.loadbytes_load in LOAD1; eauto.
    eapply Mem.loadbytes_load in LOAD2; eauto.
    rewrite LOAD1 in LOAD. inv LOAD.    
    econstructor; eauto.
    rewrite H0. econstructor.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto.    
  - inv SEMWT.
    inv WT. econstructor.
    intros until ffp. intros FIND.
    exploit FWT. eauto. intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    exploit WT2; eauto. intros (fty & C & D & E).
    eapply H; eauto.
    (* align *)
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. simpl. rewrite CO.
    (** TODO: align of composite is dividable by the alignment of each member *)
    admit.
    (** TODO: add (alignof ce fty | fofs) in wt_footprint *)
    admit.
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. simpl. rewrite CO.
    (** TODO: align of composite is dividable by the alignment of each member *)
    admit.
    (** TODO: add (alignof ce fty | fofs) in wt_footprint *)
    admit.
    (* unchanged *)
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. 
    eapply in_flat_map. eauto.
    (* loadbytes *)
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tstruct orgs id)).
    (* in_range *)
    admit.
    eauto.
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tstruct orgs id)).
    (* in_range *)
    admit.
    eauto.
  - inv SEMWT.
    inv WT. simpl in *. rewrite CO in *.
    (** IMPORTANT TODO: the shape of sizeof variant (4 + ...), to get
    the bytes of the tag *)
Admitted.

Lemma load_result_int: forall chunk n sz si,
    Cop.cast_int_int sz si n = n ->
    access_mode (Tint sz si) = Ctypes.By_value chunk ->
    Val.load_result chunk (Vint n) = Vint n.
Proof.
  intros until si; intros H0 H.
  simpl in H.
  destruct sz; destruct si; inv H; simpl;
    try (simpl in H0; rewrite H0; auto).
  auto. auto.
  simpl in H0. destruct (Int.eq n Int.zero).
  subst. simpl. auto.
  subst. simpl. auto.
  simpl in H0. destruct (Int.eq n Int.zero).
  subst. simpl. auto.
  subst. simpl. auto.
Qed.

(* Assigning a semantics well typed value to a location makes this
location semantics well-typed. The difficult part is the align and
composite. *)
Lemma assign_loc_sem_wt: forall fp ty m1 b ofs v m2
    (* We may require that the location is aligned (note that the
    location is calculated from l-value) *)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val ce m1 fp v)
    (WTFP: wt_footprint ce ty fp)
    (* the assignment does not affect the footprint *)
    (IN: ~ In b (footprint_flat fp)),
    sem_wt_loc ce m2 fp b (Ptrofs.unsigned ofs).
Proof.
  (* no need to induciton on fp *)
  destruct fp; intros.
  - inv WT.
  - inv WT.
    + inv AS. 
      inv WTFP. simpl in H. inv H.
      eapply sem_wt_base; eauto.
      simpl. eauto.
      eapply Mem.load_store_same. eauto.
      simpl. econstructor.
    + inv AS.
      inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      erewrite load_result_int; eauto.
      econstructor. auto.
    (* single *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv H. simpl.
      econstructor.
    (* float *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv H. simpl.
      econstructor.      
    (* long *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv H. simpl.
      econstructor.      
  - inv WTFP. inv WT.
    inv AS; simpl in *; try congruence.
    eapply Decidable.not_or in IN. destruct IN as (IN1 & IN2).
    assert (UNC: Mem.unchanged_on (fun b _ => b <> b0) m1 m2).
    { eapply Mem.store_unchanged_on; eauto. }
    inv H.
    econstructor. 
    eapply Mem.load_store_same. eauto.
    exploit sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H.
    intro. apply IN2. subst. auto.
    subst. auto.
    intros WTLOC1.
    replace (Val.load_result Mptr (Vptr b Ptrofs.zero)) with (Vptr b Ptrofs.zero) by auto.
    econstructor; eauto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
  - inv AS. inv WTFP. simpl in *. try congruence.
    inv WT.
    eapply sem_wt_loc_unchanged_on_copy; eauto.
    (** TODO: align: maybe we can add this check in semantics *)
    admit. admit.    
    (* unchanged *)
    eapply Mem.storebytes_unchanged_on; eauto.    
    eapply Mem.loadbytes_length in H4.
    eapply Mem.loadbytes_storebytes_same in H5.
    replace (sizeof ce ty) with (Z.of_nat (length bytes)).
    auto.
    rewrite H4. erewrite Z_to_nat_max.
    generalize (sizeof_pos ce ty). lia.    
  - inv AS. inv WTFP. simpl in *. try congruence.
    inv WT.
    eapply sem_wt_loc_unchanged_on_copy; eauto.
    (** TODO: align: maybe we can add this check in semantics *)
    admit. admit.    
    (* unchanged *)
    eapply Mem.storebytes_unchanged_on; eauto.    
    eapply Mem.loadbytes_length in H4.
    eapply Mem.loadbytes_storebytes_same in H5.
    replace (sizeof ce ty) with (Z.of_nat (length bytes)).
    auto.
    rewrite H4. erewrite Z_to_nat_max.
    generalize (sizeof_pos ce ty). lia.
Admitted.

Lemma sem_wt_subpath: forall phl fp1 b1 ofs1 b2 ofs2 fp2 m,
    sem_wt_loc ce m fp1 b1 ofs1 ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    sem_wt_loc ce m fp2 b2 ofs2.
Proof.
  induction phl; intros.
  - simpl in H0. inv H0. auto.
  - simpl in H0. destruct a.
    + destruct fp1; try congruence.
      inv H. inv WT. eapply IHphl; eauto.
    + destruct fp1; try congruence.
      inv H.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A & B). subst.      
      exploit FWT; eauto. 
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct ident_eq in H0; subst; try congruence.
      destruct list_eq_dec in H0; subst; try congruence.
      destruct ident_eq in H0; subst; try congruence.
      inv H. eauto.
Qed.

Lemma sem_wt_loc_implies_bmatch: forall fp m b ofs,
    sem_wt_loc ce m fp b ofs ->
    bmatch ce m b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv H.
  - inv H. econstructor; eauto.
  - inv H. inv WT.
    econstructor; eauto.
  - inv H0. econstructor.
    intros.
    exploit find_fields_some; eauto. intros (A & B).
    exploit FWT; eauto.
  - inv H. econstructor; eauto.
Qed.

Lemma assign_loc_unchanged_on: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    Mem.unchanged_on (fun b1 ofs1 => ~ (b1 = b /\ Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + sizeof ce ty)) m1 m2.
Proof.
  intros until v. intros AS.
  inv AS.
  - eapply Mem.store_unchanged_on; eauto.
    intros. intro. eapply H2. split; auto.
    erewrite <- sizeof_by_value; eauto.
  - exploit Mem.loadbytes_length. eauto.
    intros LEN.
    eapply Mem.storebytes_unchanged_on; eauto.
    intros. intro. eapply H7. split; auto.
    rewrite LEN in H6.
    erewrite Z_to_nat_max in H6.
    generalize (sizeof_pos ce0 ty). intros.
    erewrite Z.max_l in H6. eauto. lia.
Qed.

    
(* assignment does not change the permission of all the memory location *)
Lemma assign_loc_perm_unchanged: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    (forall b ofs k p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p).
Proof.
  intros until v. intros AS. inv AS.
  - intros. split; intros.
    eapply Mem.perm_store_1; eauto.
    eapply Mem.perm_store_2; eauto.
  - intros. split; intros.
    eapply Mem.perm_storebytes_1; eauto.
    eapply Mem.perm_storebytes_2; eauto.
Qed.

(* It collects the blocks pointed by the box pointer in the footprint. It does not collect *)
Fixpoint blocks_of_fp_box (fp: footprint) : list (block * Z) :=
  match fp with
  | fp_box b sz _ => (b, sz) :: nil
  | fp_struct _ fpl =>
      concat (map (fun '(fid, fofs, ffp) => blocks_of_fp_box ffp) fpl)
  | fp_enum _ _ _ _ _ ffp =>
      blocks_of_fp_box ffp
  | _ => nil
  end.

(* The memory location of the size record in the allocated blocks *)
Definition loc_of_size_record (bs: list block) :=
  fun b ofs => In b bs /\ (- size_chunk Mptr) <= ofs < 0.

Definition loc_of_size_record_fp (fp: footprint) :=
  loc_of_size_record (map fst (blocks_of_fp_box fp)).

(* The permissions of all blocks in bs are unchanged *)
Definition blocks_perm_unchanged (bs: list (block * Z)) (m1 m2: mem) : Prop :=
  forall b sz ofs k p,
    In (b, sz) bs -> 0 <= ofs < sz ->
    (* To avoid prove all blocks in the footprint are valid, we just
    need m1 implies m2 *)
    Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Definition blocks_perm_unchanged_fp (fp: footprint) (m1 m2: mem) : Prop :=
  blocks_perm_unchanged (blocks_of_fp_box fp) m1 m2.


Lemma loc_of_size_record_fp_subfield: forall fp fpl b ofs fid fofs id,
    loc_of_size_record_fp fp b ofs ->
    In (fid, fofs, fp) fpl ->           
    loc_of_size_record_fp (fp_struct id fpl) b ofs.
Proof.
  intros. red. red.
  repeat red in H. destruct H. split; auto.
  eapply in_map_iff in H.
  destruct H as ((b1 & sz) & A & IN). simpl in A. subst.
  eapply in_map_iff.
  exists (b, sz). split. auto.
  simpl. eapply in_concat. exists (blocks_of_fp_box fp).
  split; auto. eapply in_map_iff.
  exists (fid, fofs, fp). eauto.
Qed.

Lemma blocks_perm_unchanged_fp_subfield: forall fp fpl m1 m2 fid fofs id,
    blocks_perm_unchanged_fp (fp_struct id fpl) m1 m2 ->
    In (fid, fofs, fp) fpl ->
    blocks_perm_unchanged_fp fp m1 m2.
Proof.
  intros. red. red. intros.
  do 2 red in H. eapply H; eauto.
  simpl. eapply in_concat. exists (blocks_of_fp_box fp).
  split; auto.
  eapply in_map_iff.
  exists (fid, fofs, fp). eauto.
Qed.

(* The permission of (-size Mptr, sz) (i.e., the size of allocation)
is unchanged if the size record is unchanged_on and the permission of
the block body is also unchanged *)
Lemma size_record_and_perm_unchanged: forall fp m1 m2 b sz,
    Mem.unchanged_on (fun b1 ofs1 => loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    blocks_perm_unchanged_fp fp m1 m2 ->
    In (b, sz) (blocks_of_fp_box fp) ->
    forall k p,
      (** FIXME: if we just prove this direction, we do not need to
      prove that all the blocks in fp are valid blocks (which is used
      in unchanged_on_perm). This proof may require lots of
      effort... *)
      Mem.range_perm m1 b (- size_chunk Mptr) sz k p ->
      Mem.range_perm m2 b (- size_chunk Mptr) sz k p.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 sz1 UNC PERM IN; simpl in *; try contradiction.
  - destruct IN; try contradiction.
    inv H.
    do 2 red in PERM. intros. 
    red. intros.
    (* two cases: ofs < 0 and ofs >= 0 *)
    destruct (Z.lt_decidable ofs 0).      
    + erewrite <- Mem.unchanged_on_perm. eauto. eauto.
      simpl. red. red. simpl. split; eauto.
      lia.
      (** b1 in m1 is valid  *)
      eapply Mem.perm_valid_block. eauto.
    + eapply PERM. simpl. eauto.
      lia. eauto.
  - intros k p RPERM. red. intros ofs RANGE.
    (* (b1, sz1) is in one of the field box *)
    eapply in_concat in IN. destruct IN as (bs & IN1 & IN2).
    eapply in_map_iff in IN1.
    destruct IN1 as (((fid & fofs) & ffp) & A1 & A2). subst.
    (* use I.H. *)
    eapply H. eauto.
    (* unchanged_on *)
    eapply Mem.unchanged_on_implies; eauto. simpl.
    intros. eapply loc_of_size_record_fp_subfield; eauto.
    (* perm unchanged *)
    eapply blocks_perm_unchanged_fp_subfield; eauto.
    eauto. auto. auto.
  - intros k p RPERM. red. intros.
    eapply IHfp.
    eapply Mem.unchanged_on_implies; eauto.
    red in PERM. simpl in PERM. red. eauto.
    eauto. auto. auto.
Qed.

        
(* bmatch remians valid if we only changes the location outside the
block b and the box blocks pointed by the the shallow footprint of
fp *)
Lemma bmatch_unchanged_on_block: forall fp m1 m2 b ofs,
    bmatch ce m1 b ofs fp ->
    (* The memory block [b] and the location of the size record are
    unchanged *)
    Mem.unchanged_on (fun b1 ofs1 => b1 = b \/ loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    (* We require that the permission of the box blocks pointed by the
    shallow part of fp is unchanged *)
    blocks_perm_unchanged_fp fp m1 m2 ->
    bmatch ce m2 b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 ofs1 BM UNC PERM.
  - inv BM.
  - inv BM. econstructor; eauto.
    eapply Mem.load_unchanged_on. eauto. simpl. auto. eauto.
    inv WT; econstructor. auto.
  (* fp_box *)
  - inv BM. econstructor.
    eapply Mem.load_unchanged_on; eauto. simpl. auto.
    (* the size loaded in m2 is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. right. red. simpl. 
    red. split. econstructor; auto. lia.
    (* permission is unchanged *)
    eapply size_record_and_perm_unchanged.
    eapply Mem.unchanged_on_implies; eauto. simpl. eauto.
    auto. simpl. auto. auto.
  - inv BM. econstructor. intros fid fofs ffp FIND.
    exploit FMATCH; eauto. intros BM1.
    exploit find_fields_some; eauto.
    intros (A1 & A2).
    eapply H. eauto. eauto.
    (* unchanged_on *)
    eapply Mem.unchanged_on_implies. eauto.
    simpl. intros. destruct H0; subst; auto.
    right. eapply loc_of_size_record_fp_subfield; eauto.
    (* perm unchanged *)
    eapply blocks_perm_unchanged_fp_subfield; eauto.
  - inv BM. econstructor.
    (* prove the tag is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl. auto.
    (* prove bmatch *)
    eapply IHfp. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    red. red in PERM. eauto.
Qed.


(* A finded grained version of bmatch_unchanged_on. *)
Lemma bmatch_unchanged_on_loc: forall fp m1 m2 b ofs ty,
    bmatch ce m1 b ofs fp ->
    wt_footprint ce ty fp ->
    Mem.unchanged_on (fun b1 ofs1 => (b1 = b /\ (ofs <= ofs1 < ofs + sizeof ce ty)) \/ loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    (* We require that the permission of the box blocks pointed by the
    shallow part of fp is unchanged *)
    blocks_perm_unchanged_fp fp m1 m2 ->
    bmatch ce m2 b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 ofs1 ty1 BM WTFP UNC PERM.
  - inv BM.
  - inv BM. inv WTFP.
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. left. split; auto.
    erewrite <- sizeof_by_value; eauto.
    inv WT; econstructor; eauto.
  (* fp_box *)
  - inv BM. inv WTFP. econstructor.
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. left. split; auto.
    (* the size loaded in m2 is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. right. red. simpl. 
    red. split. econstructor; auto. lia.
    (* permission is unchanged *)
    eapply size_record_and_perm_unchanged.
    eapply Mem.unchanged_on_implies; eauto. simpl. eauto.
    auto. simpl. auto. auto.
  - inv BM. inv WTFP.
    econstructor. intros fid fofs ffp FIND.
    exploit FMATCH; eauto. intros BM1.
    exploit find_fields_some; eauto.    
    intros (A1 & A2).
    exploit WT2; eauto. intros (fty & FTY & FOFS & WTFP1).
    eapply H. eauto. eauto. eauto.
    (* unchanged_on *)
    + eapply Mem.unchanged_on_implies. eauto.
      simpl. intros. destruct H0.
      * destruct H0. subst. left. split; auto. rewrite CO.
        exploit field_offset_in_range_complete; eauto.
        lia.
      * right. eapply loc_of_size_record_fp_subfield; eauto.
    + (* perm unchanged *)
      eapply blocks_perm_unchanged_fp_subfield; eauto.
  - inv BM. inv WTFP.
    exploit variant_field_offset_in_range_complete; eauto. intros RAN.
    econstructor.    
     (* prove the tag is unchanged *)
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros. left. split; auto.
    rewrite CO.
    generalize (sizeof_pos ce fty). lia.
    (* prove bmatch *)
    eapply IHfp. eauto. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H.
    + destruct H. subst. left. split; auto.
      rewrite CO. lia.
    + right.
      red. red in PERM. eauto.
    + eauto.
Qed.

(* The footprint located in the shallow path of the footprint
satisfying bmatch still satisfies bmatch *)
Lemma get_loc_footprint_bmatch: forall phl b1 ofs1 b2 ofs2 fp1 fp2 m
    (BM: bmatch ce m b1 ofs1 fp1)
    (SHA: ~ not_shallow_prefix_paths phl)
    (GFP: get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2)),
    bmatch ce m b2 ofs2 fp2.
Proof.
  induction phl; intros; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + exfalso. eapply SHA. econstructor. auto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence. repeat destruct p.
      inv BM.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit FMATCH; eauto. intros BM1.
      eapply IHphl; eauto.
      intro. eapply SHA. eapply in_cons. eauto.
    + destr_fp_enum fp1 ty.
      inv BM. eapply IHphl; eauto.
      intro. eapply SHA. eapply in_cons. eauto.
Qed.

(* The footprint located in the path of the footprint satisfying
sem_wt_loc still satisfies sem_wt_loc *)
Lemma get_loc_footprint_sem_wt_loc: forall phl b1 ofs1 b2 ofs2 fp1 fp2 m
    (BM: sem_wt_loc ce m fp1 b1 ofs1)
    (GFP: get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2)),
    sem_wt_loc ce m fp2 b2 ofs2.
Proof.
  induction phl; intros; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + destruct fp1; try congruence.
      inv BM. inv WT. eapply IHphl; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence. repeat destruct p.
      inv BM.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit FWT; eauto.
    + destr_fp_enum fp1 ty.
      inv BM. eapply IHphl; eauto.
Qed.

      
(* The box blocks of the footprint of shallow path are subset *)
Lemma get_footprint_shallow_path_incl: forall phl fp1 fp2,
    get_footprint phl fp1 = Some fp2 ->
    ~ not_shallow_prefix_paths phl ->
    incl (blocks_of_fp_box fp2) (blocks_of_fp_box fp1).
Admitted.

Lemma blocks_perm_unchanged_fp_incl: forall fp1 fp2 m1 m2,
    incl (blocks_of_fp_box fp2) (blocks_of_fp_box fp1) ->
    blocks_perm_unchanged_fp fp1 m1 m2 ->
    blocks_perm_unchanged_fp fp2 m1 m2.
Admitted.

(* If we only update the contents of the memory, the permission is
unchanged *)
Lemma blocks_perm_unchanged_normal: forall m1 m2 fp,
    (forall b ofs k p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p) ->
    blocks_perm_unchanged_fp fp m1 m2.
Proof.
  intros. red. red. intros. eapply H. eauto.
Qed.


(* The location computed by get_loc_footprint is not in size
    record (i.e., (-size Mptr, 0) *)
Lemma get_loc_footprint_pos: forall phl fp1 b1 ofs1 b2 ofs2 fp2 ce ty,
    ofs1 >= 0 ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    wt_footprint ce ty fp1 ->
    ofs2 >= 0.
Proof.
Admitted.


Lemma get_loc_footprint_map_pos: forall phl id b ofs fp fpm e ce,
    get_loc_footprint_map e (id, phl) fpm = Some (b, ofs, fp) ->
    wf_env fpm ce e ->
    ofs >= 0.
Admitted.


(* The memory is only changed in (b1, ofs1), the changed location is
sem_wt. The memory is still bmatch *)
Lemma bmatch_set_subpath_wt_val: forall phl fp1 fp2 vfp m1 m2 b ofs b1 ofs1 ty1 vty pfp
    (BM: bmatch ce m1 b ofs fp1)    
    (* It is used to ensure that the changed location is not size
    record. Restrict ofs instead of ofs1 here is because we need to
    strengthen the I.H. More generally, there are some locations in
    the memory should be protected. They must be not modified by the
    semantics. In our setting, these locations are the location of
    size record allocated by malloc *)
    (GT: ofs >= 0)
    (* Move this comment to sem_wt_loc_set_wt_val. Only changes the
    location which is updated with vfp. To use I.H., we need to relax
    this condition to that the memory not in the vfp and not in (b1,
    ofs1) is unchanged instead of just not in (b1, ofs1)*)
    (UNC: Mem.unchanged_on (fun b2 ofs2 => ~ (b2 = b1 /\ (ofs1 <= ofs2 < ofs1 + sizeof ce vty))) m1 m2)
    (* The permission of the box blocks is unchanged *)
    (PERMUNC: blocks_perm_unchanged_fp fp1 m1 m2)
    (* we just need (b1, ofs1) to be bmatch to strengthen the I.H. *)
    (WTLOC: bmatch ce m2 b1 ofs1 vfp)
    (* pfp is useless in this proof *)
    (GFP: get_loc_footprint phl fp1 b ofs = Some (b1, ofs1, pfp))
    (SFP: set_footprint phl vfp fp1 = Some fp2)
    (WTFP1: wt_footprint ce ty1 fp1)
    (* relate ty1 and vty *)
    (WTPATH: wt_path ce ty1 phl vty)
    (* separation of fp *)
    (NOREP: list_norepet (footprint_flat fp1))
    (DIS: ~ In b (footprint_flat fp1)),
    bmatch ce m2 b ofs fp2.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. inv SFP. auto.
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    exploit set_footprint_app_inv. eauto.
    intros (fp3' & vfp' & B1 & B2 & B3).
    (* relate fp3 and fp3' *)
    exploit get_loc_footprint_eq. eapply A1. intros B1'.
    rewrite B1 in B1'. inv B1'.
    (* show that ofs1 >= 0 *)
    assert (GT1: ofs1 >= 0).
    { eapply get_loc_footprint_pos; eauto. }
    destruct ph; simpl in *.
    + destruct fp3; try congruence. inv A2. inv B2.
      (* key proof: phl' ++ [ph_deref] is not shallow path, so if
      bmatch m2 b ofs fp1 then bmatch m2 b ofs fp2
      (bmatch_set_not_shallow_paths) *)
      (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
      exploit get_footprint_incl. eauto. simpl. left; eauto.
      intros IN.
      assert (BNE: b1 <> b).
      { intro. eapply DIS. subst. auto. }
      (* To use bmatch_unchanged_on_block: we also need to prove that
      the size record and the permission of the box blocks are
      unchanged *)
      exploit bmatch_unchanged_on_block. eapply BM.
      eapply Mem.unchanged_on_implies. eauto. intros. simpl.
      destruct H. subst. intro. eapply BNE. intuition.      
      intro. destruct H1. subst. do 2 red in H. lia.
      (* perm unchanged *)
      auto.
      intros BM1.
      (* use bmatch_set_not_shallow_paths *)
      eapply bmatch_set_not_shallow_paths. eauto.
      eapply SFP. eapply in_app. right. econstructor. auto.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv B2. inv A2.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      (* Get the type *)
      eapply wt_path_field_inv in WTPATH as (sid & orgs & co & WTPATH & CO & FTY & STR).
      assert (WTFP:  wt_footprint ce (Tstruct orgs sid) (fp_struct id fpl)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* get the field_offset of i *)
      rewrite CO in CO0. inv CO0.
      exploit WT1. eapply FTY. intros (ffpi & fofsi & E1 & E2 & E3).
      rewrite FIND in E1. inv E1.
      (* show that fofsi >= 0 *)
      exploit field_offset_in_range. eauto. eauto. intros (R1 & R2).      
      (* key proof: discuss phl is shallow path or not. If yes, prove
      bmatch m2 (fp_struct id (set_field i vfp fpl)) and then use
      I.H. *)
      destruct (in_dec path_eq ph_deref phl').
      (* phl' is not shallow path. The proof is mostly the same as in ph_deref *)
      * (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
        exploit (get_loc_footprint_not_shallow_path phl'). auto.
        eapply A1. intros IN.        
        assert (BNE: b1 <> b).
        { intro. eapply DIS. subst. auto. }
        exploit bmatch_unchanged_on_block. eapply BM.
        eapply Mem.unchanged_on_implies. eauto. intros. simpl.
        destruct H. subst. intuition.
        intro. destruct H1. subst.
        do 2 red in H. destruct H. lia.
        auto.
        intros BM1.
        (* use bmatch_set_not_shallow_paths *)
        eapply bmatch_set_not_shallow_paths. eauto.
        eapply SFP. eapply in_app. left. auto.
      (* phl' is shallow path. First prove b1 = b and bmatch m1
      (fp_struct id fpl) (note that this can only be proved if phl' is
      shallow path). Then prove bmatch m2 (fp_struct (set_field i vfp
      fpl)). Finally use I.H. to prove bmatch m2 fp2 *)
      * exploit get_loc_footprint_bmatch. eapply BM. 1-2: eauto.
        intros BM1.
        assert (BM2: bmatch ce m2 b1 ofs2 (fp_struct id (set_field i vfp fpl))).
        { inv BM1. econstructor.
          intros fid fofs ffp FIND1.
          destruct (ident_eq fid i); subst.
          (* fid = i: use WTLOC to prove *)
          - exploit find_fields_same_footprint. eauto. intro. subst.
            (* prove fofs = z *)
            exploit find_fields_same_offset. eauto. intros (vfp1 & F).
            rewrite FIND in F. inv F. auto.
          (* fid <> i *)
          - exploit find_fields_same_offset; eauto.
            intros (vfp1 & FIND2).
            exploit FMATCH. eauto. intros BM3.
            exploit find_fields_set_spec. eauto.
            erewrite FIND1. intros D. inv D.
            destruct peq; try congruence.
            (* use bmatch_unchanged_on and BM3. Show that (ofs2 +
            fofs) has no overlap with the field i *)            
            (* get the type of vfp1 (the type of fid) *)
            exploit WT2. eapply FIND2. intros (fty & FTY1 & FOFS & WTVFP1).
            eapply bmatch_unchanged_on_loc; eauto.
            (* show unchanged_on i.e., (ofs2 + fofs) not in [(ofs2 +
            z), (ofs2 + z + size vty) *)
            eapply Mem.unchanged_on_implies. eauto.
            simpl. intros. destruct H.
            destruct H. subst. intro. destruct H.
            exploit field_offset_no_overlap_simplified.
            5: eauto. 1-4: eauto.
            intros [A|B]. lia. lia.
            (* loc_of_size_record_fp *)
            intro. destruct H1. subst. do 2 red in H. destruct H. lia.
            (* perm unchanged: we need to show that (blocks_of_fp_box
            vfp1) ⊆ (blocks_of_fp_box fp1) because phl is shallow
            prefix path *)
            red.
            exploit find_fields_some. eapply FIND2. intros (F1 & F2).
            eapply blocks_perm_unchanged_fp_subfield; eauto.
            eapply blocks_perm_unchanged_fp_incl; eauto.
            eapply get_footprint_shallow_path_incl.
            eapply get_loc_footprint_eq. eauto. auto. }
        (* prove by I.H. *)
        eapply IHn. eauto. eauto. eapply GT.
        2: eauto.
        2: eapply BM2. all: eauto.
        (* prove (ofs2+z) is in the range of the struct, i.e., [ofs2,
        ofs2+sizeof struct sid) *)
        eapply Mem.unchanged_on_implies; eauto.
        intros. simpl. intro. eapply H. destruct H1.
        split; auto. subst. clear H.
        (* show that z >= 0 *)
        exploit field_offset_in_range_complete; eauto.
        simpl. rewrite CO. lia.
    (* enum case: the proof strategy is similar to struct *)
    + destruct fp3; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      inv A2. inv B2.
      (* key proof: discuss phl is shallow path or not. If yes, prove
      bmatch m2 (fp_struct id (set_field i vfp fpl)) and then use
      I.H. *)
      destruct (in_dec path_eq ph_deref phl').
      (* phl' is not shallow path. The proof is mostly the same as in ph_deref *)
      * (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
        exploit (get_loc_footprint_not_shallow_path phl'). auto.
        eapply A1. intros IN.        
        assert (BNE: b1 <> b).
        { intro. eapply DIS. subst. auto. }
        exploit bmatch_unchanged_on_block. eapply BM.
        eapply Mem.unchanged_on_implies. eauto. intros. simpl.
        destruct H. subst. intuition.
        intro. destruct H1. subst.
        do 2 red in H. destruct H. lia.
        auto.
        intros BM1.
        (* use bmatch_set_not_shallow_paths *)
        eapply bmatch_set_not_shallow_paths. eauto.
        eapply SFP. eapply in_app. left. auto.
      * exploit get_loc_footprint_bmatch. eapply BM. 1-2: eauto.
        intros BM1.
        eapply wt_path_downcast_inv in WTPATH as (id1 & orgs1 & co & EQTY & WTPATH & CO & FTY & ENUM ). symmetry in EQTY. inv EQTY.
        assert (WTFP:  wt_footprint ce (Tvariant orgs id) (fp_enum id orgs tag fid0 ofs0 pfp)).
        { eapply get_wt_footprint_wt; eauto. }
        inv WTFP.
        (* some rewrite *)
        rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
        assert (BM2: bmatch ce m2 b1 ofs2 (fp_enum id orgs tag fid0 ofs0 vfp)).
        { inv BM1. econstructor; eauto.
          (* prove that the location of the tag is unchanged *)
          eapply Mem.load_unchanged_on; eauto.
          simpl. intros. intro. destruct H0.
          exploit variant_field_offset_in_range; eauto. lia. }
        (* prove by I.H. *)
        eapply IHn. eauto. eauto. eauto.
        2: eauto.
        2: eapply BM2. all: eauto.        
        eapply Mem.unchanged_on_implies; eauto.
        intros. simpl. intro. destruct H1. subst. eapply H. 
        split; auto. clear H.                
        exploit variant_field_offset_in_range_complete; eauto.
        simpl. rewrite CO. lia.
Qed.


Lemma get_loc_footprint_in: forall phl fp1 b1 ofs1 b2 ofs2 fp2,
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    In b2 (b1 :: footprint_flat fp1).
Proof.
  induction phl; intros.
  - simpl in H. inv H. econstructor; auto.
  - simpl in H. destruct a.
    + destruct fp1; try congruence.
      exploit IHphl; eauto. intros IN. inv IN.
      eapply in_cons. simpl. auto.
      eapply in_cons. simpl. auto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit IHphl; eauto. intros IN. inv IN.
      econstructor. auto.
      eapply in_cons. simpl. eapply in_flat_map; eauto.
    + destr_fp_enum fp1 ty.
      exploit IHphl; eauto.
Qed.

            
(* The location in (b, ofs) or in the footprint fp *)
Definition loc_in_footprint (b: block) (ofs sz: Z) (fp: footprint) :=
  fun b1 ofs1 =>
    (b1 = b /\ ofs <= ofs1 < ofs + sz) \/
      In b1 (footprint_flat fp).

(* The location out of (P1 and P2) is unchanged and the permission in
P1 is unchanged, if P1 and P2 are disjoint, then the permission in P1
or outside (P1 and P2) is unchanged. Here P1 is "in the range of (b, ofs) to (b, ofs + sz)" and P2 is "in the footprint fp" *)
Lemma perm_unchanged_in_loc: forall b ofs sz m1 m2 fp,
    Mem.unchanged_on (fun b1 ofs1 => ~ loc_in_footprint b ofs sz fp b1 ofs1) m1 m2 ->
    ~ In b (footprint_flat fp) ->
    (forall ofs2 k p,
        ofs <= ofs2 < ofs + sz ->
        Mem.perm m1 b ofs2 k p ->
        Mem.perm m2 b ofs2 k p) ->
    (* permission in b is unchanged *)
    (forall ofs2 k p,
        Mem.perm m1 b ofs2 k p ->
        Mem.perm m2 b ofs2 k p).
Proof.
  intros. 
  destruct (Z.le_decidable ofs ofs2).
  - destruct (Z.lt_decidable ofs2 (ofs + sz)).
    + eapply H1. lia. auto.
    + erewrite <- Mem.unchanged_on_perm; eauto.
      simpl. intro. red in H5.
      destruct H5. lia.
      congruence.
      eapply Mem.perm_valid_block; eauto.
  - erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. intro. red in H4. destruct H4.
    lia. congruence.
    eapply Mem.perm_valid_block; eauto.
Qed.


Lemma loc_in_footprint_subfield: forall b ofs co fty fofs fid ffp b1 ofs1 id fpl ce,
    co_sv co = Struct ->
    composite_consistent ce co ->
    field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    In (fid, fofs, ffp) fpl ->
    loc_in_footprint b (ofs + fofs) (sizeof ce fty) ffp b1 ofs1 ->
    loc_in_footprint b ofs (co_sizeof co) (fp_struct id fpl) b1 ofs1.
Proof.
  intros. red. red in H4.
  destruct H4.
  - destruct H4. subst. left.
    exploit field_offset_in_range_complete; eauto.
    lia.
  - right. simpl. eapply in_flat_map. eauto.
Qed.


(* sem_wt_loc version of bmatch_set_subpath_wt_val. It says that if
the modified location of the memory is sem_wt_loc, then the memory m2
also satisfies sem_wt_loc *)
Lemma set_wt_loc_set_subpath_wt_val: forall phl fp1 fp2 vfp m1 m2 b ofs b1 ofs1 ty1 vty pfp
    (WTLOC1: sem_wt_loc ce m1 fp1 b ofs)
    (* only changes the location which is updated with vfp. We should
    relax this condition to that the blocks in vfp can be "changed"
    when updating m1 to m2 because we do not care about their contents
    in m1 *)
    (UNC: Mem.unchanged_on (fun b2 ofs2 => ~ loc_in_footprint b1 ofs1 (sizeof ce vty) vfp b2 ofs2) m1 m2)
    (* We require that the permission in the range of (b1 ,ofs1) is
    unchanged, otherwise the (b1,ofs1) can be freed and breaks
    sem_wt_loc *)
    (PERMUNC: forall k p ofs2,
        ofs1 <= ofs2 < ofs1 + sizeof ce vty ->
        Mem.perm m1 b1 ofs2 k p ->
        Mem.perm m2 b1 ofs2 k p)
    (WTLOC2: sem_wt_loc ce m2 vfp b1 ofs1)
    (GFP: get_loc_footprint phl fp1 b ofs = Some (b1, ofs1, pfp))
    (SFP: set_footprint phl vfp fp1 = Some fp2)
    (WTFP1: wt_footprint ce ty1 fp1)
    (* relate ty1 and vty *)
    (WTPATH: wt_path ce ty1 phl vty)
    (* separation of fp *)
    (NOREP: list_norepet (footprint_flat fp1))
    (DIS1: ~ In b (footprint_flat fp1))
    (* The footprint to be set is disjoint with fp1 to make sure that
    fp2 is non-cyclic. If we expand vfp, we need to shrink fp1 !!!! So
    we should relax this premise to that we do not consider the blocks
    in pfp ! *)
    (* (DIS2: list_disjoint (b :: (footprint_flat fp1)) (footprint_flat vfp)) *)
    (DIS2: forall x y, In x (footprint_flat fp1) ->
                  ~ In x (footprint_flat pfp) ->
                  In y (footprint_flat vfp) ->
                  x <> y)
    (DIS3: ~ In b1 (footprint_flat vfp))
    (DIS4: ~ In b (footprint_flat vfp)),
    sem_wt_loc ce m2 fp2 b ofs.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. inv SFP. auto.
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    exploit set_footprint_app_inv. eauto.
    intros (fp3' & vfp' & B1 & B2 & B3).
    (* relate fp3 and fp3' *)
    exploit get_loc_footprint_eq. eapply A1. intros B1'.
    rewrite B1 in B1'. inv B1'.
    destruct ph; simpl in *.
    + destruct fp3; try congruence. inv A2. inv B2.
      (* prove that (b2, ofs2) is sem_wt_loc in m1 *)
      exploit sem_wt_subpath. eapply WTLOC1. eauto.
      intros WTLOC3. inv WTLOC3. inv WT.
      (* show that b1 <> b2 *)
      exploit get_loc_footprint_norepet. eauto. eapply A1. eauto.
      intros (N1 & N2). simpl in N2. eapply Decidable.not_or in N2.
      destruct N2 as (N3 & N4). 
      (* get the type vty *)
      eapply wt_path_deref_inv in WTPATH.
      destruct WTPATH as (ty1' & WTPATH & TYDEF).
      eapply type_deref_some in TYDEF. subst.
      (* prove that sz = (sizeof ce vty) *)
      exploit get_wt_footprint_wt. eapply WTPATH. eauto. eauto.
      intros WTFP2. inv WTFP2.
      (* prove that (b2, ofs2) is sem_wt_loc in m2 *)            
      assert (WTLOC3: sem_wt_loc ce m2 (fp_box b1 (sizeof ce vty) vfp) b2 ofs2).
      { econstructor.
        eapply Mem.load_unchanged_on; eauto. simpl. intros.
        unfold loc_in_footprint. intro. destruct H0.
        destruct H0. subst. intuition.
        exploit get_loc_footprint_in. eapply A1. intros IN. inv IN.
        congruence.
        eapply DIS2; eauto.
        (* sem_wt_val *)
        econstructor. eauto.
        (* perm *)
        red. intros.
        eapply perm_unchanged_in_loc. eauto. eauto. eauto. eauto.
        (* load the size record *)
        eapply Mem.load_unchanged_on; eauto.
        simpl. intros. intro. red in H0. destruct H0. lia.
        congruence. }
      eapply IHn. eauto. eapply WTLOC1.
      3: eapply WTLOC3.
      (* unchanged_on *)
      instantiate (1 := (Tbox vty)).
      eapply Mem.unchanged_on_implies. eauto. simpl. intros. intro. eapply H.
      red in H1. destruct H1. destruct H1. subst. right. simpl. auto.
      red. right. simpl. auto.
      (* permission unchanged *)
      intros. erewrite <- Mem.unchanged_on_perm; eauto. 
      simpl. intro. red in H1. destruct H1. destruct H1. subst.
      auto.
      exploit get_loc_footprint_in. eapply A1. intros IN.
      inv IN. congruence.
      eapply DIS2; eauto. 
      eapply Mem.perm_valid_block. eauto.
      all: eauto.
      (* disjointness *)
      simpl. intros. destruct H1. subst.
      intro. apply H0. auto.
      eapply DIS2; eauto.
      (* DIS3 *)
      simpl. intro. destruct H. congruence.
      exploit get_loc_footprint_in. eapply A1. intros IN. inv IN. congruence.
      eapply DIS2; eauto.
      (* DIS4 *)
      simpl. intro. destruct H; auto. subst.
      exploit get_loc_footprint_incl. eapply A1. instantiate (1 := b).
      simpl. auto. intros. congruence.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv B2. inv A2.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      (* Get the type *)
      eapply wt_path_field_inv in WTPATH as (sid & orgs & co & WTPATH & CO & FTY & STR).
      assert (WTFP:  wt_footprint ce (Tstruct orgs sid) (fp_struct id fpl)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* get the field_offset of i *)
      rewrite CO in CO0. inv CO0.
      exploit WT1. eapply FTY. intros (ffpi & fofsi & E1 & E2 & E3).
      rewrite FIND in E1. inv E1.
      exploit find_fields_some. eapply FIND. intros (F1 & F2).
      exploit get_loc_footprint_norepet. eauto. eapply A1. eauto.
      intros (NOREP2 & NIN). simpl in NOREP2.
      assert (WTLOC3: sem_wt_loc ce m2 (fp_struct id (set_field i vfp fpl)) b1 ofs2).
      { econstructor. intros fid fofs ffp FIND1.
        destruct (ident_eq fid i); subst.
        (* fid = i: use WTLOC2 to prove *)
       - exploit find_fields_same_footprint. eauto. intro. subst.
         (* prove fofs = z *)
         exploit find_fields_same_offset. eauto. intros (vfp1 & F).
         rewrite FIND in F. inv F. auto.
       - exploit find_fields_same_offset; eauto.
         intros (vfp1 & FIND2).
         exploit find_fields_set_spec. eauto. erewrite FIND1.
         destruct peq; try congruence. intros. inv H.
         exploit WT2. eapply FIND2. intros (fty & FTY1 & FOFS & WTVFP1).
         exploit get_loc_footprint_sem_wt_loc. eapply WTLOC1. eauto.
         intros WTLOC1'. inv WTLOC1'.
         exploit FWT. eapply FIND2.
         intros WTLOC3.
         eapply sem_wt_loc_unchanged_loc. eauto. eauto.
         (* unchanged_on *)
         eapply Mem.unchanged_on_implies. eauto.
         simpl. intros. destruct H.
         (* block in vfp1 must be not in vfp and (b1, ofs2+fofsi) to (b1, ofs2+fofsi) *)
         + intro. red in H1.           
           exploit find_fields_some. eapply FIND2. intros (IN1 & IN2).
           destruct H1.
           * destruct H1. subst.             
             apply NIN. simpl.             
             eapply in_flat_map. exists (fid, fofs, vfp1). split; auto.
           (* The footprint of two different subfields are disjoint *)
           * destruct (in_dec eq_block b0 (footprint_flat ffpi)).
             (* To use DIS2, we need to discuss b0 is in ffpi or not *)
             -- exploit find_fields_some. eapply FIND. intros (IN3 & IN4).
                eapply footprint_norepet_fields_disjoint. eauto.
                eapply IN2. eapply IN4. auto. eauto. eauto. auto.
             -- exploit get_loc_footprint_incl. eapply A1.
                (* show that b0 in fp1 *)
                instantiate (1 := b0). simpl.
                eapply in_flat_map. exists (fid, fofs, vfp1). split; auto.
                intros IN5.
                eapply DIS2; eauto.
         + destruct H. subst.
           intro. red in H. destruct H.
           * destruct H.
             (* prove by the disjointness of two different fields in the struct *)
             exploit field_offset_no_overlap_simplified.
             eapply E2. eauto.
             eapply FOFS. eauto. auto. lia.
           * congruence. }
      (* prove by I.H. *)
      eapply IHn. eauto. eauto.
      3: eapply WTLOC3.
      instantiate (1 := Tstruct orgs id).
      (* unchanged on *)
      eapply Mem.unchanged_on_implies; eauto. simpl. rewrite CO.
      intros. intro. eapply H. clear H.
      eapply loc_in_footprint_subfield; eauto.      
      eapply in_map_iff. exists (i, fofsi, ffpi). destruct ident_eq; try congruence; auto.
      (* permission unchanged *)
      intros. eapply perm_unchanged_in_loc; eauto.
      all: eauto.
      (* DIS2: discuss y in vfp or not *)
      intros. destruct (in_dec eq_block y (footprint_flat vfp)).
      eapply DIS2; eauto. intro. eapply H0.
      simpl. eapply in_flat_map. exists (i, fofsi, ffpi). eauto.
      assert (IN1: In y (footprint_flat (fp_struct id fpl))).
      { simpl. simpl in H1. eapply in_flat_map in H1.
        destruct H1 as (((fid & fofs) & ffp) & IN2 & IN3).
        eapply in_map_iff in IN2. destruct IN2 as (((fid1 & fofs1) & ffp1) & IN4 & IN5).
        destruct ident_eq in IN4. inv IN4. contradiction.
        inv IN4. eapply in_flat_map. exists (fid, fofs, ffp). eauto. }
      intro. subst. contradiction.
      (* DIS3 *)
      intro. simpl in H. eapply in_flat_map in H.
      destruct H as (((fid & fofs) & ffp) & IN2 & IN3).
      eapply in_map_iff in IN2. destruct IN2 as (((fid1 & fofs1) & ffp1) & IN4 & IN5).
      destruct ident_eq in IN4. inv IN4. contradiction.
      inv IN4. eapply NIN. simpl. eapply in_flat_map. eauto.
      (* DIS4 *)
      intro. simpl in H. eapply in_flat_map in H.
      destruct H as (((fid & fofs) & ffp) & IN2 & IN3).
      eapply in_map_iff in IN2. destruct IN2 as (((fid1 & fofs1) & ffp1) & IN4 & IN5).
      destruct ident_eq in IN4. inv IN4. contradiction.
      inv IN4. eapply DIS1.
      eapply get_loc_footprint_incl. eauto. simpl.
      eapply in_flat_map. eauto.
    + destr_fp_enum fp3 ty. 
      inv A2. inv B2.
      exploit get_loc_footprint_sem_wt_loc. eapply WTLOC1. eapply A1.
      intros WTLOC1'. inv WTLOC1'.
      eapply wt_path_downcast_inv in WTPATH as (id1 & orgs1 & co & EQTY & WTPATH & CO & FTY & ENUM ). symmetry in EQTY. inv EQTY.
      assert (WTFP:  wt_footprint ce (Tvariant orgs id) (fp_enum id orgs tag fid0 ofs0 pfp)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* some rewrite *)
      rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
      assert (WTLOC3: sem_wt_loc ce m2 (fp_enum id orgs tag fid0 ofs0 vfp) b1 ofs2).
      { econstructor.
        (* load tag *)
        eapply Mem.load_unchanged_on. eauto.
        simpl. intros. intro. red in H0.
        destruct H0. destruct H0.
        exploit variant_field_offset_in_range_complete; eauto. lia.
        congruence.
        auto. auto. }
      eapply IHn. eauto. eauto.
      3: eapply WTLOC3.
      instantiate (1 := Tvariant orgs id).
      (* unchanged on *)
      simpl. rewrite CO. eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. intro. eapply H.
      red. red in H1. simpl. destruct H1; auto.
      left. destruct H1. subst. split; auto.
      exploit variant_field_offset_in_range_complete; eauto. lia.
      (* perm unchanged *)
      intros. eapply perm_unchanged_in_loc; eauto.
      all: eauto.
Qed.

      
Lemma get_loc_footprint_map_different_local: forall id1 id2 phl1 phl2 fpm e b1 b2 ofs1 ofs2 fp1 fp2,
    list_norepet (flat_fp_map fpm) ->
    id1 <> id2 ->
    get_loc_footprint_map e (id1, phl1) fpm = Some (b1, ofs1, fp1) ->
    get_loc_footprint_map e (id2, phl2) fpm = Some (b2, ofs2, fp2) ->
    b1 <> b2 /\ ~ In b1 (footprint_flat fp2) /\ ~ In b2 (footprint_flat fp1).
Admitted.


(* Two memory location (b1, ofs1) and (b2, ofs2) which have type ty1
and ty2 are non-overlap *)
Definition loc_disjoint (b1 b2: block) (ty1 ty2: type) (ofs1 ofs2: Z) : Prop :=
  b1 <> b2 \/ ofs2 + sizeof ce ty2 <= ofs1 \/ ofs1 + sizeof ce ty1 <= ofs2.

(** This lemma is wrong: considet fp is fp_emp !!! *)
(* Lemma wt_footprint_same_size: forall fp ty1 ty2, *)
(*     wt_footprint ce ty1 fp -> *)
(*     wt_footprint ce ty2 fp -> *)
(*     sizeof ce ty1 = sizeof ce ty2. *)
(* Proof. *)
(*   induction fp using strong_footprint_ind; intros; simpl in *. *)
(*   - inv H. inv H0.  *)
(* Admitted. *)

(** The memory location obtained from get_loc_footprint is either in
    the range of [(b, ofs), (b, ofs+ sizeof ty)] or in the footprint
    fp. Maybe this lemma require norepet of fp? Because
    get_loc_footprint_disjoint_loc need this. *)
Lemma get_loc_footprint_in_range: forall phl fp b ofs b1 ofs1 fp1 ty ty1,
    wt_footprint ce ty fp ->
    wt_path ce ty phl ty1 ->
    ~ In b (footprint_flat fp) ->
    (* no cycle in the footprint *)
    list_norepet (footprint_flat fp) ->
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    (b = b1 /\ ofs <= ofs1 /\ ofs1 + sizeof ce ty1 <= ofs + sizeof ce ty)
    \/ (b <> b1 /\ In b1 (footprint_flat fp)).
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros until ty1; intros WTFP WTPH NIN NOREP GFP; simpl in *.  
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. eapply wt_path_nil_inv in WTPH. subst. left.
    split; auto. lia.    
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst. 
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    simpl in A2.
    destruct ph.
    + destruct fp3; try congruence.
      eapply wt_path_deref_inv in WTPH as (ty' & WTPH & TYDEF).
      eapply type_deref_some in TYDEF. subst.
      inv A2.
      exploit get_loc_footprint_norepet; eauto.
      simpl. intros (C1 & C2). eapply Decidable.not_or in C2. destruct C2 as (C2 & C3).
      exploit IHn. eauto. eapply WTFP. eauto. eauto. eauto. eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        right. split; auto.
        eapply get_loc_footprint_incl; eauto. simpl. auto.
      * destruct B2. right. split.
        intro. subst. eapply NIN. eapply get_loc_footprint_incl. eapply A1. 
        simpl. auto.
        eapply get_loc_footprint_incl. eapply A1. simpl. auto.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      inv A2. eapply wt_path_field_inv in WTPH as (id1 & orgs & co & WTPH & CO & FTY & STRUCT).
      exploit find_fields_some; eauto. intros (C1 & C2). subst.
      exploit get_loc_footprint_norepet. eauto. eapply A1. auto.
      intros (N1 & N2).
      exploit get_wt_footprint_wt. eauto. eapply WTFP. eapply get_loc_footprint_eq. eauto.
      intros WTFP1. inv WTFP1.
      exploit WT2; eauto. intros (fty & FTY1 & FOFS & WTFP2). 
      rewrite CO in CO0. inv CO0.
      rewrite FTY in FTY1. inv FTY1.
      exploit IHn. eauto. eapply WTFP. all: eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        left. split; auto.
        simpl in H0. rewrite CO in H0.
        exploit field_offset_in_range_complete; eauto. lia.
      * destruct B2. right. split; auto.
    + destr_fp_enum fp3 ty0.
      inv A2.
      eapply wt_path_downcast_inv in WTPH as (id1 & orgs1 & co & TY & WTPH & CO & FTY & ENUM).
      inv TY.
      exploit get_loc_footprint_norepet. eauto. eapply A1. auto.
      intros (N1 & N2).      
      exploit get_wt_footprint_wt. eauto. eapply WTFP. eapply get_loc_footprint_eq. eauto.
      intros WTFP1. inv WTFP1.
      rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
      exploit IHn. eauto. eapply WTFP. all: eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        left. split; auto.
        simpl in H0. rewrite CO in H0.
        exploit variant_field_offset_in_range_complete; eauto. lia.
      * destruct B2. right. split; auto.
Qed.

(** IMPORTANT TODO: This lemma says that the (memory locations,
   footprint) obtained from different location are different, no
   matter what paths it resides in. *)
Lemma get_loc_footprint_disjoint_loc: forall phl1 phl2 b1 b2 ty1 ty2 ofs1 ofs2 b1' b2' ofs1' ofs2' ty1' ty2' fp1 fp2 fp1' fp2',
    loc_disjoint b1 b2 ty1 ty2 ofs1 ofs2 ->
    (* What relation between ty1 and ty1'?? We can prove sizeof
          ty1 = sizeof ty1'*)
    wt_footprint ce ty1 fp1 ->
    wt_footprint ce ty2 fp2 ->
    wt_path ce ty1 phl1 ty1' ->
    wt_path ce ty2 phl2 ty2' ->
    get_loc_footprint phl1 fp1 b1 ofs1 = Some (b1', ofs1', fp1') ->
    get_loc_footprint phl2 fp2 b2 ofs2 = Some (b2', ofs2', fp2') ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (footprint_flat fp1) ->
    list_norepet (footprint_flat fp2) ->
    ~ In b1 (footprint_flat fp1) ->
    ~ In b2 (footprint_flat fp2) ->
    ~ In b1 (footprint_flat fp2) ->
    ~ In b2 (footprint_flat fp1) ->
    loc_disjoint b1' b2' ty1' ty2' ofs1' ofs2'
    /\ ~ In b1' (footprint_flat fp2')
    /\ ~ In b2' (footprint_flat fp1')
    /\ list_disjoint (footprint_flat fp1') (footprint_flat fp2').
Proof.
  induction phl1; intros until fp2'; intros DIS1 WT1 WT2 WTPH1 WTPH2 G1 G2 DIS2 NOREP1 NOREP2 IN1 IN2 IN3 IN4.
  - simpl in G1. inv G1.
    exploit get_loc_footprint_in_range. eapply WT2. eapply WTPH2. 
    3: eapply G2. eauto. eauto.
    intros [[A1 [A2 A3]]|[A1 A2]].
    + subst. repeat apply conj.
      * destruct DIS1; red; auto.
        right. 
        generalize sizeof_pos. intros.
        destruct H. lia.
        eapply wt_path_nil_inv in WTPH1. subst. lia.
      * intro. apply IN3.
        eapply get_loc_footprint_incl; eauto.
      * auto.  
      * red. intros. intro.
        eapply DIS2. eauto. eapply get_loc_footprint_incl; eauto.
        auto.
    + repeat apply conj.
      * red. left.
        intro. subst. congruence.
      * intro. apply IN3.
        eapply get_loc_footprint_incl; eauto.
      * intro. eapply DIS2; eauto.
      * red. intros. intro.
        eapply DIS2. eauto. eapply get_loc_footprint_incl; eauto.
        auto.
  - replace (a::phl1) with ((a::nil) ++ phl1) in G1 by auto.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b3 & ofs3 & fp3 & B1 & B2).
    (* show fp3 is well-typed *)
    exploit get_wt_footprint_exists_wt. eapply WT1.
    eapply B1. intros (ty3 & C1 & C2).
    (* show (b3, ofs3) has no overlap with (b2,ofs2) *)
    assert (DIS3: loc_disjoint b3 b2 ty3 ty2 ofs3 ofs2).
    { exploit get_loc_footprint_in_range. eapply WT1. eapply C2.
      3: eapply B1. eauto.
      eauto. intros [[A1 [A2 A3]]|[A1 A2]].
      - subst. 
        destruct DIS1; red; auto.
        right. 
        generalize sizeof_pos. intros.
        destruct H. lia. lia.
      - red. left.
        intro. subst. congruence. }
    exploit get_loc_footprint_norepet. 2: eapply B1. eauto. eauto.
    intros (D1 & D2).
    eapply IHphl1.
    eapply DIS3. 1-6: eauto.
    eapply wt_path_app. eauto. simpl. auto.
    (* disjointness between fp3 and fp2 *)
    red. intros. intro. eapply DIS2.
    eapply get_loc_footprint_incl; eauto. eauto. auto.
    eauto. eauto.
    (* four notin *)
    eauto. eauto.
    (* prove b3 is not in fp2 *)
    exploit get_loc_footprint_in_range. eapply WT1. eapply C2. 
    eapply IN1. eauto. eauto.
    intros [[A1 [A2 A3]]|[A1 A2]].
    subst. eauto.
    intro. eapply DIS2. eauto. eauto. auto.
    (* b2 is not in fp3 *)
    intro. eapply IN4. eapply get_loc_footprint_incl. eauto.
    auto.
Qed.



(* Some properties of wt_footprint. This lemma says that the
(location, footprint) pairs obtained form disjoint paths are disjoint,
i.e., the locations are disjoint and the footprints have no equal
blocks. To express the disjointness of locaitons, we also need the
type of the footprint to get its size, so we add wt_footprint premises
in this lemma. This lemma is hard to refactor because we do induction
on phl instead of its length. *)
Lemma get_loc_footprint_disjoint_paths: forall phl1 phl2 fp b ofs b1 b2 ofs1 ofs2 fp1 fp2 ty ty1 ty2,
    paths_disjoint phl1 phl2 ->
    list_norepet (footprint_flat fp) ->
    wt_footprint ce ty fp ->
    wt_path ce ty phl1 ty1 ->
    wt_path ce ty phl2 ty2 ->
    get_loc_footprint phl1 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint phl2 fp b ofs = Some (b2, ofs2, fp2) ->
    (~ In b (footprint_flat fp)) ->
    (* footprint locations are disjoint *)
    loc_disjoint b1 b2 ty1 ty2 ofs1 ofs2
    (* location and footprint are disjoint *)
    /\ (~ In b1 (footprint_flat fp2))
    /\ (~ In b2 (footprint_flat fp1))
    (* b1 may be equal to b2 so we cannot say b1::fp1 is disjoint with b2::fp2 *)
    /\ list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  induction phl1; intros until ty2.
  - intros. inv H.
  - intros DIS NOREP WT WTPH1 WTPH2 G1 G2 IN.
    inv DIS.
    + replace (a::phl1) with ((a::nil) ++ phl1) in WTPH1; auto.
      replace (p2::l2) with ((p2::nil) ++ l2) in WTPH2; auto.
      exploit wt_path_app_inv. eapply WTPH1.
      intros (ty1' & WTPH1' & WTPH1'').
      exploit wt_path_app_inv. eapply WTPH2.
      intros (ty2' & WTPH2' & WTPH2'').
      simpl in G1, G2.
      destruct a; destruct p2; destruct fp; simpl in *; try congruence.
      (* Case1: disjoint struct fields *)
      * destruct (find_fields fid fpl) eqn: FIND1; try congruence. repeat destruct p.
        destruct (find_fields fid0 fpl) eqn: FIND2; try congruence. repeat destruct p.
        exploit find_fields_some; eauto. intros (A1 & A2). subst.
        exploit find_fields_some. eapply FIND1. intros (A3 & A4). subst.
        (* get the subfield types and offsets *)
        inv WT.
        exploit WT2. eapply FIND1. intros (fty1 & FTY1 & FOFS1 & WST1).
        exploit WT2. eapply FIND2. intros (fty2 & FTY2 & FOFS2 & WST2).
        (* tediously get ty1' and ty2' *)
        erewrite <- (app_nil_l [ph_field i]) in WTPH1'.
        eapply wt_path_field_inv in WTPH1' as (id1' & orgs1' & co1' & WTPH1' & CO1' & FTY1' & STR1').
        eapply wt_path_nil_inv in WTPH1'. inv WTPH1'. rewrite CO1' in CO. inv CO.
        rewrite FTY1' in FTY1. inv FTY1.
        erewrite <- (app_nil_l [ph_field i0]) in WTPH2'.
        eapply wt_path_field_inv in WTPH2' as (id2' & orgs2' & co2' & WTPH2' & CO2' & FTY2' & STR2').
        eapply wt_path_nil_inv in WTPH2'. inv WTPH2'. rewrite CO2' in CO1'. inv CO1'.
        rewrite FTY2' in FTY2. inv FTY2.
        (* end of getting ty1' and ty2' *)
        (* field offset no overlap to get loc_disjoint *)
        exploit field_offset_no_overlap_simplified.
        eapply FOFS1. eauto. eapply FOFS2. eauto.
        congruence.
        intros FOFS_DIS.
        assert (LOC_DIS: loc_disjoint b b fty1 fty2 (ofs + z) (ofs + z0)).
        { red. right. lia. }
        (* use get_loc_footprint_disjoint_loc *)        
        exploit get_loc_footprint_disjoint_loc. eapply LOC_DIS. eauto. eauto.
        all: eauto.
        (* prove f and f0 are disjoint using fpl norepet *)
        eapply footprint_norepet_fields_disjoint; eauto.
        congruence.
        (* norepet *)
        (* easy because f and f0 are in fpl and fpl is norepet *)
        eapply footprint_norepet_fields_norepet; eauto.
        eapply footprint_norepet_fields_norepet; eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
      * destruct ty0; try congruence.
        destruct ty3; try congruence.
        repeat destruct ident_eq in *; try congruence;
        repeat destruct list_eq_dec; try congruence. 
    + replace (a::phl1) with ((a::nil)++phl1) in * by auto.
      replace (a::l2) with ((a::nil)++l2) in * by auto.
      exploit wt_path_app_inv. eapply WTPH1.
      intros (ty1' & WTPH1' & WTPH1'').
      exploit wt_path_app_inv. eapply WTPH2.
      intros (ty2' & WTPH2' & WTPH2'').
      exploit get_loc_footprint_app_inv. eapply G1.
      intros (b3 & ofs3 & fp3 & C1 & C2).
      exploit get_loc_footprint_app_inv. eapply G2.
      intros (b4 & ofs4 & fp4 & C3 & C4).
      rewrite C1 in C3. inv C3.
      assert (WTFP4: wt_footprint ce ty1' fp4).
      { exploit get_wt_footprint_wt. eapply WTPH1'. eapply WT.
        eapply get_loc_footprint_eq; eauto.
        eauto. }
      exploit wt_path_det. eapply WTPH1'. eauto. intros. subst.
      (* use I.H. *)
      exploit get_loc_footprint_norepet. eapply NOREP. eauto. eauto.
      intros (D1 & D2).            
      exploit IHphl1; eauto.      
Qed.
      

Lemma init_place_full_unchanged: forall own p p1,
    is_full (own_universe own) p = is_full (own_universe (init_place own p1)) p.
Admitted.

(* The block obtained from get_loc_footprint_map comes from
   stack or the footprint map *)
Lemma get_loc_footprint_map_in_range: forall phl id fpm le b ofs fp,
    get_loc_footprint_map le (id, phl) fpm = Some (b, ofs, fp) ->
    In b (footprint_of_env le ++ flat_fp_map fpm).
Admitted.

Lemma list_disjoint_app_r {A: Type}: forall (l1 l2 l3: list A),
    list_disjoint l1 (l2 ++ l3) ->
    list_disjoint l1 l2 /\ list_disjoint l1 l3.
Proof.
  intros. red in H. split.
  red. intros. eapply H; auto. eapply in_app; eauto.
  red. intros. eapply H; auto. eapply in_app; eauto.
Qed.

Lemma list_disjoint_app_l {A: Type}: forall (l1 l2 l3: list A),
    list_disjoint (l1 ++ l2) l3 ->
    list_disjoint l1 l3 /\ list_disjoint l2 l3.
Proof.
  intros. eapply list_disjoint_sym in H.
  eapply list_disjoint_app_r in H. destruct H.
  split; apply list_disjoint_sym; auto.
Qed.
  
(** Important Lemma: we need to say that the footprint inside a struct
is also disjoint !!! *)
(* Consider assign to a variant? *)
Lemma assign_loc_sound: forall fpm1 m1 m2 own1 own2 b ofs v p vfp pfp e ty
    (MM: mmatch fpm1 ce m1 e own1)
    (TY: ty = typeof_place p)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val ce m1 vfp v)
    (WFENV: wf_env fpm1 ce e)
    (WTFP: wt_footprint ce ty vfp)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm1 = Some (b, (Ptrofs.unsigned ofs), pfp))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (NOREP: list_norepet (footprint_of_env e ++ (flat_fp_map fpm1)))
    (* vfp and fpm1 are disjoint so that their combination is separated *)
    (DIS1: list_disjoint (footprint_flat vfp) (footprint_of_env e ++ (flat_fp_map fpm1)))
    (WFOWN: wf_own_env own1),
  exists fpm2, set_footprint_map (path_of_place p) vfp fpm1 = Some fpm2
          /\ mmatch fpm2 ce m2 e own2
          /\ list_norepet (footprint_of_env e ++ (flat_fp_map fpm2))
          /\ wf_env fpm2 ce e.
Proof.
  intros. destruct (path_of_place p) eqn: POP.
  exploit get_set_footprint_map_exists; eauto.
  instantiate (1 := vfp).
  intros (fpm2 & A & B). exists fpm2. split. auto.
  eapply list_norepet_app in NOREP.
  destruct NOREP as (NOREP1 & NOREP1' & DIS2).
  eapply list_disjoint_app_r in DIS1. destruct DIS1 as (DIS3 & DIS4).  
  assert (NOREP2: list_norepet (flat_fp_map fpm2)).
  { eapply set_disjoint_footprint_norepet. eauto. eauto.
    eapply list_disjoint_sym. auto. }
  assert (DIS5: list_disjoint (footprint_of_env e) (flat_fp_map fpm2)).
  { red. intros.
    eapply set_footprint_map_incl in H0; eauto. destruct H0; eauto.
    intro. subst. eapply DIS3; eauto. }
  assert (NOREP3: list_norepet ((footprint_of_env e) ++ (flat_fp_map fpm2))).
  { eapply list_norepet_app; eauto. }
  (* set wt_footprint remains wf_env *)
  assert (WFENV2: wf_env fpm2 ce e).
  {  (**  how to show that set a wt footprint remains wt: use the fact
  that p is well-typed?? *)
    eapply wf_env_set_wt_footprint. eauto. erewrite <- TY.
    eauto. auto. rewrite POP. auto. }
  (* show that (b, ofs) does not locate in size record *)
  assert (NSZREC: forall b1 ofs1 fp1, loc_of_size_record_fp fp1 b1 ofs1 ->
                                 ~ (b1 = b /\ Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + sizeof ce ty)).
  { intros. intro. destruct H0. subst.
    do 2 red in H. destruct H.
    generalize (Ptrofs.unsigned_range ofs). lia. }
  repeat apply conj; auto.
  (* mmatch *)
  - red. intros until fp.
    intros GFP INIT.
    unfold own_transfer_assign in CKAS.
    destruct (is_prefix p p0) eqn: PRE.
    (**  Case 1: p0 is children of p1: we need to prove that the
    value/location of p0 is sem_wt *)
    + exploit is_prefix_paths_app; eauto.
      rewrite POP. simpl.
      destruct (path_of_place p0) eqn: POP0. simpl.
      intros (P1 & (phl & P2)). subst.
      (* show that fp is subpath of vfp and (b0, ofs0) is sem_wt_loc
      which requires that (b1,ofs) is sem_wt_loc. *)
      exploit get_loc_footprint_map_app_inv; eauto.
      intros (b1 & ofs1 & fp1 & D & E). rewrite B in D. inv D.
      (* prove that assign_loc assigns a sem_wt_val then the location
      is sem_wt_loc *)
      exploit assign_loc_sem_wt; eauto. 
      (** b1 is not in fp1. Use B to show that location and its
      footprint are disjoint *)
      exploit get_loc_footprint_map_norepet. eapply NOREP2. eapply B. eauto. eauto.
      intuition.      
      intros WTLOC.
      exploit sem_wt_subpath; eauto.
      intros WTLOC1.
      (* sem_wt_loc implies bmatch *)
      exploit sem_wt_loc_implies_bmatch; eauto.
    (** Case 2: p0 is not children of p1 *)
    + assert (INIT1: is_init own1 p0 = true).
      { subst. destruct (is_init own1 p0) eqn: I; auto.
        exploit init_irrelavent_place_still_not_owned; eauto. }                
      destruct (is_prefix p0 p) eqn: PRE1.
      (* p0 is prefix of p. It is possible that p0 is a shallow prefix
      of p !!! It is the situation where overriding a field of an
      initialized struct ! *)
      * exploit is_prefix_paths_app; eauto.
        destruct (path_of_place p0) eqn: POP2.
        rewrite POP. simpl. intros (? & (phl & P1)). subst.
        exploit get_loc_footprint_map_app_inv. eapply PFP.
        intros (b2 & ofs2 & fp3 & A1 & A2). 
        exploit get_set_footprint_map_app_inv. eapply A1. eauto.
        intros (fp4 & G1 & G2).
        rewrite GFP in G1. inv G1.
        exploit MM. erewrite POP2. eauto. eauto.
        intros (BM1 & FULL1).
        exploit wt_place_prefix. eauto. eauto. intros WTP0.        
        assert (WTPH: wt_path ce (typeof_place p0) phl (typeof_place p)).
        { exploit wt_place_wt_local. eapply WTP.
          intros (b1 & ty1 & ETY). rewrite local_of_paths_of_place in ETY.
          rewrite POP in ETY. simpl in ETY.          
          eapply wt_path_app.          
          eapply wt_place_wt_path; eauto.
          eapply wt_place_wt_path; eauto. }
        exploit get_loc_footprint_map_norepet. eapply NOREP1'. eapply A1. eauto.
        intros (N1 & NOTIN).
        split.
        (** task1: prove bmatch m2 b2 ofs2 fp4 using bmatch_set_subpath_wt_val *)
        eapply bmatch_set_subpath_wt_val. eauto.
        eapply get_loc_footprint_map_pos; eauto.        
        eapply assign_loc_unchanged_on. eauto.
        (* blocks_perm_unchanged_fp: the assignment does not change
        permission of memory *)
        eapply blocks_perm_unchanged_normal.
        eapply assign_loc_perm_unchanged; eauto.
        eapply sem_wt_loc_implies_bmatch. eapply assign_loc_sem_wt. eauto. eauto.
        auto.
        (* prove b not in vfp *)
        exploit get_loc_footprint_map_in_range. eapply PFP.
        intros IN. eapply in_app in IN. destruct IN.
        intro. eapply DIS3; eauto.
        intro. eapply DIS4; eauto.
        eapply A2. eauto.
        (* wt_footprint *)
        instantiate (1 := typeof_place p0).
        eapply get_wt_place_footprint_wt. eapply WFENV.
        eapply wt_place_prefix; eauto.
        rewrite POP2. eauto.
        (* wt_path *)
        eauto.
        (* list_norepet *)
        auto. auto.
        (** Task2: prove sem_wt_loc of (b2,ofs2) *)
        (* full -> sem_wt_loc *)
        intros FULL2.
        exploit assign_loc_sem_wt; eauto.
        (* b is not in vfp *)
        exploit get_loc_footprint_map_norepet. eapply NOREP2. eapply B. eauto.
        intuition.
        intros WTLOC.
        assert (FULL3: is_full (own_universe own1) p0 = true).
        { erewrite init_place_full_unchanged. eauto. }
        exploit FULL1. auto.
        intros WTLOC1.
        eapply set_wt_loc_set_subpath_wt_val; eauto.
        (* unchanged_on *)
        eapply Mem.unchanged_on_implies.
        eapply assign_loc_unchanged_on. eauto. simpl. intros.
        intro. eapply H. destruct H1. subst. red. left; auto.
        (* perm unchanged *) 
        intros. erewrite <- assign_loc_perm_unchanged; eauto.
        (* wt_footprint *)
        eapply get_wt_place_footprint_wt. eapply WFENV.
        eapply wt_place_prefix; eauto.
        rewrite POP2. eauto.
        (* disjointness of fp3 and vfp *)
        intros. eapply list_disjoint_sym in DIS4.
        eapply DIS4; auto.
        eapply get_loc_footprint_map_incl; eauto.
        (* b not in vfp *)
        exploit get_loc_footprint_map_norepet. eapply NOREP2.
        eapply B. auto. intuition.
        (* b2 not in vfp: proved by DIS3 and DIS4 *)
        exploit get_loc_footprint_map_in_range. eapply A1. intros IN.
        eapply in_app in IN. destruct IN.
        intro. eapply DIS3; eauto.
        intro. eapply DIS4; eauto.
      (** Case 3: p0 is not a prefix of p, so p0 and p are disjoint place *)
      * exploit is_not_prefix_disjoint; eauto.
        destruct (path_of_place p0) eqn: POP2. rewrite POP. simpl.
        destruct (ident_eq i0 i); subst.
        intros [P1|P2]; try congruence.
        (** DIFFICULT: two locals are equal but their paths are disjoint *)
        --   (** How to know p0 is well-typed or not? *)
          exploit assign_loc_unchanged_on; eauto. intros UNC.
          erewrite <- get_set_disjoint_paths in GFP; eauto.
          (* bmatch m1 b0 ofs0 fp *)
          exploit MM. erewrite POP2. eauto. auto.
          intros (BM0 & FULL0).
          (* pfp is well-typed *)
          exploit get_wt_place_footprint_wt. eapply WFENV. eauto.
          erewrite POP. eauto. intros WTPFP.
          (** prove that (b, ofs) and (b0, ofs0) are disjoint *)
          unfold get_loc_footprint_map in PFP, GFP.
          destruct (e!i) eqn: E1; try congruence. destruct p1.
          destruct (fpm1 ! i) eqn: E2; try congruence.
          (* prove fp is wt_footprint *)
          exploit wf_env_footprint. eapply WFENV. eauto. intros (fp1 & E3 & E4).
          rewrite E2 in E3. inv E3.          
          exploit get_wt_footprint_exists_wt.
          eauto. eauto.
          intros (ty1 & E5 & E6).
          exploit get_loc_footprint_disjoint_paths. eapply paths_disjoint_sym; eauto. 
          instantiate (1 := fp1). eapply norepet_flat_fp_map_element; eauto.
          4: eapply PFP. 4: eapply GFP.
          eauto. eapply wt_place_wt_path; eauto. eauto.
          3: { eapply paths_disjoint_sym. auto. }
          (* b1 is not in fp1 *)
          intro. eapply DIS2. eapply in_footprint_of_env; eauto.
          eapply in_footprint_flat_fp_map; eauto. auto.
          (** Two cases *)
          destruct (eq_block b b0). subst.
          (* Case1: b = b0 *)
          ++ intros ([C1|[C2|C3]] & I1 & I2 & I3); try congruence.
             ** split.
                eapply bmatch_unchanged_on_loc; eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eapply assign_loc_perm_unchanged; eauto.
                (** sem_wt_loc *)
                intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC.
                eapply sem_wt_loc_unchanged_loc. eauto. eauto.                
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl.
                destruct H0.
                (** prove b must be not in fp *)
                intro. destruct H2. subst.
                congruence.
                lia.
             (* The same as above *)
             ** split.
                eapply bmatch_unchanged_on_loc; eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eapply assign_loc_perm_unchanged; eauto.
                (** sem_wt_loc *)
                intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC.
                eapply sem_wt_loc_unchanged_loc. eauto.
                eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl.
                destruct H0.
                (** prove b must be not in fp *)
                intro. destruct H2. subst.
                congruence.
                lia.
          (* Case2: b <> b0 *)
          ++ intros (N & I1 & I2 & I3). clear N. split.
             ** eapply bmatch_unchanged_on_block. eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eapply assign_loc_perm_unchanged; eauto.
             (** sem_wt_loc  *)
             ** intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC.
                eapply sem_wt_loc_unchanged_blocks. eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. intro. destruct H2. subst.
                destruct H0; try congruence.
                (** prove b must be not in fp: use the fact that
                "disjoint locations have disjoint footprints" *)                
        -- exploit get_loc_footprint_map_different_local. eauto. 
           2: eapply B. eauto. eauto. intros (N1 & N2 & N3).
           intros. clear H.
           erewrite <- get_set_different_local in GFP; eauto. 
           exploit MM. erewrite POP2. eauto. auto.           
           intros (BM1 & FULL1).
           exploit assign_loc_unchanged_on; eauto. intros UNC.
           split.
           eapply bmatch_unchanged_on_block. eauto.
           eapply Mem.unchanged_on_implies. eauto.
           intros. simpl. destruct H; try lia.
           eapply NSZREC. eauto.
           eapply blocks_perm_unchanged_normal.
           eapply assign_loc_perm_unchanged; eauto.
           (** sem_wt_loc *)
           intros FULL2.
           subst.
           erewrite <- init_place_full_unchanged in FULL2.
           exploit FULL1; eauto. intros WTLOC2.
           eapply sem_wt_loc_unchanged_blocks. eauto.
           eapply Mem.unchanged_on_implies. eauto. intros. simpl.
           destruct H; auto.
           (* b1 is in the fp: show that b must not be in the fp *)
           intro. destruct H1; subst. congruence.
           subst. intro. destruct H. subst. congruence.
Qed.

Lemma sem_cast_sem_wt: forall m fp v1 v2 ty1 ty2,
    sem_wt_val ce m fp v1 ->
    wt_footprint ce ty1 fp ->
    RustOp.sem_cast v1 ty1 ty2 = Some v2 ->
    sem_wt_val ce m fp v2 /\ wt_footprint ce ty2 fp.
Admitted.



(* The location of the member is sem_wt_loc. It is used in the invariant of dropstate *)
Inductive member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : member -> Prop :=
| member_footprint_struct: forall fofs fid fty
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (WTLOC: sem_wt_loc ce m fp b (ofs + fofs))
    (WTFP: wt_footprint ce fty fp),
    member_footprint m co b ofs fp (Member_plain fid fty)
| member_footprint_enum: forall fofs fid fty
    (STRUCT: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WTLOC: sem_wt_loc ce m fp b (ofs + fofs))
    (WTFP: wt_footprint ce fty fp),
    member_footprint m co b ofs fp (Member_plain fid fty)
.

(* hacking: simulate the deref_loc_rec to get the path, footprint and
location of the value. fp is the start of the footprint. *)
Inductive deref_loc_rec_footprint (m: mem) (b: block) (ofs: Z) (fty: type) (fp: footprint) : list type -> block -> Z -> type -> footprint -> Prop :=
| deref_loc_rec_footprint_nil:
  deref_loc_rec_footprint m b ofs fty fp nil b ofs fty fp
| deref_loc_rec_footprint_cons: forall ty tys fp2 b1 ofs1 b2 sz
    (* simulate type_to_drop_member_state *)
    (DEREF: deref_loc_rec_footprint m b ofs fty fp tys b1 ofs1 (Tbox ty) (fp_box b2 sz fp2))
    (TYSZ: sz = sizeof ce ty)
    (* Properties of bmatch *)
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b2 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (PERM: Mem.range_perm m b2 (- size_chunk Mptr) sz Cur Freeable),
    deref_loc_rec_footprint m b ofs fty fp ((Tbox ty) :: tys) b2 0 ty fp2.

(* Invariant of deref_loc_rec_footprint *)

(* Lemma deref_loc_rec_footprint_inv: forall m b1 b2 ofs1 ofs2 fp1 fp2 tyl phl, *)
(*     deref_loc_rec_footprint m b1 ofs1 fp1 tyl b2 ofs2 phl fp2 -> *)
(*     exists fp3, clear_footprint phl fp1 = Some fp3 /\ *)
(*              (* store fp2 to fp3 *) *)
(*              set_footprint phl fp2 fp3 = Some fp1 /\ *)
(*              deref_loc_rec_footprint m b1 ofs1 fp3 tyl b2 ofs2 phl fp_emp *)
(* . *)
(* Admitted. *)

(* the location computed by deref_loc_rec_footprint is the same as that computed by deref_loc_rec *)
(* Lemma deref_loc_rec_footprint_eq: forall m b ofs tys b1 ofs1 b2 ofs2 fp1 fp2 phl, *)
(*           deref_loc_rec m b (Ptrofs.repr ofs) tys (Vptr b1 ofs1) -> *)
(*           deref_loc_rec_footprint m b ofs fp1 tys b2 ofs2 phl fp2 -> *)
(*           b1 = b2 /\ ofs1 = Ptrofs.repr ofs2. *)
(* Admitted. *)

Inductive drop_member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : option drop_member_state -> Prop :=
| drop_member_fp_none:
    drop_member_footprint m co b ofs fp None
| drop_member_fp_comp_struct: forall fid fofs fty tyl b1 ofs1 fp1 compty
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 compty fp1)
    (* (b1, ofs1) is sem_wt_loc *)
    (WTLOC: sem_wt_loc ce m fp1 b1 ofs1)
    (WTFP: wt_footprint ce compty fp1),
    drop_member_footprint m co b ofs fp (Some (drop_member_comp fid fty compty tyl))
| drop_member_fp_comp_enum: forall fid fofs fty tyl b1 ofs1 fp1 compty
    (ENUM: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 compty fp1)
    (* (b1, ofs1) is sem_wt_loc *)
    (WTLOC: sem_wt_loc ce m fp1 b1 ofs1)
    (WTFP: wt_footprint ce compty fp1),
    drop_member_footprint m co b ofs fp (Some (drop_member_comp fid fty compty tyl))
| drop_member_fp_box_struct: forall fid fofs fty tyl b1 ofs1 ty
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 ty fp_emp),
    drop_member_footprint m co b ofs fp (Some (drop_member_box fid fty tyl))
| drop_member_fp_box_enum: forall fid fofs fty tyl b1 ofs1 ty
    (ENUM: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 ty fp_emp),
    drop_member_footprint m co b ofs fp (Some (drop_member_box fid fty tyl))
.


Fixpoint typeof_cont_call (ttop: type) (k: cont) : option type :=
  match k with
  | Kcall p _ _ _ _ =>
      Some (typeof_place p)
  | Kstop => Some ttop
  | Kseq _ k
  | Kloop _ k
  (* impossible? *)
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k => typeof_cont_call ttop k
  end.


(* Lemma split_drop_place_sound: forall ce own p universe drops *)
(*     (WF: wf_own_env own) *)
(*     (UNI: (own_universe own) ! (local_of_place p) = Some universe) *)
(*     (SPLIT: split_drop_place ce universe p (typeof_place p) = OK drops), *)
(*   sound_split_drop_place own drops. *)
(* Admitted. *)

(** Some thoughts about how to define sound_drop_place_state  *)
(** How to prove eval_place can get the footprint of p in
step_dropplace? We cannot use eval_place_sound because we cannot prove
that p's dominators are init. We can use the fact that the footprint
map is unchanged during step_dropplace. So we can prove that when
entering drop_fully_owned, the footprint of the split place can be
obtained (by get_loc_footprint_progress). Invariant of
drop_place_state must contain that we can use the extra paths of p to
get the footprint of p from the footprint of the (split place's
footprint), and show that this footprint is mmatch (sem_wt if it is
composite). How to prove that the locations evaluated by eval_place
and get_loc_footprint are the same? We need some eval_place_prefix
lemma to split eval_place to eval_prefix and eval_sufix, but how to
prove the result of eval_prefix is unchanged if we drop a place?? Can
we prove mmatch (yes, by mmatch_unchanged_on) when we move out some
footprint outside the footprint map and then use eval_place_sound to
show that the result of eval_prefix is unchanged? *)

(** How to prove the eval_place in step_dropplace has no memory error? *)

(* This relation says that for some root place (split place) residing
in (b,ofs) whose footprint is rfp, we can evaluate the places list and
get the place and its location (along with its type and footprint) of
the pointee of this list. So if this list is empty, the pointee is
just the root place itselt; if this list is not empty, the list must
have some given shape, and the location is evaluated by dereferencing
the location of the result of the remaining list. Some invariant, the
return place is the dereference of the head of the list or the root place *)
Inductive sound_split_fully_own_place (m: mem) (r: place) (b: block) (ofs: Z) (rfp: footprint) : list place -> place -> block -> Z -> type -> footprint -> Prop :=
| sound_split_nil:
  sound_split_fully_own_place m r b ofs rfp nil r b ofs (typeof_place r) rfp
| sound_split_cons: forall b1 ofs1 ty b2 sz fp2 l p1 
    (SOUND: sound_split_fully_own_place m r b ofs rfp l p1 b1 ofs1 (Tbox ty) (fp_box b2 sz fp2))
    (TYSZ: sz = sizeof ce ty)
    (* Properties of bmatch *)
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b2 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (PERM: Mem.range_perm m b2 (- size_chunk Mptr) sz Cur Freeable),
    sound_split_fully_own_place m r b ofs rfp (p1 :: l) (Pderef p1 ty) b2 0 ty fp2  
.

(* This relation is the invariant of the drop_place_state. In
particular, when there is a composite to be dropped, we should say
that the location "computed" by sound_split_fully_own_place is
semantically well-typed. The root place (and its location and its
footprint because we need to maintain some separation property of its
footprint and the other) is internal in this invariant because we do
not want to expose them in sound_cont (i.e., internal in
sound_cont). rfp is the footprint of this state *)
Inductive sound_drop_place_state (e: env) (m: mem) (fpm: fp_map) (own: own_env) : footprint -> option drop_place_state -> Prop :=
| sound_drop_place_state_none: sound_drop_place_state e m fpm own fp_emp None
| sound_drop_place_state_comp: forall r b ofs p l b1 ofs1 fp1 empfp rfp    (* Note that the footprint of r has been moved out (but we cannot
    ensure that its footprint is fp_emp because it may be a struct! *)
    (PFP: get_loc_footprint_map e (path_of_place r) fpm = Some (b, ofs, empfp))
    (NOREP: list_norepet (footprint_flat rfp))
    (* used to prove get_loc_footprint_map is equal to eval_place r) *)
    (DOM: dominators_is_init own r = true)
    (SPLIT: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 (typeof_place p) fp1)
    (WTLOC: sem_wt_loc ce m fp1 b1 ofs1)
    (WTP: wt_place e ce r)
    (WTFP: wt_footprint ce (typeof_place p) fp1),
    sound_drop_place_state e m fpm own rfp (Some (drop_fully_owned_comp p l))
| sound_drop_place_state_box: forall r b ofs l b1 ofs1 ty1 empfp p rfp fp
    (PFP: get_loc_footprint_map e (path_of_place r) fpm = Some (b, ofs, empfp))
    (NOREP: list_norepet (footprint_flat rfp))
    (DOM: dominators_is_init own r = true)
    (* The footprint of p must be empty to make rfp minimum so that we
    can prove no memory leak. But it make the sound_dropplace proof
    very difficult as we need to track the status of the footprint in
    the sound_dropplace *)
    (SPLIT: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp)
    (WTP: wt_place e ce r),
    sound_drop_place_state e m fpm own rfp (Some (drop_fully_owned_box l)).


Lemma sound_split_fully_own_place_type_inv: forall m r b ofs rfp l p b1 ofs1 ty1 fp1,
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    typeof_place p = ty1.
Proof.
  destruct l; intros.
  - inv H. auto.
  - inv H. simpl. auto.
Qed.
    
(* we also require that the produced footprint is norepet *)
Lemma sound_split_fully_own_place_footprint_inv: forall m r b ofs rfp l p b1 ofs1 ty1 fp1,
    list_norepet (footprint_flat rfp) ->
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    incl (footprint_flat fp1) (footprint_flat rfp)
    /\ In b1 (footprint_flat rfp)
    /\ ~ In b1 (footprint_flat rfp)
    /\ list_norepet (footprint_flat fp1).
Admitted.


(* sound_split_fully_own_place remains satisfied if the changed blocks
are outside the rfp/fp1 *)
Lemma sound_split_fully_own_place_unchanged: forall m1 m2 r b ofs rfp l p b1 ofs1 ty1 fp1
    (NOREP: list_norepet (footprint_flat rfp))
    (SOUND: sound_split_fully_own_place m1 r b ofs rfp l p b1 ofs1 ty1 fp1)
    (* block in fp1 can be changed *)
    (UNC: Mem.unchanged_on (fun b2 _ =>  In b2 (footprint_flat rfp) /\ ~ In b2 (footprint_flat fp1)) m1 m2),
    sound_split_fully_own_place m2 r b ofs rfp l p b1 ofs1 ty1 fp1.
Proof.
  induction l; intros.
  - inv SOUND. econstructor.
  - inv SOUND.
    exploit sound_split_fully_own_place_footprint_inv; eauto.
    intros (INCL & INb & NOTINb & NOREP1).
    econstructor; eauto.
    eapply IHl; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H.
    split; auto.
    (* load value *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. split; auto.
    (* load size of block *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. split.
    eapply INCL; simpl;  auto.
    simpl in NOREP1. inv NOREP1. auto.
    (* range_perm *)
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. split.
    eapply INCL; simpl;  auto.
    simpl in NOREP1. inv NOREP1. auto.
    (* valid_block *)
    eapply Mem.perm_valid_block; eauto.
Qed.

Lemma sound_split_fully_own_place_eval_place: forall l m r b ofs rfp p b1 ofs1 ty1 fp1 b2 ofs2 e
  (SOUND: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1)
  (EVAL: eval_place ce e m p b2 ofs2),
  exists b3 ofs3,
    eval_place ce e m r b3 ofs3
    /\ ((b3, Ptrofs.unsigned ofs3) = (b, ofs) -> (b1, ofs1) = (b2, Ptrofs.unsigned ofs2)).
Proof.
  induction l; intros.
  - inv SOUND. exists b2, ofs2.
    eauto.
  - inv SOUND. inv EVAL.
    exploit sound_split_fully_own_place_type_inv; eauto. intros TY.
    rewrite TY in *.
    inv H4; simpl in *; try congruence. inv H.
    exploit IHl; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exists b3, ofs3. split; auto.
    intros. inv H. exploit A2. auto.
    intros. inv H.
    rewrite LOAD in H0. inv H0.
    auto.
Qed.    

Lemma sound_split_fully_own_place_set: forall l m r b ofs rfp p b1 ofs1 ty1 fp1 fp2
    (SOUND: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1),
  exists rfp1,
    get_footprint (repeat ph_deref (length l)) rfp = Some fp1
    /\ set_footprint (repeat ph_deref (length l)) fp2 rfp = Some rfp1
    /\ sound_split_fully_own_place m r b ofs rfp1 l p b1 ofs1 ty1 fp2.
Proof.
  induction l; intros.
  - inv SOUND. simpl. eexists. repeat apply conj; eauto.
    econstructor.
  - inv SOUND. exploit IHl; eauto.
    instantiate (1 := fp_box b1 (sizeof ce ty1) fp2).    
    intros (rfp1 & A & B & C).
    cbn [length]. cbn [repeat].
    erewrite repeat_cons.
    exists rfp1. repeat apply conj.
    + eapply get_footprint_app; eauto.
    + eapply set_footprint_app; eauto.
      simpl. auto.
    + econstructor; eauto.
Qed.

    
(* soundness of continuation: the execution of current function cannot
modify the footprint maintained by the continuation *)

Inductive sound_cont : AN -> statement -> rustcfg -> cont -> node -> option node -> option node -> node -> mem -> fp_frame -> Prop :=
| sound_Kstop: forall an body cfg nret m
    (RET: cfg ! nret = Some Iend),
    sound_cont an body cfg Kstop nret None None nret m fpf_emp
| sound_Kseq: forall an body cfg s k pc next cont brk nret m fpf
    (MSTMT: match_stmt an body cfg s pc next cont brk nret)
    (MCONT: sound_cont an body cfg k next cont brk nret m fpf),
    sound_cont an body cfg (Kseq s k) next cont brk nret m fpf
| sound_Kloop: forall an body cfg s k body_start loop_jump_node exit_loop nret contn brk m fpf
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an body cfg s body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: sound_cont an body cfg k exit_loop contn brk nret m fpf),
    sound_cont an body cfg (Kloop s k)loop_jump_node (Some loop_jump_node) (Some exit_loop) nret m fpf
| sound_Kcall: forall an body cfg k nret f e own p m fpf
    (MSTK: sound_stacks (Kcall p f e own k) m fpf)
    (RET: cfg ! nret = Some Iend)
    (WFOWN: wf_own_env own),
    sound_cont an body cfg (Kcall p f e own k) nret None None nret m fpf
| sound_Kdropplace: forall f st ps nret cfg pc cont brk k own1 own2 e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit rfp
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc cont brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (WFNEV: wf_env fpm ce e)
    (** VERY DIFFICULT: Invariant of drop_place_state *)
    (SDP: sound_drop_place_state e m fpm own1 rfp st)
    (SEP: list_norepet (flat_fp_frame (fpf_dropplace e fpm rfp fpf)))
    (MOVESPLIT: move_split_places own1 ps = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst ps))
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env own1),
    sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg (Kdropplace f st ps e own1 k) pc cont brk nret m (fpf_func e fpm fpf)
| sound_Kdropcall: forall an body cfg k pc cont brk nret fpf st co fp ofs b membs fpl id m
    (CO: ce ! id = Some co)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (** Do we need some separation properties? *)
    (SOUND: sound_cont an body cfg k pc cont brk nret m fpf),
    sound_cont an body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret m (fpf_drop fp fpl fpf)

with sound_stacks : cont -> mem -> fp_frame -> Prop :=
| sound_stacks_stop: forall m,
    sound_stacks Kstop m fpf_emp
| sound_stacks_call: forall f nret cfg pc contn brk k own1 own2 p e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc contn brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (WFENV: wf_env fpm ce e)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env own1),
    sound_stacks (Kcall p f e own1 k) m (fpf_func e fpm fpf).
    

(** TODO: add syntactic well typedness in the sound_state and
sound_cont *)
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s pc next cont brk nret k e own m fpm fpf flat_fp sg mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (STMT: match_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s pc next cont brk nret)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own mayinit mayuninit universe)
    (MM: mmatch fpm ce m e own)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (* footprint is separated *)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m))
    (* we need to maintain the well-formed invariant of own_env *)
    (WFENV: wf_env fpm ce e)
    (* invariant of the own_env *)
    (WFOWN: wf_own_env own),
    sound_state (State f s k e own m)
| sound_dropplace: forall f cfg entry maybeInit maybeUninit universe next cont brk nret st drops k e own1 own2 m fpm fpf flat_fp sg mayinit mayuninit rfp
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (FLAT: flat_fp = flat_fp_frame (fpf_dropplace e fpm rfp fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m))
    (* every place in the drop_fully_owned state is owned: this may be
    wrong because it does not consider own is changing *)
    (SDP: sound_drop_place_state e m fpm own1 rfp st)
    (* big step update of the own_env *)
    (MOVESPLIT: move_split_places own1 drops = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst drops))
    (* fullspec is used to maintain the invariant between is_full and the full flags *)
    (FULLSPEC: forall p full,  In (p, full) drops -> is_full (own_universe own1) p = full)
    (WF: wf_env fpm ce e)
    (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit)))
    (* Why sound_own own2 here not own1? because the analysis result is about the next node *)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env own1),
    (* no need to maintain borrow check domain in dropplace? But how
    to record the pc and next statement? *)
    sound_state (Dropplace f st drops k e own1 m)
| sound_dropstate: forall an body cfg next cont brk nret id co fp fpl b ofs st m membs k fpf flat_fp sg
    (CO: ce ! id = Some co)
    (* The key is how to prove semantics well typed can derive the
    following two properties *)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (* all the remaining members are semantically well typed *)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (CONT: sound_cont an body cfg k next cont brk nret m fpf)
    (FLAT: flat_fp = flat_fp_frame (fpf_drop fp fpl fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m)),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k flat_fp sg
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL: sem_wt_val_list ce m fpl args)
    (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl)
    (STK: sound_stacks k m fpf)
    (FLAT: flat_fp = flat_fp_frame fpf)
    (* also disjointness of fpl and fpf *)
    (NOREP: list_norepet (flat_fp ++ concat (map footprint_flat fpl)))
    (ACC: rsw_acc w (rsw sg flat_fp m)),
    sound_state (Callstate vf args k m)
| sound_returnstate: forall sg flat_fp m k retty rfp v
    (ACC: rsw_acc w (rsw sg flat_fp m))
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = Some retty)
    (WTVAL: sem_wt_val ce m rfp v)
    (WTFP: wt_footprint ce (rs_sig_res sg) rfp)
    (SEP: list_norepet (flat_fp ++ (footprint_flat rfp))),
    sound_state (Returnstate v k m)
.



(* (* sound_cont is preserved if its footprint is unchanged *) *)

(* (* Similar to non-interference properties? *) *)
Lemma sound_cont_unchanged: forall m1 m2 fpf k an body cfg next cont brk nret
  (SOUND: sound_cont an body cfg k next cont brk nret m1 fpf)
  (UNC: Mem.unchanged_on (fun b _ => In b (flat_fp_frame fpf)) m1 m2),
    sound_cont an body cfg k next cont brk nret m2 fpf.
Admitted.

Lemma mmatch_unchanged: forall m1 m2 fpm e own,
    mmatch fpm ce m1 e own ->
    Mem.unchanged_on (fun b _ => In b (flat_fp_map fpm)) m1 m2 ->
    mmatch fpm ce m2 e own.
Admitted.

           
(* Lemma deref_loc_rec_no_mem_error: forall m b ofs tys fp b1 ofs1 phl fp1, *)
(*     deref_loc_rec_mem_error m b (Ptrofs.repr ofs) tys -> *)
(*     deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl fp1 -> *)
(*     False. *)
(* Admitted. *)

(* (** TODO: Maybe we should require that fp is disjoint because the memory is *)
(* changed during the drop *) *)
(* Lemma drop_box_rec_no_mem_error: forall m b ofs tys fp b1 ofs1 phl fp1, *)
(*     list_norepet (footprint_flat fp) -> *)
(*     drop_box_rec_mem_error ge b (Ptrofs.repr ofs) m tys -> *)
(*     deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl fp1 -> *)
(*     False. *)
(* Admitted. *)


(* Lemma sound_dropstate_no_mem_error: forall s, *)
(*     step_drop_mem_error ge s -> sound_state s -> False. *)
(* Proof. *)
(*   intros s ERR SOUND. *)
(*   inv ERR. *)
(*   (* step_dropstate_struct_error1 *) *)
(*   - inv SOUND. *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1.     *)
(*     (* GOAL: To show that deref_loc_rec_mem_error is impossible if *)
(*     (b1,ofs1) has footprint fp *) *)
(*     inv DROPMEMB. *)
(*     (* co1.(co_sv) = Struct *) *)
(*     + rewrite STRUCT in FOFS. *)
(*       unfold ce in FOFS0. *)
(*       rewrite FOFS in FOFS0. inv FOFS0. *)
(*       rewrite Ptrofs.add_unsigned in DEREF. *)
(*       (* some overflow constrain *) *)
(*       assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit. *)
(*       rewrite Ptrofs.unsigned_repr in DEREF; eauto. *)
(*       eapply deref_loc_rec_no_mem_error; eauto. *)
(*     (* co1.(co_sv) = TaggedUnion *) *)
(*     + admit. *)
(*   (* step_dropstate_enum_error1 *) *)
(*   - inv SOUND. *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1. *)
(*     inv DROPMEMB. *)
(*     (* co1.(co_sv) = Struct *) *)
(*     + rewrite STRUCT in FOFS. *)
(*       unfold ce in FOFS0. *)
(*       rewrite FOFS in FOFS0. inv FOFS0. *)
(*       rewrite Ptrofs.add_unsigned in DEREF. *)
(*       (* some overflow constrain *) *)
(*       assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit. *)
(*       rewrite Ptrofs.unsigned_repr in DEREF; eauto. *)
(*       eapply deref_loc_rec_no_mem_error; eauto. *)
(*     (* co1.(co_sv) = TaggedUnion *) *)
(*     + admit. *)
(*   (* step_dropstate_enum_error2: load tag error *) *)
(*   - inv SOUND. *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1. *)
(*     inv DROPMEMB. *)
(*     (* co1.(co_sv) = Struct *) *)
(*     + rewrite STRUCT in FOFS. *)
(*       unfold ce in FOFS0. *)
(*       rewrite FOFS in FOFS0. inv FOFS0. *)
(*       rewrite Ptrofs.add_unsigned in DEREF. *)
(*       (* some overflow constrain *) *)
(*       assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit. *)
(*       rewrite Ptrofs.unsigned_repr in DEREF; eauto. *)
(*       (** Prove that deref_loc_rec and deref_loc_rec_footprint get the same address *) *)
(*       exploit deref_loc_rec_footprint_eq; eauto. *)
(*       intros (A & B). subst. *)
(*       (* (b0,ofs0) is semantically well typed location, so load tag *)
(*       error is impossible *) *)
(*       inv WT. *)
(*       simpl in MODE. congruence. *)
(*       eapply TAG. *)
(*       eapply Mem.load_valid_access. *)
(*       (* some overflow constrain *) *)
(*       assert (OFSRANGE: 0 <= ofs0 <= Ptrofs.max_unsigned) by admit. *)
(*       rewrite Ptrofs.unsigned_repr; eauto. *)
(*     (* co1.(co_sv) = TaggedUnion *) *)
(*     + admit. *)
(*   (* step_dropstate_box_error *) *)
(*   - inv SOUND. *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1. *)
(*     inv DROPMEMB. *)
(*     (* co1.(co_sv) = Struct *) *)
(*     + rewrite STRUCT in FOFS. *)
(*       unfold ce in FOFS0. *)
(*       rewrite FOFS in FOFS0. inv FOFS0. *)
(*       rewrite Ptrofs.add_unsigned in DROPB. *)
(*       (* some overflow constrain *) *)
(*       assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit. *)
(*       rewrite Ptrofs.unsigned_repr in DROPB; eauto. *)
(*       (** show that drop_box_rec_mem_error is impossible if there is *)
(*       deref_loc_rec_footprint *) *)
(*       eapply drop_box_rec_no_mem_error; eauto. *)
(*       (* norepet proof *) *)
(*       admit. *)
(*     (* co1.(co_sv) = TaggedUnion *) *)
(*     + admit. *)
(* Admitted. *)

(* Lemma sound_dropplace_no_mem_error: forall s, *)
(*     step_dropplace_mem_error ge s -> sound_state s -> False. *)
(* Proof. *)
(*   intros s ERR SOUND. *)
(*   inv ERR. *)
(*   (* step_dropplace_box_error1 *) *)
(*   - inv SOUND. inv DP. *)
(*     (* p is owned so that eval_place p must not be error *) *)
(*     eapply eval_place_no_mem_error. eauto. eauto. *)
(*     (* syntactic well typedness *) *)
(*     instantiate (1 := p). *)
(*     admit. *)
(*     simpl in OWN. eapply andb_true_iff in OWN. *)
(*     destruct OWN as (POWN & LOWN). *)
(*     eapply wf_own_dominator; eauto. *)
(*     auto. *)
(*   (* step_dropplace_box_error2 *) *)
(*   - inv SOUND. inv DP. *)
(*     simpl in OWN. eapply andb_true_iff in OWN. *)
(*     destruct OWN as (POWN & LOWN). *)
(*     exploit eval_place_sound. 1-3: eauto. *)
(*     (* syntactic well typedness *) *)
(*     admit. *)
(*     eapply wf_own_dominator; auto. *)
(*     intros (pfp & PFP). *)
(*     exploit MM. eauto. eauto. *)
(*     intros BM. *)
(*     rewrite PTY in BM. inv BM. *)
(*     inv PVAL. *)
(*     eapply H0. *)
(*     simpl in H. inv H. *)
(*     eapply Mem.load_valid_access. eauto. *)
(*     simpl in TY. congruence. *)
(*   (* step_dropplace_box_error3 *) *)
(*   - inv SOUND. inv DP. *)
(*     simpl in OWN. eapply andb_true_iff in OWN. *)
(*     destruct OWN as (POWN & LOWN). *)
(*     exploit eval_place_sound. 1-3: eauto. *)
(*     (* syntactic well typedness *) *)
(*     admit. *)
(*     eapply wf_own_dominator; auto. *)
(*     intros (pfp & PFP). *)
(*     exploit MM. eauto. eauto. *)
(*     intros BM. *)
(*     rewrite PTY in BM. inv BM. *)
(*     + inv PVAL. *)
(*       simpl in H. inv H. simpl in H0. rewrite H0 in LOAD. *)
(*       inv LOAD. *)
(*       (** TODO: show contradiction between extcall_free_sem_mem_error *)
(*       and Mem.range_perm Freeable *) *)
(*       admit. *)
(*       simpl in H0. congruence. *)
(*       simpl in H0. congruence. *)
(*     + simpl in TY. congruence. *)
(*   (* step_dropplace_comp_error *) *)
(*   - inv SOUND. inv DP. *)
(*     (* movable place is owned *) *)
(*     assert (POWN: is_owned own p = true) by admit. *)
(*     (* eval_place error is impossible *) *)
(*     eapply eval_place_no_mem_error. eauto. eauto. *)
(*     (* syntactic well typedness *) *)
(*     instantiate (1 := p). admit. *)
(*     eapply wf_own_dominator; auto. *)
(*     auto. *)
(* Admitted. *)

(* Lemma sound_state_no_mem_error: forall s, *)
(*     step_mem_error ge s -> sound_state s -> False . *)
(* Admitted. *)

Lemma initial_state_sound: forall q s,
    query_inv wt_rs (se, w) q ->
    Smallstep.initial_state L q s ->
    sound_state s /\ wt_state ce s.
Admitted.

(* Lemma step_drop_sound: forall s1 t s2, *)
(*     sound_state s1 -> *)
(*     step_drop ge s1 t s2 -> *)
(*     (* how to prove sound_state in dropstate? *) *)
(*     sound_state s2. *)
(* Proof. *)
(*   intros s1 t s2 SOUND STEP. *)
(*   inv STEP. *)
(*   (* step_dropstate_init *) *)
(*   - inv SOUND. *)
(*     (* fp is fp_emp *) *)
(*     inv DROPMEMB. *)
(*     inv MEMBFP. rename H2 into MEMBFP. rename H3 into MEMBS. *)
(*     econstructor; eauto. instantiate (1 := a1). *)
(*     (** TODO: relation between member_footprint and drop_member_footprint *) *)
(*     admit. *)
(*     (* easy: list norepet *) *)
(*     admit. *)
(*     (* easy: accessibility *) *)
(*     instantiate (1 := sg). admit. *)
(*   (* step_dropstate_struct *) *)
(*   - inv SOUND. *)
(*     (* rewrite ce!id1 *) *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1. *)
(*     inv DROPMEMB. *)
(*     (* co_sv co1 is struct *) *)
(*     + rewrite STRUCT0 in FOFS. *)
(*       (* clear fp1 from fp *) *)
(*       exploit deref_loc_rec_footprint_inv; eauto. *)
(*       intros (fp3 & CLEAR & SET & FPREC). *)
(*       econstructor. eauto. *)
(*       econstructor. *)
(*       (** TODO: show the footprint of the members in co2 using (b0,ofs0) *)
(*     is sem_wt_loc *) *)
(*       admit. *)
(*       (* sound_cont *) *)
(*       instantiate (1 := (fpf_drop fp3 fpl fpf)). *)
(*       econstructor; eauto. *)
(*       eapply drop_member_fp_box_struct; eauto. *)
(*       (* end of sound_cont *) *)
(*       (* construct the flat footprint *) *)
(*       eauto. *)
(*       (* easy: norepet *) *)
(*       admit. *)
(*       (* easy: accessibility *) *)
(*       admit. *)
(*     (* co_sv co1 is enum *) *)
(*     + rewrite ENUM in FOFS. *)
(*       (* clear fp1 from fp *) *)
(*       exploit deref_loc_rec_footprint_inv; eauto. *)
(*       intros (fp3 & CLEAR & SET & FPREC). *)
(*       econstructor. eauto. *)
(*       econstructor. *)
(*       (** TODO: show the footprint of the members in co2 using (b0,ofs0) *)
(*     is sem_wt_loc *) *)
(*       admit. *)
(*       (* sound_cont *) *)
(*       instantiate (1 := (fpf_drop fp3 fpl fpf)). *)
(*       econstructor; eauto. *)
(*       eapply drop_member_fp_box_enum; eauto. *)
(*       (* end of sound_cont *) *)
(*       (* construct the flat footprint *) *)
(*       eauto. *)
(*       (* easy: norepet *) *)
(*       admit. *)
(*       (* easy: accessibility *) *)
(*       admit. *)
(*   (* step_dropstate_enum (similar to step_dropstate_struct case) *) *)
(*   - admit. *)
(*   (* step_dropstate_box (memory is updated) *) *)
(*   - inv SOUND. *)
(*     (* rewrite ce!id *) *)
(*     unfold ce in CO. rewrite CO in CO1. inv CO1. *)
(*     inv DROPMEMB. *)
(*     (* co_sv co = Struct *) *)
(*     + (** TODO: prove that drop_box_rec unchanged_on (In b fp) *) *)
(*       assert (UNC: Mem.unchanged_on (fun b _ => ~ In b (footprint_flat fp)) m m'). *)
(*       admit. *)
(*       econstructor. eauto. *)
(*       econstructor. *)
(*       (* prove the soundness of the remaining fields members *) *)
(*       instantiate (1 := fpl). admit. *)
(*       (* sound_cont: use unchanged property *) *)
(*       eapply sound_cont_unchanged; eauto. *)
(*       eapply Mem.unchanged_on_implies; eauto. *)
(*       (* easy: prove the disjointness between fpf and fp *) *)
(*       admit. *)
(*       eauto. *)
(*       (* easy: norepet *) *)
(*       admit. *)
(*       (* easy: accessibility *) *)
(*       instantiate (1 := sg). *)
(*       admit. *)
(*     (* co_sv co = TaggedUnion *) *)
(*     + (** TODO: prove that drop_box_rec unchanged_on (In b fp) *) *)
(*       assert (UNC: Mem.unchanged_on (fun b _ => ~ In b (footprint_flat fp)) m m'). *)
(*       admit. *)
(*       econstructor. eauto. *)
(*       econstructor. *)
(*       (* prove the soundness of the remaining fields members *) *)
(*       instantiate (1 := fpl). admit. *)
(*       (* sound_cont: use unchanged property *) *)
(*       eapply sound_cont_unchanged; eauto. *)
(*       eapply Mem.unchanged_on_implies; eauto. *)
(*       (* easy: prove the disjointness between fpf and fp *) *)
(*       admit. *)
(*       eauto. *)
(*       (* easy: norepet *) *)
(*       admit. *)
(*       (* easy: accessibility *) *)
(*       instantiate (1 := sg). *)
(*       admit. *)

(*   (* step_dropstate_return1 *) *)
(*   - inv SOUND. *)
(*     inv CONT. *)
(*     econstructor; eauto. *)
(*     (* easy: norepet *) *)
(*     admit. *)
(*     (* easy: accessibility *) *)
(*     instantiate (1 := sg). *)
(*     admit. *)
(*   (* step_dropstate_return1 *) *)
(*   - inv SOUND. *)
(*     inv CONT. *)
(*     econstructor; eauto. *)
(*     (* easy: norepet *) *)
(*     admit. *)
(*     (* easy: accessibility *) *)
(*     instantiate (1 := sg). *)
(*     admit. *)
(* Admitted. *)

Lemma valid_owner_same: forall p ty fid,
    ~ In (ph_downcast ty fid) (snd (path_of_place p)) ->
    valid_owner p = p.
Admitted.


Lemma sound_split_fully_own_place_app: forall l1 l2 m p1 p2 p3 b1 b2 b3 ofs1 ofs2 ofs3 fp1 fp2 fp3 ty2 ty3,
    sound_split_fully_own_place m p1 b1 ofs1 fp1 l1 p2 b2 ofs2 ty2 fp2 ->
    sound_split_fully_own_place m p2 b2 ofs2 fp2 l2 p3 b3 ofs3 ty3 fp3 ->
    sound_split_fully_own_place m p1 b1 ofs1 fp1 (l2++l1) p3 b3 ofs3 ty3 fp3.
Proof.
  induction l2; intros.
  - exploit sound_split_fully_own_place_type_inv. eapply H. intros. subst.
    inv H0. simpl.   auto.
  - inv H0. exploit sound_split_fully_own_place_type_inv. eapply H. intros. subst.
    simpl. econstructor.
    eapply IHl2; eauto. all: eauto.
Qed.

(* Used to prove gen_drop_place_state_sound. We only consider non-empty list. *)
Lemma split_fully_own_place_sound: forall ty p m b ofs fp p0 l
    (PTY: typeof_place p = ty)
    (SPLIT: split_fully_own_place p ty = p0 :: l)
    (WTLOC: sem_wt_loc ce m fp b ofs)
    (WTFP: wt_footprint ce (typeof_place p) fp),
    exists b1 ofs1 fp1,
      sound_split_fully_own_place m p b ofs fp l p0 b1 ofs1 (typeof_place p0) fp1
      /\ sem_wt_loc ce m fp1 b1 ofs1
      /\ wt_footprint ce (typeof_place p0) fp1.
Proof.
  induction ty; intros; simpl in *; try congruence.
  - destruct l.
    + eapply app_eq_unit in SPLIT. destruct SPLIT as [[A1 A2]|[B1 B2]]; try congruence.
      inv A2.
      exists b, ofs, fp. repeat apply conj; auto.
      econstructor.
    + destruct (split_fully_own_place (Pderef p ty) ty) eqn: SPLIT1; simpl in SPLIT; try congruence.
      inv SPLIT.
      (* get fp *)
      rewrite PTY in WTFP. inv WTFP. inv WTLOC. simpl in WF. congruence.
      inv WTLOC. inv WT0.
      exploit IHty. 2: eauto. simpl. auto.
      eapply WTLOC. simpl. auto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      exists b1, ofs1, fp1. repeat apply conj; auto.
      eapply sound_split_fully_own_place_app.
      econstructor. erewrite <- PTY. econstructor.
      all: auto.   
  - destruct l0; try congruence. inv SPLIT.
    exists b, ofs, fp. repeat apply conj; auto.
      econstructor.
  - destruct l0; try congruence. inv SPLIT.
    exists b, ofs, fp. repeat apply conj; auto.
    econstructor.
Qed.

  
Lemma split_fully_own_place_cons_type: forall ty p p1 l,
    typeof_place p = ty ->
    split_fully_own_place p ty = p1 :: l ->
    (exists orgs id, typeof_place p1 = Tstruct orgs id)
    \/ (exists orgs id, typeof_place p1 = Tvariant orgs id)
    \/ (exists ty, typeof_place p1 = Tbox ty).
Proof.
  induction ty; intros; simpl in *; try congruence.
  - destruct l.
    + eapply app_eq_unit in H0. destruct H0 as [[A1 A2]|[B1 B2]]; try congruence.
      inv A2. eauto.
    + destruct (split_fully_own_place (Pderef p ty) ty) eqn: SPLIT1; simpl in H0; try congruence.
      inv H0.
      eapply IHty. instantiate (1 := Pderef p ty). auto. eauto.
  - inv H0. eauto.
  - inv H0. eauto.
Qed.
    
Lemma gen_drop_place_state_sound: forall p own fp b ofs m empfp fpm (le: env),
    wt_place le ce p ->
    dominators_is_init own p = true ->
    sem_wt_loc ce m fp b ofs ->
    wt_footprint ce (typeof_place p) fp ->
    get_loc_footprint_map le (path_of_place p) fpm = Some (b, ofs, empfp) ->
    list_norepet (footprint_flat fp) ->
    sound_drop_place_state le m fpm own fp (Some (gen_drop_place_state p)).
Proof.
  intros until le; intros WTP DOM WTLOC WTFP GFP NOREP; unfold gen_drop_place_state.
  destruct (split_fully_own_place p (typeof_place p)) eqn: SPLIT.
  - econstructor; eauto.
    econstructor.
  - exploit split_fully_own_place_cons_type; eauto.
    intros. destruct H as [A|B]. 2: destruct B.
    + destruct A as (orgs & id & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      econstructor; eauto.
    + destruct H as (orgs & id & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      econstructor; eauto.
    + destruct H as (ty & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      rewrite TYP1 in *.
      inv A3. inv A2. simpl in WF. congruence.
      inv A2. inv WT0.
      econstructor; eauto.
      econstructor; eauto.
Qed.

(* Set a wt footprint in the footprint map remains wf_env *)
Lemma set_footprint_map_wf_env: forall phl id fpm1 fpm2 ce le fp ty,
    wt_footprint ce ty fp ->
    set_footprint_map (id, phl) fp fpm1 = Some fpm2 ->
    wf_env fpm1 ce le ->
    wf_env fpm2 ce le.
Admitted.

(* The empty footprint is well-typed *)
Lemma clear_wt_footprint_wt: forall fp ty,
    wt_footprint ce ty fp ->
    wt_footprint ce ty (clear_footprint_rec fp).
Admitted.

(* Extract useful properties if only the fpm is changed *)
Lemma list_norepet3_fpm_changed {A: Type} : forall (le fpm fpf: list A),
    list_norepet (le ++ fpm ++ fpf) ->
    list_norepet (le ++ fpf)
    /\ list_norepet fpm 
    /\ list_disjoint (le ++ fpf) fpm
    (* used in get_loc_footprint_norepet *)
    /\ list_disjoint le fpm
    (* the separation of stack and heap *)
    /\ list_norepet (le ++ fpm)
    (* used to prove that block changed in le ++ fpm must be not in
    fpf, which is used to prove sound_cont *)
    /\ list_disjoint (le ++ fpm) fpf.
Admitted.


Lemma step_dropplace_sound: forall s1 t s2,
    sound_state s1 ->
    wt_state ce s1 ->
    step_dropplace ge s1 t s2 ->
    sound_state s2 /\ wt_state ce s2.
Proof.
  intros s1 t s2 SOUND WTST STEP.
  inv STEP.
  (* step_dropplace_init1 *)
  - inv SOUND. inv ORDERED.
    simpl in *. rewrite NOTOWN in *.
    split.
    econstructor; eauto.
    (* wt_state: may be lift to a lemma *)
    inv WTST.
    econstructor. inv WT1. auto.     
  (* step_dropplace_init2 *)
  - inv SOUND. inv ORDERED.
    simpl in *. rewrite OWN in *.
    (* compute the new footprint map: it require some well-formed
    properties of own_env *)
    exploit get_loc_footprint_map_progress. eauto. eauto.
    (* wt_place *)
    instantiate (1 := p). inv WTST. inv WT1. auto.
    (* dominators_is_init *)
    eapply wf_own_dominators; eauto.
    (* place p does not contain downcast *)
    intros. eapply wf_own_no_downcast. eauto.
    eapply is_init_in_universe. eauto.    
    intros (b & ofs & fp & GFP & WTFP).
    (* remove fp from fpm *)
    destruct (path_of_place p) eqn: POP.
    exploit get_set_footprint_map_exists. eauto.
    instantiate (1 := clear_footprint_rec fp). intros (fpm1 & CLR & GFP1).
    (* p has no downcast *)
    assert (forall ty fid, ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. eapply wf_own_no_downcast. eauto. eapply is_init_in_universe. auto. }
    split. inv SDP.
    (* destruct the norepet *)
    simpl in NOREP.
    eapply list_norepet3_fpm_changed in NOREP.
    destruct NOREP as (A1 & A2 & A3 & A4 & A5).    
    eapply sound_dropplace with (fpm:=fpm1) (rfp:=fp); eauto.
    (* mmatch: use mmatch_move_place_sound *)
    erewrite <- (valid_owner_same p).
    eapply mmatch_move_place_sound. eauto.
    all: try erewrite valid_owner_same; eauto.
    exists p. split.
    eapply Paths.mem_2. eapply is_init_in_universe. auto.
    apply is_shallow_prefix_refl.
    unfold clear_footprint_map. rewrite POP. rewrite GFP. auto.
    (* norepet of the footprint frame *)
    simpl.
    erewrite (app_assoc (flat_fp_map fpm1)).
    eapply list_norepet_append_commut2.
    rewrite app_assoc.
    eapply list_norepet_app. repeat apply conj; auto.
    eapply list_norepet_app. repeat apply conj.
    eapply set_disjoint_footprint_norepet. eauto. eauto.
    erewrite empty_footprint_flat. red. intros. inv H1.
    eapply get_loc_footprint_map_norepet; eauto.
    eapply get_set_disjoint_footprint_map; eauto.
    erewrite empty_footprint_flat. red. intros. inv H1.
    red. intros. eapply A3; auto.
    eapply in_app in H1. destruct H1.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    erewrite empty_footprint_flat in B. inv B.
    eapply get_loc_footprint_map_incl; eauto.        
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto.
    econstructor. eapply Mem.unchanged_on_refl.
    simpl. red. intros. intro. eapply H0.
    rewrite !in_app_iff.
    rewrite !in_app_iff in H1. repeat destruct H1; auto.
    right. left.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    rewrite empty_footprint_flat in B. inv B.
    right. left.
    eapply get_loc_footprint_map_incl; eauto.
    (** IMPORTATN TODO: prove sound_drop_place_state, but first we
    test if sound_drop_place_state is enough or not *)
    exploit MM. erewrite POP. eauto. auto.
    intros (BM & FULL).
    (* prove that full is true then p is_full *)
    destruct full.
    exploit FULL. eapply FULLSPEC. auto. intros WTLOC.
    (* soundness of gen_drop_place_state *)
    exploit move_place_dominator_still_init. eapply wf_own_dominators; eauto.
    intros DOM1. inv WTST. inv WT1.
    eapply gen_drop_place_state_sound; eauto.
    rewrite POP. eauto.
    eapply get_loc_footprint_map_norepet; eauto.
    (* case2 *)
    { exploit FULLSPEC. left. eauto.
      intros F.
      (* p's type must be Box type *)
      exploit wf_own_type. eauto.
      eapply is_init_in_universe. eauto. auto.
      intros (ty & B3).
      (* how do we know the type of p? How can we ensure that the *)
      (*         footprint of p is fp_emp? *)
      erewrite B3 in *.  inv WTFP;  try congruence.
      inv BM. inv BM.
      eapply sound_drop_place_state_box with (r:=p). erewrite POP.
      eauto.
      (* norepet *)
      eapply get_loc_footprint_map_norepet; eauto.
      (* dominator is init *)
      eapply move_place_dominator_still_init.
      eapply wf_own_dominators; eauto.
      (* sound_split_fully_own_place *)
      econstructor. erewrite <- B3. eapply sound_split_nil; eauto.
      all: eauto. inv WTST. inv WT1. auto. }
    (* wf_env *)
    eapply set_footprint_map_wf_env. 
    eapply clear_wt_footprint_wt. eauto.
    eauto. auto.    
    (* wf_own_env *)
    eapply wf_own_env_move_place. auto.
    (* wt_state *)
    admit.
  (* step_dropplace_scalar: mostly the same as step_dropplace_init2
  because p is init and the type of p does not affect the proof of
  sound_state *)
  - inv SOUND. inv SDP. simpl in *. rewrite OWN in *.
    (* compute the new footprint map: it require some well-formed
    properties of own_env *)
    exploit get_loc_footprint_map_progress. eauto. eauto.
    (* wt_place *)
    instantiate (1 := p). inv WTST. inv WT1. auto.
    (* dominators_is_init *)
    eapply wf_own_dominators; eauto.
    (* place p does not contain downcast *)
    intros. eapply wf_own_no_downcast. eauto.
    eapply is_init_in_universe. eauto.    
    intros (b & ofs & fp & GFP & WTFP).
    (* remove fp from fpm *)
    destruct (path_of_place p) eqn: POP.
    exploit get_set_footprint_map_exists. eauto.
    instantiate (1 := clear_footprint_rec fp). intros (fpm1 & CLR & GFP1).
    (* p has no downcast *)
    assert (forall ty fid, ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. eapply wf_own_no_downcast. eauto. eapply is_init_in_universe. auto. }
    split. 
    eapply sound_dropplace with (fpm:=fpm1) (rfp:=fp_emp); eauto.
    (* mmatch: use mmatch_move_place_sound *)
    erewrite <- (valid_owner_same p).
    eapply mmatch_move_place_sound. eauto.
    all: try erewrite valid_owner_same; eauto.
    exists p. split.
    eapply Paths.mem_2. eapply is_init_in_universe. auto.
    apply is_shallow_prefix_refl.
    unfold clear_footprint_map. rewrite POP. rewrite GFP. auto.
    (* norepet of the footprint frame *)
    simpl.
    eapply list_norepet_append_commut2.
    eapply list_norepet_append_commut2 in NOREP.
    rewrite app_assoc in *.
    eapply list_norepet_app in NOREP. destruct NOREP as (A1 & A2 & A3).
    eapply list_norepet_app. repeat apply conj; auto.
    eapply set_disjoint_footprint_norepet. eauto. eauto.
    erewrite empty_footprint_flat. red. intros. inv H1.
    red. intros. eapply A3; auto.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    erewrite empty_footprint_flat in B. inv B.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto.
    econstructor. eapply Mem.unchanged_on_refl.
    simpl. red. intros. intro. eapply H0.
    rewrite !in_app_iff.
    rewrite !in_app_iff in H1. repeat destruct H1; auto.
    right. left.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    rewrite empty_footprint_flat in B. inv B.
    (* sound_drop_place_state *)
    econstructor.
    (* move_ordered_split_places_spec *)
    inv ORDERED. rewrite OWN in *. auto.
    (* wf_env *)
    eapply set_footprint_map_wf_env. 
    eapply clear_wt_footprint_wt. eauto.
    eauto. auto.    
    (* wf_own_env *)
    eapply wf_own_env_move_place. auto.
    (* wt_state *)
    admit.    
  (* step_dropplace_box *)
  - inv SOUND. inv SDP. inv SPLIT.
    (* To prove the (b,ofs) is equal to (b2,ofs2) so that (b', ofs')
    is equal to (b1, 0). But we first need to show that eval_place r
    is (b0, ofs0). It is possible because eval_place p has been
    successful *)
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & EVALR & A).
    (* the locations of get_loc_footprint_map and eval_place are the
    same. Do we need to prove that all the dominators of r is init to
    utilize mmatch? *)
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3). subst.
    exploit A. auto. intros A2. inv A2.
    (* prove (b',ofs') = (b1,0) *)
    inv PVAL; simpl in *; try congruence. inv H.
    rewrite LOAD in H0. inv H0.
    (* use sound_split_fully_own_place_unchanged,  m -> m' only changes b' *)
    inv FREE.
    exploit sound_split_fully_own_place_unchanged. 2: eapply SOUND.
    auto. eapply Mem.free_unchanged_on. eauto.
    intros. intro. destruct H0. apply H3. simpl. auto.
    intros SOUND1.
    (* sound_split_fully_own still holds after removing the final footprint of rfp *)
    exploit sound_split_fully_own_place_set; eauto.
    instantiate (1 := fp_emp). intros (rfp1 & G1 & G2 & G3).
    (* b' is not in (fpm ++ fpf). It is used to prove sound_cont and mmatch *)
    generalize NOREP as NOREP1. intros.
    erewrite app_assoc in NOREP.
    eapply list_norepet_append_commut2 in NOREP.
    erewrite app_assoc in NOREP.
    eapply list_norepet_app in NOREP.
    destruct NOREP as (N1 & N2 & N3).
    assert (NOTIN: ~ In b' (flat_fp_map fpm ++ flat_fp_frame fpf)).
    { intro. eapply in_app in H. destruct H.
      eapply N3. eapply in_app. left. eapply in_app. eauto.
      eapply get_footprint_incl; eauto. simpl. eauto. auto.
      eapply N3. eapply in_app. right. eauto.
      eapply get_footprint_incl; eauto. simpl. eauto. auto. }
    (* norepet of rfp1 *)
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      simpl. econstructor.
      simpl. red. intros. inv H0. }
    split.
    (* prove sound_dropplace *)
    eapply sound_dropplace with (rfp := rfp1); eauto.
    (* sound_cont *)
    eapply sound_cont_unchanged; eauto.
    eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply NOTIN. eapply in_app_iff. right. auto.
    (* mmatch *)
    eapply mmatch_unchanged; eauto.
    eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply NOTIN. eapply in_app_iff. left. auto.
    (* norepet *)
    simpl.
    erewrite app_assoc.
    eapply list_norepet_append_commut2.
    erewrite app_assoc.
    eapply list_norepet_app. repeat apply conj; eauto.
    red. intros. eapply N3. auto.
    exploit set_footprint_incl; eauto. intros [?|?]; auto. simpl in H3.
    contradiction.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto.
    econstructor. eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply H0. eapply in_app_iff. right.
    eapply in_app_iff. right. eapply in_app_iff. left.
    eapply get_footprint_incl; eauto. simpl. eauto.
    (* flat_footprint_separated *)
    red. intros. intro. apply H. simpl in H0.
    erewrite !in_app. erewrite !in_app in H0.
    repeat destruct H0; auto.
    right. right. left.
    eapply set_footprint_incl in H0; eauto. destruct H0; auto.
    simpl in H0. contradiction.
    (* sound_drop_place_state *)
    econstructor; eauto.
    (* wt_state *)
    admit.
  (* step_dropplace_struct *)
(*   - inv SOUND. *)
(*     inv DP. *)
(*     (* easy: movable is owned *) *)
(*     assert (POWN: is_owned own p = true) by admit. *)
(*     (* show that (b,ofs) is sem_wt of Tstruct and prove the soundness *) *)
(* (*     of members *) *)
(*     exploit eval_place_sound. 1-3: eauto. *)
(*     (** TODO: how to show p is syntactic well typed?  *) *)
(*     admit. *)
(*     eapply wf_own_dominator. auto. *)
(*     auto. *)
(*     intros (pfp & PFP). *)
(*     exploit movable_place_sem_wt; eauto. *)
(*     rewrite PTY. intros WT. *)
(*     (* prove sound_state *) *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (** TODO: use sem_wt_loc to prove member_footprint *) *)
(*     admit. *)
(*     (* sound_cont *) *)
(*     instantiate (1 := fpf_func le fpm fpf). *)
(*     econstructor. *)
(*     (** TODO: shrinking the own_env preserves mmatch *) *)
(*     admit. *)
(*     auto. *)
(*     (** TODO: sound_drop_place *) *)
(*     inv SOUND. *)
(*     econstructor. auto. *)
(*     (* show that move out p does not change the ownership of l *) *)
(*     admit. *)
(*     (* use SEP to prove this goal *) *)
(*     admit. *)
(*     inv SEP. auto. *)
(*     (* property of wf_own_env *) *)
(*     admit. *)
(*     (* norepet *) *)
(*     admit. *)
(*     (* accessibility *) *)
(*     admit. *)
(*   (* step_dropplace_struct *) *)
(*   - admit. *)
(*   (* step_dropplace_next *) *)
(*   - inv SOUND. inv DP. *)
(*     econstructor; eauto. *)
(*     econstructor. auto. *)
(*   (* step_dropplace_return *) *)
(*   - inv SOUND. *)
(*     econstructor; eauto. *)
Admitted.

Lemma norepet_fpf_func_internal1: forall le fpm fpf,
    list_norepet (flat_fp_frame (fpf_func le fpm fpf)) ->
    list_norepet (flat_fp_map fpm).
Admitted.

Lemma norepet_fpf_func_internal2: forall le fpm fpf,
    list_norepet (flat_fp_frame (fpf_func le fpm fpf)) ->
    list_norepet (flat_fp_frame fpf).
Admitted.

Lemma flat_fp_frame_func1: forall le fpm fpf ty b id,
    list_norepet (flat_fp_frame (fpf_func le fpm fpf)) ->
    le ! id = Some (b, ty) ->
    ~ In b (flat_fp_map fpm) /\ ~ In b (flat_fp_frame fpf).
Admitted.

Lemma flat_fp_frame_func2: forall le fpm fpf fp id,
    list_norepet (flat_fp_frame (fpf_func le fpm fpf)) ->
    fpm ! id = Some fp ->
    list_disjoint (footprint_flat fp) (footprint_of_env le)
    /\ list_disjoint (footprint_flat fp) (flat_fp_frame fpf).
Admitted.

(* To prove the norepet of footprint frame when only the footprint
    map is changed *)
Lemma fp_frame_norepet_internal: forall le fpm1 fpm2 fpf,
    list_norepet (flat_fp_frame (fpf_func le fpm1 fpf)) ->
    incl (flat_fp_map fpm2) (flat_fp_map fpm1) ->
    list_norepet (flat_fp_map fpm2) ->
    list_norepet (flat_fp_frame (fpf_func le fpm2 fpf)).
Proof.
  intros until fpf. intros A1 A2 A3.
  simpl in *. apply list_norepet_append_commut2.
  apply list_norepet_append_commut2 in A1.
  rewrite app_assoc in *.
  apply list_norepet_app in A1. destruct A1 as (N1 & N2 & N3).
  apply list_norepet_app. repeat apply conj; auto.
  red. intros. intro. subst. eapply N3. eauto.
  eapply A2. eauto. auto.
Qed.

(* frame rule of rsw_acc *)
(* Lemma rsw_acc_frame: forall m1 m2 fp1 fp1' fp2 fp2' fp1'' fp2'' sg, *)
(*     rsw_acc (rsw sg fp1 m1) (rsw sg fp2 m2) -> *)
(*     (* separation conjunction *) *)
(*     list_disjoint fp1 fp1' -> *)
(*     list_disjoint fp2 fp2' -> *)
(*     (* fp1 * fp1' = fp1'' *) *)
(*     list_equiv (fp1 ++ fp1') fp1'' -> *)
(*     list_equiv (fp1 ++ fp1') fp2'' -> *)
(*     rsw_acc (rsw sg fp1'' m1) (rsw sg fp2'' m2). *)
(* Admitted. *)

(* Some frame update of rsw_acc *)
Lemma rsw_acc_app: forall l l1 l2 m1 m2 sg,
    rsw_acc (rsw sg l1 m1) (rsw sg l2 m2) ->
    rsw_acc (rsw sg (l1 ++ l) m1) (rsw sg (l2 ++ l) m2).
Proof.
  intros. inv H. econstructor.
  eapply Mem.unchanged_on_implies; eauto.
  intros. simpl. intro. eapply H. eapply in_app; eauto.
  red. intros. intro. eapply SEP; eauto.
  intro. eapply H. eapply in_app; eauto.
  eapply in_app in H0. destruct H0; auto.
  exfalso. eapply H. eapply in_app; auto.
Qed.

  
(* More generally, rsw_acc is preserved under permuation of the
      footprint *)
Lemma rsw_acc_commut: forall l1 l2 l sg m1 m2,
    rsw_acc (rsw sg (l1 ++ l) m1) (rsw sg (l2 ++ l) m2) ->
    rsw_acc (rsw sg (l ++ l1) m1) (rsw sg (l ++ l2) m2).
Admitted.


Lemma in_flat_fp_map: forall b fp fpm id,
    fpm ! id = Some fp ->
    In b (footprint_flat fp) ->
    In b (flat_fp_map fpm).
Admitted.

    
(* If the footprint shrinks, the flat_footprint_separated is
    satisfied trivially *)
Lemma flat_footprint_separated_shrink: forall l1 l2 m,
    incl l2 l1 ->
    flat_footprint_separated l1 l2 m. 
Proof.
  intros. red. intros. intro. eapply H0. auto.
Qed.

Lemma list_equiv_norepet {A: Type}: forall (l1 l2 l3 l4: list A),
    list_norepet (l1 ++ l2) ->
    list_equiv (l1 ++ l2) l3 ->
    list_norepet (l4 ++ l3) ->
    list_norepet (l4 ++ l1)
    /\ list_norepet (l4 ++ l2)
    /\ list_disjoint l1 (l4 ++ l2).
Proof.
  intros. eapply list_norepet_app in H as (A1 & A2 & A3).
  eapply list_norepet_app in H1 as (B1 & B2 & B3).
  repeat apply conj.
  - eapply list_norepet_app.
    repeat apply conj; auto.
    red. intros. eapply B3. auto.
    eapply H0. eapply in_app; auto. 
  - eapply list_norepet_app.
    repeat apply conj; auto.
    red. intros. eapply B3. auto.
    eapply H0. eapply in_app; auto.
  - red. intros. eapply in_app in H1. destruct H1.
    + eapply list_disjoint_sym in B3. eapply B3; auto.
      eapply H0. eapply in_app; auto.
    + eapply A3; auto.
Qed.
    
Ltac simpl_getIM IM :=
  generalize IM as IM1; intros;
  inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst;
  try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *.


(* sound state and syntactic well-typed state is preserved in one
step *)
Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    wt_state ce s1 ->
    Step L s1 t s2 ->
    sound_state s2 /\ wt_state ce s2.
Proof.
  intros s1 t s2 SOUND WTST STEP. simpl in STEP.
  inv STEP.
  (* assign sound *)
  - inv SOUND. inv STMT. simpl in TR.    
    simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (WTVAL2 & WTFP2).
    exploit eval_place_sound; eauto.
    (** sound_own after moving the place in the expression *)
    destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
    eapply move_place_sound. auto.     
    intros (pfp & GFP & WTFP3).
    exploit (@list_equiv_norepet block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit assign_loc_sound; eauto.
    intros (fpm3 & SFP & MM3 & NOREP3 & WFENV3).        
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    instantiate (1 := (init_place (move_place_option own1 (moved_place e)) p)).
    exploit move_option_place_sound; eauto.
    instantiate (1 := (moved_place e)). intros SOUND1.
    exploit init_place_sound; eauto.
    intros (mayinit3 & mayuninit3 & A & B).
    (* end of construct *)
    split.
    (* sound_state *)
    (* key proof: figure out which location the changed block resides
    in. The changed block is in the stack or in the footprint map
    (maybe we can prove this using get_loc_footprint_map_in_range *)
    assert (RAN: In b (footprint_of_env le ++ flat_fp_map fpm2)).
    { destruct (path_of_place p) eqn: POP. simpl in GFP.
      destruct (le ! i) eqn: LOC; try congruence. destruct p0.
      destruct (fpm2 ! i) eqn: GFP1; try congruence.
      exploit wf_env_footprint. eapply WFENV1. eauto.
      intros (fp & A1 & A2). rewrite GFP1 in A1. inv A1.
      exploit get_loc_footprint_in_range. 5: eapply GFP. eauto.
      eapply wt_place_wt_path; eauto.
      (* prove b0 not in fp *)
      eapply list_norepet_app in N7. destruct N7 as (N9 & N10 & N11).
      intro. eapply N11. eapply in_footprint_of_env; eauto.
      eapply in_footprint_flat_fp_map; eauto. auto.
      (* norepet of fp *)
      eapply list_norepet_app in N7. destruct N7 as (N9 & N10 & N11).
      eapply norepet_flat_fp_map_element; eauto.
      intros [(B1 & B2 & B3) | (B1 & B2)]; subst.
      (* case1: b is in the stack (i.e., in the le) *)
      eapply in_app. left. eapply in_footprint_of_env; eauto.    
      (* case2: b is in abstract value (i.e., in the heap) *)
      eapply in_app. right. eapply in_flat_fp_map; eauto. }
    assert (RAN1: In b (footprint_of_env le ++ flat_fp_map fpm)).
    { eapply in_app in RAN. apply in_app. destruct RAN; auto.
      right. eapply EQUIV1. eapply in_app; eauto. }
    econstructor; eauto.
    econstructor.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    (* to prove sound_cont: unchanged on the footprint of the frames
    of the function *)
    exploit assign_loc_unchanged_on; eauto.
    intros UNC1. eapply Mem.unchanged_on_implies. eauto.
    simpl. intros. intro. destruct H5. subst.
    (* show that block in le++fpm is not in fpf *)
    eapply DIS1. eauto. eauto. auto. 
    (* end of the proof of sound_cont *)
    (* norepet *)
    eapply fp_frame_norepet_internal. eauto.
    destruct (path_of_place p) eqn: POP.
    red. intros. eapply set_footprint_map_incl in H3; eauto.
    eapply EQUIV1. eapply in_app. intuition.
    eapply list_norepet_app. eauto.
    (* accessibility *)
    instantiate (1:= sg).
    eapply rsw_acc_trans. eauto.
    (** TODO: how to prove rsw_acc more generally? *)
    simpl. do 2 rewrite app_assoc.
    eapply rsw_acc_app. 
    econstructor.
    exploit assign_loc_unchanged_on; eauto.
    intros UNC1. eapply Mem.unchanged_on_implies. eauto.
    simpl. intros. intro. destruct H5. subst.
    apply H3. 
    destruct (path_of_place p) eqn: POP. simpl in GFP. auto.
    (* flat_footprint_separate: easy because support is unchanged *)
    eapply flat_footprint_separated_shrink.
    red. intros. apply in_app in H3; apply in_app; destruct H3; auto.
    right. apply EQUIV1.
    destruct (path_of_place p) eqn: POP.
    eapply set_footprint_map_incl in H3; eauto. apply in_app. destruct H3; auto.
    (* end of rsw_acc *)
    (* wf_own_env preservation (write it in another lemma) *)
    admit.
    (* wt_state *)
    admit.
    
Admitted.

  (* (* assign_variant sound *) *)
  (* - admit. *)
  (* (* step_box sound *) *)
  (* - admit. *)
  (* (** NOTEASY: step_to_dropplace sound *) *)
  (* - inv SOUND. inv STMT. *)


    
  (*   exploit split_drop_place_sound; eauto. *)
  (*   intros SOUNDSPLIT. *)
  (*   econstructor; eauto. *)
  (*   econstructor. auto. *)
  (* (* step_in_dropplace sound *) *)
  (* - eapply step_dropplace_sound; eauto. *)
  (* (* step_dropstate sound *) *)
  (* - eapply step_drop_sound; eauto. *)
  (* (* step_storagelive sound *) *)
  (* - admit. *)
  (* (* step_storagedead sound *) *)
  (* - admit. *)
  (* (* step_call sound *) *)
  (* - inv SOUND. *)
  (*   exploit eval_exprlist_sem_wt; eauto. *)
  (*   intros (fpl & fpm2 & WT & MM2). *)
  (*   econstructor. 1-3: eauto. *)
  (*   (* sound_cont *) *)
  (*   instantiate (1 := fpf_func le fpm2 fpf). *)
  (*   econstructor. eauto. auto. *)
  (*   (* wf_own_env *) *)
  (*   admit. *)
  (*   eauto. *)
  (*   (* norepeat *) *)
  (*   admit. *)
  (*   (* accessibility *) *)
  (*   instantiate (1 := sg). *)
  (*   admit. *)
  (* (* step_internal_function sound *) *)
  (* - inv SOUND. *)
  (*   exploit function_entry_sound; eauto. *)
  (*   intros (fpm & MM & WFOWN). *)
  (*   econstructor; eauto. *)
  (*   (* prove sound_cont *) *)
  (*   instantiate (1 := fpf). *)
  (*   eapply sound_cont_unchanged; eauto. *)
  (*   (* prove unchanged_on of function_entry *) *)
  (*   admit. *)
  (*   (* new allocated blocks are disjoint with the frames *) *)
  (*   admit. *)
  (*   instantiate (1 := sg). *)
  (*   (* accessibility *) *)
  (*   admit. *)
    
(* (* Admitted. *) *)

(* Lemma reachable_state_sound: forall s, *)
(*     (* What about after external? *) *)
(*     reachable L s -> sound_state s. *)
(* Admitted. *)

Lemma external_sound: forall s q,
    sound_state s ->
    wt_state ge s ->
    at_external ge s q ->
    exists wA, symtbl_inv wt_rs wA se /\ query_inv wt_rs wA q /\
            forall r, reply_inv wt_rs wA r ->
                 (exists s', after_external s r s' (* do we really need
                 this exists s'? It is repeated in partial safe *)
                        /\ forall s', after_external s r s' -> sound_state s' /\ wt_state ge s').
Admitted.

Lemma final_sound: forall s r,
    sound_state s ->
    wt_state ge s ->
    final_state s r ->
    reply_inv wt_rs (se, w) r.
Admitted.

End MOVE_CHECK.

(** Specific definition of partial safe *)
(* Definition partial_safe ge (L: lts li_rs li_rs state) (s: state) : Prop := *)
(*   not_stuck L s \/ step_mem_error ge s. *)

Definition mem_error prog se (L: lts li_rs li_rs state) (s: state) : Prop :=
  step_mem_error (globalenv se prog) s.

(* I is the generic partial safe invariant *)
Lemma move_check_module_safe (I: invariant li_rs) p:
  module_type_safe (semantics p) I I (mem_error p) ->  
  (* Genv.valid_for (erase_program (program_of_program p)) se ->  *)
  move_check_program p = OK p ->
  module_type_safe (semantics p) (inv_compose I wt_rs) (inv_compose I wt_rs) SIF.
  (* module_safe_se (semantics p) (inv_compose I wt_rs) (inv_compose I wt_rs) not_stuck se. *)
Proof.
  intros [SAFE] MVCHK. destruct SAFE as (SINV & PRE).
  (* w1 is the world in partial safe *)
  set (IS := fun se1 '(w1, (se2, w2)) s =>
               SINV se1 w1 s
               /\ sound_state p w2 se2 s
               /\ wt_state p.(prog_comp_env) s
               /\ se1 = se2).
  red. constructor.
  eapply (Module_ksafe_components li_rs li_rs (semantics p) (inv_compose I wt_rs) (inv_compose I wt_rs) SIF IS).
  intros se (w1 & (se' & w2)) (SYMINV1 & SYMINV2) VSE. simpl in SYMINV2. subst.
  simpl in VSE.
  generalize (PRE se w1 SYMINV1 VSE). intros PRE1.
  econstructor.
  (* internal_step_preserves *)
  - intros s t s' (SINV1 & SOUND & WTST & SE) STEP.
    simpl. repeat apply conj; auto.
    + eapply internal_step_preserves; eauto.
    + eapply step_sound; eauto.
    + eapply step_sound; eauto.
  (* internal_state_progress *)
  - intros s (SINV1 & SOUND & WTST & SE).
    exploit @internal_state_progress; eauto. intros [A|B].
    auto.
    (* memory error is impossible in sound_state*)
    admit.
  (* initial_preserves_progress *)
  - intros q VQ (QINV1 & QINV2).
    (** partial safe also allow initial_state???? *)
    exploit @initial_preserves_progress; eauto.
    intros (s & INIT & SINV1).
    exists s. split; auto.
    intros s' INIT'.
    red. exploit initial_state_sound; eauto.
    intros (SOUND & WT).
    repeat apply conj; auto.
  (* external_preserves_progress *)
  - intros s q (SINV1 & SOUND & WTST & SE) ATEXT.
    exploit @external_preserves_progress; eauto.
    intros (wI & SYM1 & QINV1 & AFEXT1).    
    exploit external_sound; eauto.
    intros ((wrs & se') & SYM2 & QINV2 & AFEXT2).
    exists (wI, (wrs, se')). repeat apply conj; auto.
    (* after external *)
    intros r (RINV1 & RINV2).
    exploit AFEXT1; eauto.
    intros (s' & AFST & AF).
    exists s'. split; auto.
    intros s'' AFST'.
    exploit AFEXT2; eauto. intros (s''' & AFST'' & AF').
    red.  simpl in AF'. repeat apply conj; auto.
    eapply AF'. eauto. eapply AF'. eauto.
  (* final_state_preserves *)
  - intros s r (SINV1 & SOUND & WTST & SE) FINAL.
    exploit @final_state_preserves; eauto.
    intros RINV1.
    exploit @final_sound; eauto. intros RINV2.
    econstructor; eauto.
Admitted.

    
(*   (* preservation *) *)
(*   - intros (w1 & w2) (SINV1 & SINV2).  *)
(*     exploit PSAFE; eauto. intros PLSAFE. *)
(*     constructor. *)
(*     (* preserve step *) *)
(*     + intros s t s' (REACH & PS & SOUND) STEP. *)
(*       red. repeat apply conj. *)
(*       * eapply step_reachable; eauto. *)
(*       * eapply reachable_safe; eauto. *)
(*         eapply step_reachable; eauto. *)
(*       (* step sound_state *) *)
(*       * eapply step_sound; eauto.         *)
(*     (* initial *) *)
(*     + intros q s VQ (QINV1 & QINV2) INIT. *)
(*       red. repeat apply conj. *)
(*       * eapply initial_reach; eauto. *)
(*         eapply star_refl. *)
(*       * eapply reachable_safe; eauto. *)
(*         eapply initial_reach; eauto. *)
(*         eapply star_refl. *)
(*       (* initial sound state *) *)
(*       * eapply initial_state_sound; eauto. *)
(*     (* external preserve *) *)
(*     + intros s s' q r (w1' & w2') (REACH & PS & SOUND) ATEXT (QINV1 & QINV2) (RINV1 & RINV2) AFEXT. *)
(*       red. repeat apply conj. *)
(*       * eapply external_reach; eauto. *)
(*         eapply star_refl. *)
(*       * eapply reachable_safe; eauto. *)
(*         eapply external_reach; eauto. *)
(*         eapply star_refl. *)
(*       (** external sound state: may be very difficult!!! *) *)
(*       * eapply external_sound_preserve; eauto. *)
(*   (* progress *) *)
(*   - intros (w1 & w2) (SINV1 & SINV2).  *)
(*     exploit PSAFE; eauto. intros PLSAFE. *)
(*     constructor. *)
(*     (* sound_state progress *) *)
(*     + intros s (REACH & PS & SOUND). *)
(*       unfold partial_safe in PS. destruct PS; auto. *)
(*       (** proof of no memory error in sound state *) *)
(*       admit. *)
(*     (* initial_progress *) *)
(*     + intros q VQ (QINV1 & QINV2). *)
(*       eapply initial_progress; eauto. *)
(*     (* external_progress *) *)
(*     + intros s q (REACH & PS & SOUND) ATEXT. *)
(*       exploit (@external_progress li_rs); eauto. *)
(*       intros (w1' & SINV1' & QINV1' & RINV1). *)
(*       (** To construct wA: prove sound_state external progress *) *)
(*       exploit external_sound_progress; eauto. *)
(*       intros (w2' & SINV2' & QINV2' & RINV2'). *)
(*       exists (w1',w2'). repeat apply conj; eauto. *)
(*       intros r (RINV1'' & RINV2''). *)
(*       eapply RINV2'. auto.             *)
(*     (* final_progress *) *)
(*     + intros s r (REACH & PS & SOUND) FINAL. *)
(*       exploit (@final_progress li_rs); eauto. *)
(*       intros RINV1. *)
(*       (** final_progress of sound_state  *) *)
(*       exploit final_sound_progress; eauto. *)
(*       intros RINV2. constructor; auto.       *)
(* Admitted. *)

Definition wt_rs_inv p '(se, w) := sound_state p (se, w) se.

Lemma sound_rustir_preserves p:
  move_check_program p = OK p ->
  preserves (semantics p) wt_rs wt_rs (wt_rs_inv p).
Proof.
  intros.
  assert (CE: forall se, composite_env_consistent (globalenv se p)).
  { intros. eapply build_composite_env_consistent.
    instantiate (1 := (prog_types p)). destruct p; simpl; eauto. }
  constructor; intros; destruct w; simpl in *; subst.
  - eapply step_sound; eauto.
    constructor.
  - eapply initial_state_sound; eauto.
    constructor.
    auto.
  - exploit external_sound_progress; eauto.
    constructor.
    intros (wA & SINV & QINV & RINV).
    exists wA. repeat apply conj; auto.
    intros. eapply external_sound_preserve; eauto.
    constructor.
  - exploit final_sound_progress; eauto.
    constructor.
Qed.

Lemma sound_rustir_self_sim p:
  move_check_program p = OK p ->
  forward_simulation wt_rs wt_rs (semantics p) (semantics p).
Proof.
  intros.
  eapply preserves_fsim with (IS := wt_rs_inv p).
  eapply sound_rustir_preserves.
  auto.
Qed.
