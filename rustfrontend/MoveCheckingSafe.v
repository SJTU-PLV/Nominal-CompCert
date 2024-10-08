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

Inductive wt_expr: expr -> Prop :=
| wt_move_place: forall p
    (WT1: wt_place p)
    (SCALAR: scalar_type (typeof_place p) = false),
    wt_expr (Emoveplace p (typeof_place p)).
(** TODO: wt_pexpr  *)


End TYPING.

Coercion env_to_tenv (e: env) : typenv :=
  PTree.map1 snd e.


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


(** Test: try to define semantics well-typedness for a memory location *)

(* A tree structured footprint (maybe similar to some separation logic
algebra) *)
Inductive footprint : Type :=
| fp_emp                        (* empty footprint *)
| fp_box (b: block) (sz: Z) (fp: footprint) (* A heap block storing values that occupy footprint fp *)
(* (field ident, field type, field offset,field footprint) *)
| fp_struct (id: ident) (fpl: list (ident * type * Z * footprint))
| fp_enum (id: ident) (tag: Z) (fid: ident) (fty: type) (ofs: Z) (fp: footprint)
.
(* with field_footprint : Type := *)
(* | fp_field (fid: ident) (fty: type) (ofs: Z) (fp: footprint). *)

Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPbox: forall (b : block) sz (fp : footprint), P fp -> P (fp_box b sz fp))
  (HPstruct: forall id fpl, (forall fid fty ofs fp, In (fid, fty, ofs, fp) fpl -> P fp) -> P (fp_struct id fpl))
  (HPenum: forall id (tag : Z) fid fty ofs (fp : footprint), P fp -> P (fp_enum id tag fid fty ofs fp)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as (((fid1 & fty1) & ofs1) & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid fty ofs fp H). 
  - apply HPenum. apply strong_footprint_ind.
Qed.
    
End FP_IND.

(* Try to define new sem_wt *)

Definition find_fields (fid: ident) (fpl: list (ident * type * Z * footprint)) : option (ident * type * Z * footprint) :=
  find (fun '(fid', _, _, _) => if ident_eq fid fid' then true else false) fpl. 

Lemma find_fields_some: forall fid fid1 fpl fty fofs ffp,
    find_fields fid fpl = Some (fid1, fty, fofs, ffp) ->
    fid = fid1 /\ In (fid, fty, fofs, ffp) fpl.
Proof.
  intros. unfold find_fields in H.
  exploit find_some; eauto. intros (A & B).
  destruct ident_eq in B; try congruence.
  subst. auto.
Qed.


(* Semantics well typed location is mutually defined with semantics
well typed value *)
Inductive sem_wt_loc (m: mem) : footprint -> block -> Z -> type -> Prop :=
| sem_wt_base: forall ty b ofs fp chunk v
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val m fp v ty),
    sem_wt_loc m fp b ofs ty
| sem_wt_struct: forall b ofs fpl orgs id
    (* all fields are semantically well typed *)
    (FWT: forall fid fty fofs ffp,
        find_fields fid fpl = Some (fid, fty, fofs, ffp) ->
        sem_wt_loc m ffp b (ofs + fofs) fty),
    sem_wt_loc m (fp_struct id fpl) b ofs (Tstruct orgs id)
| sem_wt_enum: forall fp b ofs orgs id tagz fid fty fofs
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc m fp b (ofs + fofs) fty),
    sem_wt_loc m (fp_enum id tagz fid fty fofs fp) b ofs (Tvariant orgs id)

with sem_wt_val (m: mem) : footprint -> val -> type -> Prop :=
| wt_val_unit:
  sem_wt_val m fp_emp (Vint Int.zero) Tunit
| wt_val_int: forall sz si n,
    Cop.cast_int_int sz si n = n ->
    sem_wt_val m fp_emp (Vint n) (Tint sz si)
| wt_val_float: forall n,
    sem_wt_val m fp_emp (Vfloat n) (Tfloat Ctypes.F64)
| wt_val_single: forall n,
    sem_wt_val m fp_emp (Vsingle n) (Tfloat Ctypes.F32)
| wt_val_long: forall si n,
    sem_wt_val m fp_emp (Vlong n) (Tlong si)
| wt_val_box: forall b ty fp sz
    (** Box pointer must be in the starting point of a block *)
    (* The value stored in (b,0) has type ty and occupies footprint fp *)
    (WTLOC: sem_wt_loc m fp b 0 ty)
    (VALID: Mem.range_perm m b (- size_chunk Mptr) sz Cur Freeable),
    sem_wt_val m (fp_box b sz fp) (Vptr b Ptrofs.zero) (Tbox ty)
(* TODO *)
(* | wt_val_ref: forall b ofs ty org mut, *)
(*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *)
| wt_val_struct: forall id orgs b ofs fp
    (WTLOC: sem_wt_loc m fp b (Ptrofs.unsigned ofs) (Tstruct orgs id)),
    sem_wt_val m fp (Vptr b ofs) (Tstruct orgs id)
| wt_val_enum: forall id orgs b ofs fp
    (WTLOC: sem_wt_loc m fp b (Ptrofs.unsigned ofs) (Tvariant orgs id)),
    sem_wt_val m fp (Vptr b ofs) (Tvariant orgs id)
.

  
Section COMP_ENV.

Variable ce: composite_env.

Definition member_footprint_rel (wtfp: type -> footprint -> Prop) (co: composite) (memb: member) (f: ident * type * Z * footprint) : Prop :=
  let '(fid, fty, fofs, fp) := f in
  match memb with
  | Member_plain fid1 fty1 => fid = fid1 /\ fty = fty1
                             /\ field_type fid co.(co_members) = OK fty
                             /\ field_offset ce fid co.(co_members) = OK fofs
                             /\ wtfp fty fp
  end.


(* Try to define wt_footprint *)

Inductive wt_footprint : composite_env -> type -> footprint -> Prop :=
| wt_fp_emp: forall ce1 ty,
    (* It means that the location with this type is not
        initialized or this location is scalar type *)
    (forall orgs id, ty <> Tstruct orgs id) ->
    wt_footprint ce1 ty fp_emp
| wt_fp_struct: forall orgs id fpl ce1 co
    (CO: ce1 ! id = Some co)
    (** TODO: combine WT1 and WT2 elegantly  *)
    (WT1: forall fid fty fofs,
        field_type fid co.(co_members) = OK fty ->
        field_offset ce fid co.(co_members) = OK fofs ->
        (* For simplicity, use find_field instead of In predicate *)
        exists ffp, find_fields fid fpl = Some (fid, fty, fofs, ffp)
               (* bound condition *)
               /\ wt_footprint (PTree.remove id ce1) fty ffp)
    (WT2: forall fid fty fofs ffp,
        find_fields fid fpl = Some (fid, fty, fofs, ffp) ->
        field_type fid co.(co_members) = OK fty
        /\ field_offset ce fid co.(co_members) = OK fofs
        /\ wt_footprint (PTree.remove id ce1) fty ffp),
    wt_footprint ce1 (Tstruct orgs id) (fp_struct id fpl)
| wt_fp_enum: forall orgs id tagz fid fty fofs fp ce1 co
    (CO: ce1 ! id = Some co)
    (TAG: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty))
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: wt_footprint ce fty fp),
    wt_footprint ce1 (Tvariant orgs id) (fp_enum id tagz fid fty fofs fp)
| wt_fp_box: forall ty b fp ce1
    (* this is ensured by bm_box *)
    (WT: wt_footprint ce1 ty fp),
    wt_footprint ce1 (Tbox ty) (fp_box b (sizeof ce ty) fp).

End COMP_ENV.

Inductive bmatch (m: mem) (b: block) (ofs: Z) : footprint -> type -> Prop :=
| bm_box: forall ty b1 fp sz
    (LOAD: Mem.load Mptr m b ofs = Some (Vptr b1 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b1 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (VRES: Mem.range_perm m b1 (- size_chunk Mptr) sz Cur Freeable),
    bmatch m b ofs (fp_box b1 sz fp) (Tbox ty)
| bm_struct: forall fpl orgs id
    (* all fields are semantically well typed *)
    (FMATCH: forall fid fty fofs ffp,
        find_fields fid fpl = Some (fid, fty, fofs, ffp) ->
        bmatch m b (ofs + fofs) ffp fty),
    bmatch m b ofs (fp_struct id fpl) (Tstruct orgs id)
| bm_enum: forall fp orgs id tagz fid fty fofs
    (* Interpret the field by the tag and prove that it is well-typed *)
    (* [p] whose value has footprint (fp_enum tagz fp) is actually has
    tag tagz *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz))) 
    (BM: bmatch m b (ofs + fofs) fp fty),
    bmatch m b ofs (fp_enum id tagz fid fty fofs fp) (Tvariant orgs id)
| bm_scalar: forall ty chunk v
    (TY: scalar_type ty = true)
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val m fp_emp v ty),
    bmatch m b ofs fp_emp ty
(** TODO: bm_reference  *)
.

Definition fp_map := PTree.t footprint.

(* Getter and Setter of footprint map  *)

(* Similar to ProjectElem in rustc *)
Variant path : Type :=
  | ph_deref
  | ph_field (fid: ident)
  (* type of the variant here is used in valid_owner proof !! *)
  | ph_downcast (ty: type) (fid: ident) (fty: type).

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
      (id, phl ++ [ph_downcast (typeof_place p1) fid fty])
  end.

Inductive paths_disjoint : list path -> list path -> Prop :=
| phs_disjoint1: forall p1 p2 l1 l2,
    (* Is it enough to use neq? *)
    p1 <> p2 ->
    paths_disjoint (p1::l1) (p2::l2)
| phs_disjoint2: forall p l1 l2,
    paths_disjoint l1 l2 ->
    paths_disjoint (p::l1) (p::l2).

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
            | Some (fid1, fty, fofs, ffp) =>                
                match set_footprint l v ffp with
                | Some ffp1 =>
                    Some (fp_struct id (map (fun '(fid2, fty2, fofs2, ffp2) => if ident_eq fid fid2 then (fid2, fty2, fofs2, ffp1) else (fid2, fty2, fofs2, ffp2)) fpl)) 
                | None => None
                end
            | None => None
            end
        | ph_downcast pty fid fty, fp_enum id tagz fid1 fty1 fofs1 fp1 =>
            match pty with
            | Tvariant _ id1 =>
                if ident_eq id1 id then
                  if ident_eq fid fid1 && type_eq fty fty1 then
                    match set_footprint l v fp1 with
                    | Some fp2 =>
                        Some (fp_enum id tagz fid1 fty1 fofs1 fp2)
                    | None => None
                    end
                  else None
                else None
            | _ => None
            end
        | _, _ => None
        end
  end.

Fixpoint clear_footprint_rec (fp: footprint) : footprint :=
  match fp with
  | fp_box _ _ _
  | fp_enum _ _ _ _ _ _
  | fp_emp => fp_emp
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, fty, fofs, ffp) => (fid, fty, fofs, clear_footprint_rec ffp)) fpl)
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
          | Some (_, _, fofs, fp1) =>
              get_loc_footprint l fp1 b (ofs + fofs)
          | None => None
          end
      | ph_downcast pty fid1 fty1, fp_enum id _ fid2 fty2 fofs fp1 =>
          match pty with
          | Tvariant _ id1 =>
              if ident_eq id1 id then     
                if ident_eq fid1 fid2 && type_eq fty1 fty2 then
                  get_loc_footprint l fp1 b (ofs + fofs)
                else
                  None
              else None
          | _ => None
          end
      | _, _  => None
      end
  end.

Fixpoint get_footprint (phl: list path) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some fp
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_footprint l fp1
      | ph_field fid, fp_struct _ fpl =>
          match find_fields fid fpl with
          | Some (_, _, fofs, fp1) =>
              get_footprint l fp1
          | None => None
          end
      | ph_downcast pty fid1 fty1, fp_enum id _ fid2 fty2 fofs fp1 =>
          match pty with
          | Tvariant _ id1 =>
              if ident_eq id1 id then                
                if ident_eq fid1 fid2 && type_eq fty1 fty2 then
                  get_footprint l fp1
                else
                  None
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
      destruct ident_eq in H0; simpl in H0; try congruence. subst.
      destruct type_eq in H0; simpl in H0; try congruence. subst.
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. destruct ident_eq; simpl; try congruence.
      destruct ident_eq; simpl; try congruence.
      destruct type_eq; simpl; try congruence.
      eauto. auto.
Qed.

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


(** IMPORTANT TODO: how to perform induction???  *)
Lemma set_footprint_map_app_inv: forall phl2 phl1 id fpm1 fpm2 fp1 fp2 b1 ofs1 le,
    get_loc_footprint_map le (id, phl1++phl2) fpm1 = Some (b1, ofs1, fp1) ->
    set_footprint_map (id, phl1++phl2) fp2 fpm1 = Some fpm2 ->
    exists b2 ofs2 fp3 fp4,
      get_loc_footprint_map le (id, phl1) fpm1 = Some (b2, ofs2, fp3)
      /\ get_loc_footprint_map le (id, phl1) fpm2 = Some (b2, ofs2, fp4)
      /\ set_footprint phl2 fp2 fp3 = Some fp4.
(* Proof. *)
(*   induction phl1; intros. *)
(*   - (* rewrite app_nil_r in *. exists b1, ofs1, fp1, fp2. *) *)
(*     (* repeat apply conj; auto. *) *)
(*   (* eapply get_set_footprint_map; eauto.  *) *)
(*     admit. *)
(*   - replace (a::phl1) with ((a::nil) ++ phl1) in * by auto. *)
(*     rewrite <- app_assoc in *.             *)
(*     exploit get_loc_footprint_map_app_inv; eauto. *)
(*     intros (b3 & ofs3 & fp5 & D & E). *)
(*     simpl in H0. destruct (fpm1 ! id) eqn: FP1; try congruence. *)
(*     destruct a. *)
(*     + destruct f; try congruence. *)
(*       destruct (set_footprint (phl1 ++ phl2) fp2 f) eqn: SET; try congruence. *)
(*       assert (SET1: set_footprint_map (id, phl1++phl2) (fp_box b sz f0) fpm1 = Some fpm2). *)
(*       { unfold set_footprint_map. rewrite FP1. rewrite  *)
      
      
    
(*     exploit get_loc_footprint_map_app_inv. eapply A. *)
(*     intros (b4 & ofs4 & fp6 & F & G). rewrite  *)
Admitted.

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

    
Section FPM.

Variable fpm : fp_map.

(* Inductive place_footprint (e: env) : place -> block -> Z -> footprint -> Prop := *)
(* | place_footprint_deref: forall p fp ofs1 b1 b2 ty sz *)
(*     (* (b1, ofs1) *-> (b2, 0) *) *)
(*     (FP: place_footprint e p b1 ofs1 (fp_box b2 sz fp)), *)
(*     (* For now, we do not consider reference, so the location of *p is *) *)
(* (*     always in the start of a block b2 *) *)
(*     place_footprint e (Pderef p ty) b2 0 fp *)
(* | place_footprint_field: forall p fp ofs b id fid fty fofs fpl orgs *)
(*     (FP: place_footprint e p b ofs (fp_struct id fpl)) *)
(*     (FIND: In (fid, fty, fofs, fp) fpl) *)
(*     (PTY: typeof_place p = Tstruct orgs id), *)
(*     place_footprint e (Pfield p fid fty) b (ofs + fofs) fp *)
(* | place_footprint_enum: forall p fp fid fty tagz b ofs id fofs orgs *)
(*     (FP: place_footprint e p b ofs (fp_enum id tagz fid fty fofs fp)) *)
(*     (PTY: typeof_place p = Tvariant orgs id), *)
(*     place_footprint e (Pdowncast p fid fty) b (ofs + fofs) fp *)
(* | place_footprint_local: forall id fp ty b *)
(*     (FP: fpm ! id = Some fp) *)
(*     (STK: e ! id = Some (b, ty)), *)
(*     place_footprint e (Plocal id ty) b 0 fp *)
(* . *)

(* (* Unable to prove because place_footprint contain some type checking  *) *)
(* Lemma get_loc_footprint_map_implies_place_footprint: forall p e ce b ofs fp, *)
(*     wt_place (env_to_tenv e) ce p -> *)
(*     get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) -> *)
(*     place_footprint e p b ofs fp. *)
(* Proof. *)
(*   induction p; simpl; intros. *)
(*   - destruct (e!i) eqn: A; try congruence. destruct p. *)
(*     destruct (fpm!i) eqn: B; try congruence. inv H. *)
(*     unfold env_to_tenv in WT1. *)
(*     erewrite PTree.gmap1 in WT1. rewrite A in WT1. inv WT1. inv H0. *)
(*     econstructor; auto. *)
(*   - inv H. *)
(*     destruct (path_of_place p) eqn: POP. *)
(*     exploit get_loc_footprint_map_app_inv; eauto. *)
(*     intros (b1 & ofs1 & fp1 & A & B). *)
(*     exploit IHp; eauto. intros PFP. *)
(*     simpl in B. destruct fp1; try congruence. *)
(*     destruct (find_fields i fpl) eqn: FIND. repeat destruct p0. *)
(*     inv B. econstructor; eauto. *)
(*     eapply find_some in FIND. destruct FIND.     *)
(* Admitted. *)
  
Definition mmatch (m: mem) (e: env) (own: own_env): Prop :=
  forall p b ofs fp,
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) ->
    is_init own p = true ->
    bmatch m b ofs fp (typeof_place p)
    /\ (is_full own.(own_universe) p = true ->
       sem_wt_loc m fp b ofs (typeof_place p)).


Record wf_env (ce: composite_env) (e: env): Prop := {
    wf_env_footprint: forall id b ty,
      e!id = Some (b, ty) ->
      (* Do we need to ensure the location is sem_wt? *)
      exists fp, fpm!id = Some fp
            /\ wt_footprint ce ce ty fp;
  }.

End FPM.

Definition ce_extends (env env': composite_env) : Prop := forall id co, env!id = Some co -> env'!id = Some co.

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
    (VOWN: valid_owner_offset_footprint p ofs (fp_enum id tagz fid fty fofs fp) fp1),
    valid_owner_offset_footprint (Pdowncast p fid fty) (ofs + fofs) fp fp1.

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
    destruct ident_eq in GET2; simpl in GET2; try congruence. subst.
    destruct type_eq in GET2; simpl in GET2; try congruence.
    inv GET2.
    do 3 eexists. repeat apply conj.
    eauto. econstructor; eauto.    lia.
    (* ??? use the fact that variant_field_offset is constant to prove *)
Qed.

Lemma valid_owner_bmatch: forall p m b ofs1 fofs1 fp1 fp,
    bmatch m b ofs1 fp1 (typeof_place (valid_owner p)) ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    bmatch m b (ofs1 + fofs1) fp (typeof_place p).
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  rewrite PTY in H0. inv H0.
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.

Lemma valid_owner_sem_wt_loc: forall p m b ofs1 fofs1 fp1 fp,
    sem_wt_loc m fp1 b ofs1 (typeof_place (valid_owner p)) ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    sem_wt_loc m fp b (ofs1 + fofs1) (typeof_place p).
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  rewrite PTY in H0. inv H0. simpl in *. try congruence. 
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.


(* The footprint contained in the location of a place *)
Lemma eval_place_sound: forall e m p b ofs own fpm init uninit universe
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch fpm m e own)
    (WFOWN: wf_env fpm ce e)
    (WT: wt_place (env_to_tenv e) ce p)
    (SOWN: sound_own own init uninit universe)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: dominators_must_init init uninit universe p = true),
  (* Do we need to specify the properties of fp? Do we need to show
  the permission of the location of p? *)
  exists fp ce' (* phl *), get_loc_footprint_map e (path_of_place p) fpm = Some (b, (Ptrofs.unsigned ofs), fp)
                      /\ wt_footprint ce ce' (typeof_place p) fp
                      /\ ce_extends ce' ce.
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
    exists fp, ce. repeat apply conj. simpl. rewrite H. rewrite FP. auto.
    simpl. auto.
    red. auto.
  (* Pfield *)
  - inv WT.
    (* two type facts, reduce one *)
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    (** TODO: make it a lemma: prove p's dominators are init *)
    assert (PDOM: dominators_must_init init uninit universe p = true) by admit.    
    exploit IHEVAL. 1-5: auto.
    intros (fp & ce' & PFP & WTFP & EXT).
    (* exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN). *)
    (** TODO: produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr.
    (** Inversion of WTFP *)
    rewrite H in WTFP. inv WTFP; try congruence.
    eapply EXT in CO. rewrite H0 in CO. inv CO.
    exploit WT0; eauto. intros (ffp & INFPL & WTFP1).
    exists ffp, (PTree.remove id0 ce'). repeat apply conj; auto.
    (* get_loc_footprint_map *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl.  rewrite INFPL. auto.        
    (** TODO: ce_extend trans and remove *)
    admit.
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
    intros (fp & ce' & PFP & WTFP & EXT).
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
    assert (BM1: bmatch m b (Ptrofs.unsigned ofs) fp (typeof_place p)).
    { rewrite OFSEQ. eapply valid_owner_bmatch. eauto. auto. }
    rewrite H in BM1. rewrite H in WTFP. inv BM1.
    (* rewrite some redundant premises *)
    simpl in H1. rewrite H1 in TAG. inv TAG. rewrite Int.unsigned_repr in H2.
    inv WTFP.
    (* do some rewrting *)
    eapply EXT in CO. rewrite H0 in CO. inv CO.
    rewrite H2 in TAG. inv TAG. simpl.
    rewrite H3 in FOFS. inv FOFS.
    exists fp0, ce. repeat apply conj.
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto. simpl.
    rewrite H. repeat destruct ident_eq; simpl; try congruence.
    destruct type_eq; simpl; try congruence. auto.    
    red. auto.
    2 : { simpl in *. congruence. }
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
    intros (fp & ce' & PFP & WTFP & EXT).
    exploit MM. eauto.
    eapply must_init_sound; eauto.
    intros (BM & FULL). destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2. inv BM.
    inv WTFP.
    exists fp0, ce'. repeat apply conj.    
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
    auto.
    simpl in *. congruence.
Admitted.

End COMP_ENV.

Lemma movable_place_sem_wt: forall ce ce1 fp fpm m e own p b ofs init uninit universe
    (MM: mmatch fpm m e own)    
    (* p owns the ownership chain *)    
    (POWN: must_movable ce1 init uninit universe p = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp))
    (WTFP: wt_footprint ce ce1 (typeof_place p) fp)
    (EXTEND: ce_extends ce1 ce),
    sem_wt_loc m fp b ofs (typeof_place p)
.
Proof.
  intros ce. intros c. pattern c. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold must_movable, must_movable_fix in *.
  erewrite unroll_Fix in *.
  destruct (typeof_place p) eqn: PTY; simpl in POWN; try congruence.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  (* Tbox *)
  - destruct (must_init init uninit universe p) eqn: INIT; try congruence.    
    (* adhoc generalization *)
    generalize dependent p. generalize dependent b.
    generalize dependent fp. generalize dependent ofs.
    induction t; intros; simpl in *; try congruence.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). rewrite PTY in *. inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p Tunit)) fpm = Some (b1, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). simpl in BM1. inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    (* The same as Tunit case *)
    + admit.
    + admit.
    + admit.
    (* Induction case *)
    + destruct (must_init init uninit universe (Pderef p (Tbox t))) eqn: INIT2; try congruence.
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). rewrite PTY in *. inv BM; simpl in *; try congruence.
      inv WTFP.
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
      intros (BM & WTLOC). rewrite PTY in *. inv BM; simpl in *; try congruence. inv WTFP.
      clear GCO. eapply EXTEND in P. rewrite P in *.
      econstructor. simpl. eauto. eauto. econstructor; eauto.
      (* two cases *)
      destruct (must_init init uninit universe (Pderef p (Tstruct l id1))) eqn: INIT1; try congruence.
      (** Case1 check that p is full so we can derive sem_wt_loc by mmatch *)
      destruct (is_full universe (Pderef p (Tstruct l id1))) eqn: FULL; try congruence.
      (* construct footprint of Pderef p to use mmatch *)
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tstruct l id1))) fpm = Some (b1, 0, fp0)).
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
      inv WT; try congruence. 
      eapply sem_wt_struct. intros.
      replace fty with (typeof_place (Pfield (Pderef p (Tstruct l id1)) fid fty)) by auto.
      (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
      exploit WT2; eauto. intros (A & B & C).
      eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
      eapply PTree_removeR. eauto. eauto.
      assert (INMEM: In (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield (Pderef p (Tstruct l id1)) fid fty, fty)) (co_members co))).
      (** TODO *)
      { admit. }
      generalize (POWN (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) INMEM). eauto.
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
      intros (BM & WTLOC). rewrite PTY in *.
      inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto.
      eauto. econstructor; eauto.
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
    intros (BM & WTLOC). rewrite PTY in WTLOC. eapply WTLOC.
    erewrite <- is_full_same. eauto. eapply sound_own_universe; eauto.
    (** Case2: p is not in the universe *)
    erewrite forallb_forall in POWN.
    (** Get the structure of fp by wt_footprint *)
    inv WTFP; try congruence.
    eapply sem_wt_struct. intros.
    replace fty with (typeof_place (Pfield p fid fty)) by auto.
    (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
    exploit WT2; eauto. intros (A & B & C).
    eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
    eapply PTree_removeR. eauto. eauto.
    assert (INMEM: In (Pfield p fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield p fid fty, fty)) (co_members co))).
    (** TODO *)
    { admit. }
    generalize (POWN (Pfield p fid fty, fty) INMEM). eauto.
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
    intros (BM & WTLOC). rewrite PTY in BM.
    inv BM; simpl in *; try congruence. 
    inv WTFP.
    rewrite PTY in WTLOC. eapply WTLOC.
    erewrite <- is_full_same; eauto.
    eapply sound_own_universe; eauto.
Admitted.

    
(* Footprint used in interface (for now, it is just defined by
support) *)
Definition flat_footprint : Type := Mem.sup.

(* Similar to inject_separated: m contains footprint fp1 and fp2 is
the extended footprint which is not in m *)
Definition flat_footprint_separated (fp1 fp2: flat_footprint) (m : mem) : Prop :=
  forall b, ~ Mem.sup_In b fp1 ->
       Mem.sup_In b fp2 ->
       ~ Mem.valid_block m b.


Fixpoint footprint_flat (fp: footprint) : flat_footprint :=
  match fp with
  | fp_emp => nil
  | fp_box b _ fp' =>
      b :: footprint_flat fp'
  | fp_struct _ fpl =>
      concat (map (fun '(_, _, _, fp) => footprint_flat fp) fpl)
  | fp_enum _ _ _ _ _ fp =>
      footprint_flat fp
  end.

Definition wf_footprint (fp: footprint) :=
  list_norepet (footprint_flat fp).

Definition footprint_disjoint (fp1 fp2: footprint) :=
  list_disjoint (footprint_flat fp1) (footprint_flat fp2).

Inductive footprint_disjoint_list : list footprint -> Prop :=
| fp_disjoint_nil: footprint_disjoint_list nil
| fp_disjoint_cons: forall fp fpl,
      list_disjoint (footprint_flat fp) (concat (map footprint_flat fpl)) ->
      footprint_disjoint_list fpl ->
      footprint_disjoint_list (fp::fpl)
.

Definition in_footprint (b: block) (fp: footprint) : Prop :=
  In b (footprint_flat fp).
  


(* Inductive footprint_path : Type := *)
(* | fpp_leaf *)
(* | fpp_box (p: footprint_path)        (* use p to select the box footprint *) *)
(* | fpp_field (idx: Z) (p: footprint_path) (* select the nth field in struct footprint and use p to select the remaining *) *)
(* | fpp_variant (tag: Z) (p: footprint_path) *)
(* . *)
  

(* Footprint defined by property *)
(* Definition footprint := block -> Z -> Prop.  *)

(* Definition empty_footprint : footprint := fun b ofs => False. *)

(* Definition footprint_equiv (fp1 fp2: footprint) := *)
(*   forall b ofs, fp1 b ofs <-> fp2 b ofs. *)

(* Definition footprint_incr (fp1 fp2: footprint) := *)
(*   forall b ofs, fp1 b ofs -> fp2 b ofs. *)

(* (** TODO: add some useful notations for footprint *) *)

(* Definition remove_footprint (fp: footprint) b ofs sz := *)
(*   fun b1 ofs1 => *)
(*     ((b1 = b /\ ofs <= ofs1 < ofs + sz) -> False) *)
(*     /\ fp b1 ofs1. *)

(* Definition add_footprint (fp: footprint) b ofs sz := *)
(*   fun b1 ofs1 => *)
(*     ((b1 = b /\ ofs <= ofs1 < ofs + sz)) *)
(*     \/ fp b1 ofs1. *)

(* Definition in_footprint (fp: footprint) b ofs sz := *)
(*   forall ofs1, ofs <= ofs1 < ofs + sz -> fp b ofs1. *)

(* Definition merge_footprint (fp1 fp2: footprint) := *)
(*   fun b ofs => fp1 b ofs \/ fp2 b ofs. *)

(* Definition merge_footprint_list (l: list footprint) := *)
(*   fun b ofs => exists fp, In fp l -> fp b ofs. *)

(* Definition footprint_disjoint (fp1 fp2: footprint) := *)
(*   forall b ofs, fp1 b ofs -> fp2 b ofs -> False. *)

(* Definition footprint_disjoint_list (l: list footprint) := *)
(*   forall fp1 fp2, In fp1 l -> In fp2 l -> *)
(*              ~ footprint_equiv fp1 fp2 -> *)
(*              footprint_disjoint fp1 fp2. *)


(** * Definitions of semantics typedness (TODO: support user-defined semantics types) *)

(* Semantics well typed location is mutually defined with semantics
well typed value *)
(* Inductive sem_wt_loc (ce: composite_env) (m: mem) : footprint -> block -> Z -> type -> Prop := *)
(* | sem_wt_base: forall ty b ofs fp chunk v *)
(*     (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk) *)
(*     (LOAD: Mem.load chunk m b ofs = Some v) *)
(*     (WT: sem_wt_val ce m fp v ty), *)
(*     sem_wt_loc ce m fp b ofs ty *)
(* | sem_wt_struct: forall b ofs co fpl orgs id *)
(*     (CO: ce ! id = Some co)    *)
(*     (* all fields are semantically well typed *) *)
(*     (FWT: forall n fid fty ffp fofs, *)
(*         field_tag fid (co_members co) = Some n -> *)
(*         field_type fid (co_members co) = OK fty -> *)
(*         list_nth_z fpl n = Some ffp -> *)
(*         field_offset ce fid co.(co_members) = OK fofs -> *)
(*         sem_wt_loc ce m ffp b (ofs + fofs) fty), *)
(*     sem_wt_loc ce m (fp_struct fpl) b ofs (Tstruct orgs id) *)
(* | sem_wt_enum: forall fp b ofs orgs id co tagz *)
(*     (CO: ce ! id = Some co)     *)
(*     (* Interpret the field by the tag and prove that it is well-typed *) *)
(*     (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz))) *)
(*     (FWT: forall fid fty fofs, *)
(*         list_nth_z co.(co_members) tagz = Some (Member_plain fid fty) -> *)
(*         variant_field_offset ce fid (co_members co) = OK fofs -> *)
(*         sem_wt_loc ce m fp b (ofs + fofs) fty), *)
(*     sem_wt_loc ce m (fp_enum tagz fp) b ofs (Tvariant orgs id) *)


(* with sem_wt_val (ce: composite_env) (m: mem) : footprint -> val -> type -> Prop := *)
(* | wt_val_unit: *)
(*   sem_wt_val ce m fp_emp (Vint Int.zero) Tunit *)
(* | wt_val_int: forall sz si n, *)
(*     Cop.cast_int_int sz si n = n -> *)
(*     sem_wt_val ce m fp_emp (Vint n) (Tint sz si) *)
(* | wt_val_float: forall n, *)
(*     sem_wt_val ce m fp_emp (Vfloat n) (Tfloat Ctypes.F64) *)
(* | wt_val_single: forall n, *)
(*     sem_wt_val ce m fp_emp (Vsingle n) (Tfloat Ctypes.F32) *)
(* | wt_val_long: forall si n, *)
(*     sem_wt_val ce m fp_emp (Vlong n) (Tlong si) *)
(* | wt_val_box: forall b ty fp *)
(*     (** Box pointer must be in the starting point of a block *) *)
(*     (* The value stored in (b,0) has type ty and occupies footprint fp *) *)
(*     (WTLOC: sem_wt_loc ce m fp b 0 ty) *)
(*     (VALID: Mem.range_perm m b (- size_chunk Mptr) (sizeof ce ty) Cur Freeable), *)
(*     sem_wt_val ce m (fp_box b fp) (Vptr b Ptrofs.zero) (Tbox ty) *)
(* (* TODO *) *)
(* (* | wt_val_ref: forall b ofs ty org mut, *) *)
(* (*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *) *)
(* | wt_val_struct: forall id orgs b ofs fp *)
(*     (WTLOC: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs) (Tstruct orgs id)), *)
(*     sem_wt_val ce m fp (Vptr b ofs) (Tstruct orgs id) *)
(* | wt_val_enum: forall id orgs b ofs fp *)
(*     (WTLOC: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs) (Tvariant orgs id)), *)
(*     sem_wt_val ce m fp (Vptr b ofs) (Tvariant orgs id) *)
(* . *)

Inductive sem_wt_val_list (m: mem) : list footprint -> list val -> list type -> Prop :=
| sem_wt_val_nil:
    sem_wt_val_list m nil nil nil
| sem_wt_val_cons: forall fpl fp vl tyl v ty,
    sem_wt_val_list m fpl vl tyl ->
    sem_wt_val m fp v ty ->
    sem_wt_val_list m (fp::fpl) (v::vl) (ty::tyl)
.


(** Semantics Interface *)

Inductive wt_rs_world :=
  rsw (sg: rust_signature)
    (fp: flat_footprint)
    (m: mem)
    (Hm: Mem.sup_include fp (Mem.support m)).

(** The footprint may be unique *)
Inductive wt_rs_query : wt_rs_world -> rust_query -> Prop :=
| wt_rs_query_intro: forall sg m vf args fpl fp Hm
    (DIS: footprint_disjoint_list fpl)
    (SEMWT: sem_wt_val_list m fpl args (rs_sig_args sg))
    (* footprints are well-typed *)
    (WTFP: list_forall2 (fun argty fp => wt_footprint (rs_sig_comp_env sg) (rs_sig_comp_env sg) argty fp) (rs_sig_args sg) fpl)
    (* structured footprint is equivalent with the flat footprint in the interface *)
    (EQ: list_equiv fp (concat (map footprint_flat fpl))),
    wt_rs_query (rsw sg fp m Hm) (rsq vf sg args m)
.

(* Only consider ownership transfer for now. The footprints of generic
origins are more complicated *)
Inductive rsw_acc : wt_rs_world -> wt_rs_world -> Prop :=
| rsw_acc_intro: forall sg fp fp' m m' Hm Hm'
    (UNC: Mem.unchanged_on (fun b ofs => ~ In b fp) m m')
    (* new footprint is separated *)
    (SEP: flat_footprint_separated fp fp' m),
    rsw_acc (rsw sg fp m Hm) (rsw sg fp' m' Hm').

Inductive wt_rs_reply : wt_rs_world -> rust_reply -> Prop :=
| wt_rs_reply_intro: forall rfp m rv sg fp Hm
    (SEMWT: sem_wt_val m rfp rv (rs_sig_res sg))
    (WTFP: wt_footprint (rs_sig_comp_env sg) (rs_sig_comp_env sg) (rs_sig_res sg) rfp)
    (* rfp is separated from fpl *)
    (SEP: list_disjoint (footprint_flat rfp) fp),
    wt_rs_reply (rsw sg fp m Hm) (rsr rv m)
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

(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* A footprint in a function frame *)

Definition flat_fp_map (fpm: fp_map) : flat_footprint :=
  concat (map (fun elt => footprint_flat (snd elt)) (PTree.elements fpm)).

(* The footprint in a module (similar to continuation) *)

Inductive fp_frame : Type :=
| fpf_emp
(* we need to record the footprint of the stack *)
| fpf_func (e: env) (fpm: fp_map) (fpf: fp_frame)
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
  | fpf_drop fp fpl fpf =>
      footprint_flat fp ++ concat (map footprint_flat fpl) ++ flat_fp_frame fpf
  end.

(* Lemma get_footprint_map_app: forall id fp phl phl' fpm, *)
(*     get_footprint_map (id, phl) fpm = Some fp -> *)
(*     get_footprint_map (id, phl ++ phl') fpm = get_footprint phl' fp. *)
(* Admitted. *)

(* Lemma footprint_map_gss: forall phl id fpm1 fpm2 fp1 fp2 ce, *)
(*     (VPH: valid_path *)
(*     get_footprint_map (id, phl) fpm1 = Some fp1 -> *)
(*     exists fpm3, set_footprint_map ce (id, phl) fpm2 fp2 = Some fpm3 *)
(*             /\ get_footprint_map (id, phl) fpm3 = Some fp2. *)


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
Let match_stmt (ae: AN) body cfg s := match_stmt get_init_info ae (move_check_stmt ce) body cfg s s.

(* Hypothesis CONSISTENT: composite_env_consistent ce. *)

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
      
(** IMPORTANT TODO  *)
Lemma mmatch_move_place_sound: forall p fpm1 fpm2 m le own
    (MM: mmatch fpm1 m le own)
    (CLR: clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2),
    (* valid_owner makes this proof difficult *)
    mmatch fpm2 m le (move_place own (valid_owner p)).
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
      exploit set_footprint_map_app_inv. eapply GET1. eauto.
      intros (b2 & ofs2 & fp3 & fp4 & A & B & C).
      rewrite PFP in B. inv B.
      (* use mmatch *)
      exploit MM. erewrite POP2. eauto.
      eapply move_place_init_is_init. eauto.
      intros (BM & FULL).
      (* We need to say that p must not be shallow children of p0!!! *)
      (** TODO: 1. p0's type must not be struct/variant if so, no
        children of p0 is in the universe (to add a properties for
        universe in own_env) *)
      assert (PTY: exists ty, typeof_place p0 = Tbox ty). admit.
      destruct PTY as (ty & PTY). rewrite PTY in *.
      inv BM. split.
      (** TODO: po is strict prefix of p so phl is not nil  *)
      destruct phl. admit.
      simpl in C. destruct p2; try congruence.
      destruct (set_footprint phl (clear_footprint_rec f) fp) eqn: SET; try congruence.
      inv C. econstructor; eauto.
      (** is_full is not possible because p is in the universe (add
        a premise in this lemma) *)
      admit.
      simpl in TY. congruence.
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
Admitted.
       
(* Lemma footprint_map_gss: forall p phs fpm1 fp1 fp2 ce le *)
(*   (WT: wt_place le ce p) *)
(*   (POP: path_of_place ce p phs) *)
(*   (WTFP1: wt_footprint ce (typeof_place p) fp2) *)
(*   (GFP: get_footprint_map phs fpm1 = Some fp1), *)
(*   exists fpm2, set_footprint_map ce phs fp2 fpm1 = Some fpm2 *)
(*           /\ get_footprint_map phs fpm2 = Some fp2. *)
(* Admitted. *)
    
(** dereferce a semantically well typed location produces well typed value *)
Lemma deref_sem_wt_loc_sound: forall m fp b ofs ty v
    (WT: sem_wt_loc m fp b (Ptrofs.unsigned ofs) ty)
    (DE: deref_loc ty m b ofs v),
    sem_wt_val m fp v ty.
Proof.
  intros. destruct ty; inv WT; inv DE; simpl in *; try congruence.
  (* struct *)
  - econstructor. eapply sem_wt_struct; eauto.
  (* enum *)
  - econstructor. eapply sem_wt_enum; eauto.
Qed.
  
(* The result of eval_expr is semantically well typed *)

(* The footprint must be fp_emp in pexpr *)
Lemma eval_pexpr_sem_wt: forall fpm m le own pe v init uninit universe
    (MM: mmatch fpm m le own)
    (EVAL: eval_pexpr ce le m pe v)
    (SOUND: sound_own own init uninit universe)
    (CHECK: move_check_pexpr init uninit universe pe = true),
    sem_wt_val m fp_emp v (typeof_pexpr pe).
Admitted.

Lemma eval_expr_sem_wt: forall fpm1 m le own1 own2 e v init uninit universe
    (MM: mmatch fpm1 m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (EVAL: eval_expr ce le m e v)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_expr ce init uninit universe e = true)
    (OWN: move_place_option own1 (moved_place e) = own2)
    (WFENV: wf_env fpm1 ce le)
    (WT: wt_expr le ce e),
  (** TODO: how to relate fp and fpm2 ? We should show that they are disjoint *)
  exists fp fpm2, sem_wt_val m fp v (typeof e)
             (* If expr is pure expr, fp is fp_emp and not from any phs *)
             (* /\ get_footprint_map phs fpm1 = Some fp *)
             (* /\ clear_footprint_map ce phs fpm1 = Some fpm2 *)
             /\ mmatch fpm2 m le own2
             /\ wf_env fpm2 ce le
             (* footprint disjointness *)
             /\ list_disjoint (footprint_flat fp) (flat_fp_map fpm2).
Proof.
  intros. destruct e.
  (* Emoveplace *)
  - simpl in *. inv EVAL. inv WT. inv H2.
    destruct (place_eq p (valid_owner p)); subst.
    (* p is not downcast *)
    + eapply andb_true_iff in CHECK. destruct CHECK as (DONW & MOVABLE).
      exploit eval_place_sound; eauto.
      intros (pfp & ce' & PFP & WTFP & EXT).
      (* location of p is sem_wt *)
      exploit movable_place_sem_wt; eauto. instantiate (1 := ce).
      (** TODO: wt_footprint implication *)
      admit.
      red. auto.
      intros WT_LOC. 
      (* deref sem_wt location *)
      exploit deref_sem_wt_loc_sound; eauto. intros WT_VAL.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2).
      { unfold clear_footprint_map.
        admit.
      }
      destruct A as (fpm2 & CLEAR).
      exists pfp, fpm2. repeat apply conj; auto.
      eapply mmatch_move_place_sound; eauto. 
      (* wf_env *)
      constructor. intros.
      destruct (peq (local_of_place p) id).
      subst.
      (** set a wt_footprint in a wt_footprint is still wt *)
      exploit wf_env_footprint; eauto. intros (fp1 & A & B).
      admit.
      exploit wf_env_footprint; eauto.
      intros (fp & GFPM1 & WFFP). exists fp. split; auto.
      (** set (local_of_place p) unchanges the footprint of id *)
      admit.
      (** use GFP: get norepet footprint_map is disjoint  *)
      admit.
    (* p is downcast *)
    + 
      do 2 rewrite andb_true_iff in CHECK. destruct CHECK as ((DOWN & INIT) & FULL).
      exploit eval_place_sound; eauto.
      intros (fp1 & ce1 & PFP & WTFP).
      exploit valid_owner_place_footprint; eauto.
      intros (fp2 & ofs1 & fofs1 & PFP1 & VOFS & OFSEQ).
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC).      
      exploit valid_owner_sem_wt_loc. eapply WTLOC.
      erewrite <- is_full_same; eauto. eapply sound_own_universe; eauto.
      eauto. intros WTLOC1.
      rewrite <- OFSEQ in WTLOC1.
      exploit deref_sem_wt_loc_sound; eauto. intros WT_VAL.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2).
      { admit. }
      destruct A as (fpm2 & CLEAR).
      exists fp1, fpm2. repeat apply conj; auto.
      eapply mmatch_move_place_sound; eauto.
      (* wf_env *)
      admit.
      (* disjoint *)
      admit.
      
  - exists fp_emp, fpm1. simpl in *. subst.
    inv EVAL.
    exploit eval_pexpr_sem_wt; eauto. intros VWT.
    repeat apply conj; auto.
    red. intros. inv H.
Admitted.

(** IMPORTANT TODO: *)
Lemma sem_wt_loc_unchanged: forall m1 m2 fp b ofs ty
    (WT: sem_wt_loc m1 fp b ofs ty)
    (UNC: Mem.unchanged_on (fun b1 _ => In b1 (footprint_flat fp)) m1 m2),
      sem_wt_loc m2 fp b ofs ty.
Admitted.


Definition list_interval {A: Type} (l: list A) (lo: Z) (sz: Z) :=
  firstn (Z.to_nat sz) (skipn (Z.to_nat lo) l).

Definition in_range (lo sz hi: Z) : Prop :=
  0 <= lo /\ lo + sz <= hi.

(** It we want to derive sem_wt_bytes from sem_wt_loc/val without the
wt_footprint assumption, we need to add size attribute to the
footprint. Otherwise we need to consider the well-founded induction of
composite_env *)
Inductive sem_wt_bytes (m: mem) : footprint -> list memval -> type -> Prop :=
| sem_wt_bytes_base: forall chunk bytes fp ty
    (AS: access_mode ty = Ctypes.By_value chunk)
    (WT: sem_wt_val m fp (decode_val chunk bytes) ty),
  sem_wt_bytes m fp bytes ty  
(* | sem_wt_bytes_box: forall b sz ty bytes bytes1 fp *)
(*     (DEC: decode_val Mptr bytes = Vptr b Ptrofs.zero) *)
(*     (LOAD: Mem.loadbytes m b 0 sz = Some bytes1) *)
(*     (WT: sem_wt_bytes m fp bytes1 ty), *)
(*     sem_wt_bytes m (fp_box b sz fp) bytes (Tbox ty) *)
| sem_wt_bytes_struct: forall fpl bytes orgs id
    (WT: forall fid fty fofs ffp,
        find_fields fid fpl = Some (fid, fty, fofs, ffp) ->          
        sem_wt_bytes m ffp (list_interval bytes fofs (sizeof ce fty)) fty),
    sem_wt_bytes m (fp_struct id fpl) bytes (Tstruct orgs id)
| sem_wt_bytes_enum: forall fp orgs id tagz fid fty fofs bytes
    (TAG: decode_val Mint32 (firstn (Z.to_nat (size_chunk Mint32)) bytes) = Vint (Int.repr tagz))
    (WT: sem_wt_bytes m fp (skipn (Z.to_nat fofs) bytes) fty),
    sem_wt_bytes m (fp_enum id tagz fid fty fofs fp) bytes (Tvariant orgs id)
.


(** May be very difficult  *)
Lemma loadbytes_interval: forall m b ofs sz ofs1 sz1 bytes,
    in_range ofs1 sz1 sz ->
    Mem.loadbytes m b ofs sz = Some bytes ->
    Mem.loadbytes m b (ofs + ofs1) sz1 = Some (list_interval bytes ofs1 sz1).
Admitted.
  
Lemma sem_wt_loc_implies_wt_bytes: forall m fp b ofs bytes ty
    (LOAD: Mem.loadbytes m b ofs (sizeof ce ty) = Some bytes)
    (* (COMP: complete_type ce ty = true) *)
    (WT: sem_wt_loc m fp b ofs ty),
    sem_wt_bytes m fp bytes ty.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv WT. econstructor. eauto.
    exploit Mem.load_loadbytes; eauto.
    intros (bytes1 & LOAD1 & EQ). 
    assert (SZEQ: size_chunk chunk = sizeof ce ty).
    { eapply sizeof_by_value. auto. }
    rewrite <- SZEQ in LOAD.
    rewrite LOAD in LOAD1. inv LOAD1.
    auto.
  - inv WT. econstructor. eauto.
    exploit Mem.load_loadbytes; eauto.
    intros (bytes1 & LOAD1 & EQ). 
    assert (SZEQ: size_chunk chunk = sizeof ce ty).
    { eapply sizeof_by_value. auto. }
    rewrite <- SZEQ in LOAD.
    rewrite LOAD in LOAD1. inv LOAD1.
    auto.
  - inv WT. inv WT0; simpl in *; try congruence.
    eapply sem_wt_bytes_struct. intros until ffp.
    intros FIND.
    exploit FWT; eauto. intros WTLOC.
    exploit loadbytes_interval; eauto. instantiate (1 := (sizeof ce fty)).
    instantiate (1 := fofs).
    (** in_range proof: we need wt_footprint but how to perform induction? !!! *)
    admit.
    intros LOAD1.
    exploit find_fields_some; eauto. intros (A & B). subst.
    (* use I.H. *)
    exploit H; eauto. 
  - inv WT. inv WT0; simpl in *; try congruence.
    eapply sem_wt_bytes_enum.
    (** TODO: wt_footprint should state that the fofs is larger than 4
    and sizeof enum is larger than fofs *)
    assert (LEN: exists fsz n, sizeof ce (Tvariant orgs id) = 4 + n + fsz /\ 4 + n = ofs /\ fsz >= 0 /\ n >= 0).
    { admit. }
    destruct LEN as (fsz & n & A & B & C & D). subst.
    rewrite A in LOAD.    
    exploit Mem.loadbytes_split. eauto. lia. lia.
    intros (byte1 & byte2 & E & F & G). subst.
    replace (Z.to_nat (size_chunk Mint32)) with 4%nat.
    2: { simpl. auto. }
    rewrite firstn_app.
    replace (4 - length byte1)%nat with 0%nat.
    2: { eapply Mem.loadbytes_length in E. rewrite E. lia. }
    rewrite firstn_O. rewrite app_nil_r.
    exploit Mem.loadbytes_split. eauto. lia. lia.
    intros (byte3 & byte4 & P1 & P2 & P3). subst.
    admit.
Admitted.

Lemma sem_wt_bytes_implies_wt_loc: forall m fp b ofs bytes ty
    (LOAD: Mem.loadbytes m b ofs (sizeof ce ty) = Some bytes)
    (ALIGN: (alignof ce ty | ofs))
    (WT: sem_wt_bytes m fp bytes ty),
    sem_wt_loc m fp b ofs ty.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv WT. econstructor. eauto.
    assert (SZEQ: size_chunk chunk = sizeof ce ty).
    { eapply sizeof_by_value. auto. }
    rewrite <- SZEQ in LOAD.
    exploit Mem.loadbytes_load; eauto.
    (* alignment *)
    eapply Z.divide_trans.
    eapply alignof_by_value. eauto. eauto.
    auto.
  - inv WT. econstructor. eauto.
    assert (SZEQ: size_chunk chunk = sizeof ce ty).
    { eapply sizeof_by_value. auto. }
    rewrite <- SZEQ in LOAD.
    exploit Mem.loadbytes_load; eauto.
    (* alignment *)
    eapply Z.divide_trans.
    eapply alignof_by_value. eauto. eauto.
    auto.
  - inv WT. inv WT0; simpl in *; try congruence.
    eapply sem_wt_struct. intros until ffp. intros FIND.
    exploit WT0; eauto. intros WTBYTES.
    exploit loadbytes_interval; eauto. instantiate (1 := (sizeof ce fty)).
    instantiate (1 := fofs).
    (** in_range proof: we need wt_footprint but how to perform induction? !!! *)
    admit.
    intros LOAD1.
    exploit find_fields_some; eauto. intros (A & B). subst.
    exploit H; eauto.
    (** alignof proof *)
    admit.
  - admit.
Admitted.  
    
Lemma assign_loc_sem_wt: forall fp ty m1 b ofs v m2
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val m1 fp v ty)
    (WTFP: wt_footprint ce ce ty fp)
    (* the assignment does not affect the footprint *)
    (IN: ~ In b (footprint_flat fp)),
    sem_wt_loc m2 fp b (Ptrofs.unsigned ofs) ty.
Proof.
  (* no need to induciton on fp *)
  destruct fp; intros.
  - inv WT.
    + inv AS. eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv H.
      simpl. econstructor.
    + inv AS. eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H0.
      destruct sz; destruct si; inv H0; simpl; econstructor;
        try (simpl in H; rewrite H; auto).
      auto. auto.
      simpl in H. destruct (Int.eq n Int.zero).
      subst. simpl. auto.
      subst. simpl. auto.
      simpl in H. destruct (Int.eq n Int.zero).
      subst. simpl. auto.
      subst. simpl. auto.
    (* float *)
    + admit.
    (* double *)
    + admit.
    (* long *)
    + admit.
    + inv WTFP. congruence.
    + inv WTLOC. simpl in *. congruence.
  - inv WTFP. inv WT.
    inv AS; simpl in *; try congruence.
    eapply Decidable.not_or in IN. destruct IN as (IN1 & IN2).
    assert (UNC: Mem.unchanged_on (fun b _ => b <> b0) m1 m2).
    { eapply Mem.store_unchanged_on; eauto. }
    econstructor. simpl; eauto.
    eapply Mem.load_store_same. eauto.
    exploit sem_wt_loc_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    intro. apply IN2. subst. auto.
    intros WTLOC1.
    inv H. unfold Mptr.
    destruct Archi.ptr64 eqn: A; simpl; try rewrite A.
    econstructor; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    econstructor; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
  - inv WTFP.
    inv AS. simpl in *. try congruence.
    inv WT.
    exploit sem_wt_loc_implies_wt_bytes; eauto. intros WTBYTES.
    assert (WTBYTES1: sem_wt_bytes m2 (fp_struct id fpl) bytes (Tstruct orgs id)).
    { admit. }
    exploit Mem.loadbytes_storebytes_same; eauto.
    intros LOAD1.
    exploit Mem.loadbytes_length. eapply H4. intros LEN.
    rewrite LEN in LOAD1. rewrite Z_to_nat_max in LOAD1.
    replace (Z.max (sizeof ce (Tstruct orgs id)) 0) with (sizeof ce (Tstruct orgs id)) in LOAD1.    
    eapply sem_wt_bytes_implies_wt_loc; eauto.
    (** TODO: Align properties  *) admit.
    generalize (sizeof_pos ce (Tstruct orgs id)). extlia.

  - 
    
(* Mem.storebytes_split *)
    
(*     Lemma load_sem_wt_val_loc:  *)
(*       Mem.loadbytes_storebytes_same *)
Admitted.
    
(** Important Lemma  *)
(* Consider assign to a variant? *)
Lemma assign_loc_sound: forall fpm1 m1 m2 own1 own2 b ofs v p vfp pfp e ty
    (MM: mmatch fpm1 m1 e own1)
    (TY: ty = typeof_place p)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val m1 vfp v ty)
    (WTFP: wt_footprint ce ce ty vfp)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm1 = Some (b, (Ptrofs.unsigned ofs), pfp))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (* type of place is not enum *)
    (NOTENUM: forall orgs id, typeof_place p <> Tvariant orgs id)
    (NOREP: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_flat vfp) (flat_fp_map fpm1)),
  exists fpm2, set_footprint_map (path_of_place p) vfp fpm1 = Some fpm2
          /\ mmatch fpm2 m2 e own2
          /\ list_norepet (flat_fp_map fpm2).
Proof.
  intros. destruct (path_of_place p) eqn: POP.
  exploit get_set_footprint_map_exists; eauto.
  instantiate (1 := vfp).
  intros (fpm2 & A & B). exists fpm2. split. auto.
  split.
  (* mmatch *)
  - red. intros until fp.
    intros GFP INIT.
    unfold own_transfer_assign in CKAS.
    destruct (is_prefix p p0) eqn: PRE.
    (* p0 is children of p1: we need to prove that the value/location of p0 is sem_wt *)
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
      (** TODO: b1 is not in fp1  *) admit.
      intros WTLOC.
      Lemma get_loc_footprint_sem_wt: forall phl fp b ofs b1 ofs1 fp1,
          get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
          wt_footprint ce ce ty fp1 ->
          sem_wt_loc m fp b ofs ty ->
          (** some relation between ty an ty1 *)
          sem_wt_loc m fp1 b1 ofs ty1 
      
      
Inductive member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : member -> Prop :=
| member_footprint_struct: forall fofs fid fty
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (WT: sem_wt_loc ce m fp b (ofs + fofs) fty),
    member_footprint m co b ofs fp (Member_plain fid fty)
| member_footprint_enum: forall fofs fid fty
    (STRUCT: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: sem_wt_loc ce m fp b (ofs + fofs) fty),
    member_footprint m co b ofs fp (Member_plain fid fty)
.

(* hacking: simulate the deref_loc_rec to get the path, footprint and
location of the value. fp is the start of the footprint. *)
Inductive deref_loc_rec_footprint (m: mem) (b: block) (ofs: Z) (fp: footprint) : list type -> block -> Z -> list path -> footprint -> Prop :=
| deref_loc_rec_footprint_nil:
  deref_loc_rec_footprint m b ofs fp nil b ofs nil fp
| deref_loc_rec_footprint_cons: forall ty tys fp2 b1 ofs1 b2 phl
    (* The location (b1, ofs1) has footprint (fp_box b2 fp2) and the
    location of (b2,0) has footprint fp2 *)
    (FP: deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl (fp_box b2 fp2))
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 (Ptrofs.zero)))
    (* block b2 is freeable *)
    (FREE: Mem.range_perm m b2 (- size_chunk Mptr) (sizeof ce ty) Cur Freeable),
    (* how to relate ty and b *)
    deref_loc_rec_footprint m b ofs fp (ty :: tys) b2 0 (phl ++ [ph_deref]) fp2.

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
Lemma deref_loc_rec_footprint_eq: forall m b ofs tys b1 ofs1 b2 ofs2 fp1 fp2 phl,
          deref_loc_rec m b (Ptrofs.repr ofs) tys (Vptr b1 ofs1) ->
          deref_loc_rec_footprint m b ofs fp1 tys b2 ofs2 phl fp2 ->
          b1 = b2 /\ ofs1 = Ptrofs.repr ofs2.
Admitted.

Inductive drop_member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) : option drop_member_state -> footprint -> Prop :=
| drop_member_fp_none:
    drop_member_footprint m co b ofs None fp_emp
| drop_member_fp_comp_struct: forall fid fofs fty fp tyl b1 ofs1 fp1 compty phl
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fp tyl b1 ofs1 phl fp1)
    (* (b1, ofs1) is sem_wt_loc *)
    (WT: sem_wt_loc ce m fp1 b1 ofs1 compty),
    drop_member_footprint m co b ofs (Some (drop_member_comp fid fty compty tyl)) fp
| drop_member_fp_comp_enum: forall fid fofs fty fp tyl b1 ofs1 fp1 compty phl
    (ENUM: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fp tyl b1 ofs1 phl fp1)
    (* (b1, ofs1) is sem_wt_loc *)
    (WT: sem_wt_loc ce m fp1 b1 ofs1 compty),
    drop_member_footprint m co b ofs (Some (drop_member_comp fid fty compty tyl)) fp
| drop_member_fp_box_struct: forall fid fofs fty fp tyl b1 ofs1 phl
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fp tyl b1 ofs1 phl fp_emp),
    drop_member_footprint m co b ofs (Some (drop_member_box fid fty tyl)) fp
| drop_member_fp_box_enum: forall fid fofs fty fp tyl b1 ofs1 phl
    (ENUM: co.(co_sv) = TaggedUnion)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fp tyl b1 ofs1 phl fp_emp),
    drop_member_footprint m co b ofs (Some (drop_member_box fid fty tyl)) fp
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

(* Every former element is the children of letter elements *)
(** TODO: maybe we need a more precise definition  *)
Inductive sound_split_fully_own_place : list place -> Prop :=
| sound_split_fully_nil: sound_split_fully_own_place nil
| sound_split_fully_cons: forall p l
    (CHILDREN: Forall (fun p' => is_prefix p p' = false) l)
    (SOUND: sound_split_fully_own_place l),
    sound_split_fully_own_place (p::l).

(* (* May be difficult: algebraic property of split_drop_place *) *)
Inductive sound_split_drop_place (own: own_env) : list (place * bool) -> Prop :=
| sound_split_drop_nil: sound_split_drop_place own nil
| sound_split_drop_cons_full: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun elt => is_prefix p (fst elt) = false) l ->
    (* p is fully owned so that p is owned equivalent to p is movable *)
    is_init own p = is_movable own p ->
    sound_split_drop_place own l ->
    sound_split_drop_place own ((p, true) :: l)
| sound_split_drop_cons_partial: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun elt => is_prefix p (fst elt) = false) l ->
    sound_split_drop_place own l ->
    sound_split_drop_place own ((p, false) :: l)
.

(* Lemma split_drop_place_sound: forall ce own p universe drops *)
(*     (WF: wf_own_env own) *)
(*     (UNI: (own_universe own) ! (local_of_place p) = Some universe) *)
(*     (SPLIT: split_drop_place ce universe p (typeof_place p) = OK drops), *)
(*   sound_split_drop_place own drops. *)
(* Admitted. *)


Inductive sound_drop_fully_owned (own: own_env) : option drop_place_state -> Prop :=
| sound_drop_fully_owned_none: sound_drop_fully_owned own None
| sound_drop_fully_owned_comp: forall p l
    (* drop the head place does not affect the ownership status in the *)
(*     rest of the list *)
    (FO: sound_split_fully_own_place l)
    (OWN: forallb (is_init own) l = true)
    (MOVE: is_movable own p = true)
    (* we should show that move out p should not affect the ownership *)
(*     of l *)
    (SEP: Forall (fun elt => is_prefix p elt = false) l),
    sound_drop_fully_owned own (Some (drop_fully_owned_comp p l))
| sound_drop_fully_owned_box: forall l
    (FO: sound_split_fully_own_place l)
    (OWN: forallb (is_init own) l = true),
    sound_drop_fully_owned own (Some (drop_fully_owned_box l))
.

(* combine sound_drop_fully_owned, sound_split_drop_place and require
that st and ps are disjoint *)
Inductive sound_drop_place (own: own_env) (ps: list (place * bool)) : option drop_place_state -> Prop :=
| sound_drop_place_none: forall
    (SPLIT: sound_split_drop_place own ps),
    sound_drop_place own ps None
| sound_drop_place_comp: forall p l
    (SOUND: sound_split_fully_own_place (p::l))
    (OWN: forallb (is_init own) l = true)
    (MOVE: is_movable own p = true)
    (SPLIT: sound_split_drop_place own ps)
    (* we should show that p and l are both disjoint with ps *)
    (SEP: Forall (fun p' => Forall (fun elt => is_prefix p' (fst elt) = false) ps) (p::l)),
    sound_drop_place own ps (Some (drop_fully_owned_comp p l))
| sound_drop_place_box: forall l
    (SOUND: sound_split_fully_own_place l)
    (OWN: forallb (is_init own) l = true)
    (SPLIT: sound_split_drop_place own ps)
    (* we should show that l is disjoint with ps *)
    (SEP: Forall (fun p' => Forall (fun elt => is_prefix p' (fst elt) = false) ps) l),
    sound_drop_place own ps (Some (drop_fully_owned_box l))
.

(* Soundness of continuation: the execution of current function cannot
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
    (RET: cfg ! nret = Some Iend),
    sound_cont an body cfg (Kcall p f e own k) nret None None nret m fpf
| sound_Kdropplace: forall f st ps nret cfg pc cont brk k own1 own2 e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc cont brk nret m fpf)
    (MM: mmatch ce fpm m e own1)
    (WF: wf_own_env own1)
    (** DP may be wrong *)
    (DP: sound_drop_place own1 ps st)
    (MOVESPLIT: move_split_places own1 ps = own2)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe),
    sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg (Kdropplace f st ps e own1 k) pc cont brk nret m (fpf_func e fpm fpf)
| sound_Kdropcall: forall an body cfg k pc cont brk nret fpf st co fp ofs b membs fpl id m
    (CO: ce ! id = Some co)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) st fp)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (SOUND: sound_cont an body cfg k pc cont brk nret m fpf),
    sound_cont an body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret m (fpf_drop fp fpl fpf)

with sound_stacks : cont -> mem -> fp_frame -> Prop :=
| sound_stacks_stop: forall m,
    sound_stacks Kstop m fpf_emp
| sound_stacks_call: forall f nret cfg pc contn brk k own1 own2 p e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc contn brk nret m fpf)
    (MM: mmatch ce fpm m e own1)
    (WF: wf_own_env own1)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)                  
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe),
    sound_stacks (Kcall p f e own1 k) m (fpf_func e fpm fpf).
    

(** TODO: add syntactic well typedness in the sound_state and
sound_cont *)
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s pc next cont brk nret k e own m fpm fpf flat_fp sg mayinit mayuninit Hm
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (STMT: match_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s pc next cont brk nret)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own mayinit mayuninit universe)
    (MM: mmatch ce fpm m e own)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (* footprint is separated *)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (* we need to maintain the well-formed invariant of own_env *)
    (WF: wf_own_env own),
    sound_state (State f s k e own m)
| sound_dropplace: forall f cfg entry maybeInit maybeUninit universe next cont brk nret st drops k e own1 own2 m fpm fpf flat_fp sg mayinit mayuninit Hm
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (MM: mmatch ce fpm m e own1)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (* every place in the drop_fully_owned state is owned: this may be
    wrong because it does not consider own is changing *)
    (DP: sound_drop_place own1 drops st)
    (WF: wf_own_env own1)
    (MOVESPLIT: move_split_places own1 drops = own2)
    (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe),
    (* no need to maintain borrow check domain in dropplace? But how
    to record the pc and next statement? *)
    sound_state (Dropplace f st drops k e own1 m)
| sound_dropstate: forall an body cfg next cont brk nret id co fp fpl b ofs st m membs k fpf flat_fp sg Hm
    (CO: ce ! id = Some co)
    (* The key is how to prove semantics well typed can derive the
    following two properties *)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) st fp)
    (* all the remaining members are semantically well typed *)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (CONT: sound_cont an body cfg k next cont brk nret m fpf)
    (FLAT: flat_fp = flat_fp_frame (fpf_drop fp fpl fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm)),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k flat_fp sg Hm
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WT: sem_wt_val_list ce m fpl args (type_list_of_typelist tyargs))
    (STK: sound_stacks k m fpf)
    (FLAT: flat_fp = flat_fp_frame fpf)
    (* also disjointness of fpl and fpf *)
    (NOREP: list_norepet (flat_fp ++ concat (map footprint_flat fpl)))
    (ACC: rsw_acc w (rsw sg flat_fp m Hm)),
    sound_state (Callstate vf args k m)
| sound_returnstate: forall sg flat_fp m k retty rfp v Hm
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = Some retty)
    (WT: sem_wt_val ce m rfp v retty)
    (SEP: list_norepet (flat_fp ++ (footprint_flat rfp))),
    sound_state (Returnstate v k m)
.


(** IMPORTANT TODO: This lemma requires that no p's shallow prefix
    exists in the universe *)
(* Lemma must_init_is_owned: forall p own init uninit universe *)
(*     (SOUND: sound_own own init uninit universe) *)
(*     (INIT: must_init init uninit universe p = true), *)
(*     is_owned own p = true. *)
(* Admitted. *)

(** IMPORTANT TODO *)
(* Lemma must_movable_is_owned: forall p own init uninit universe *)
(*     (SOUND: sound_own own init uninit universe) *)
(*     (INIT: must_movable init uninit universe p = true), *)
(*     is_owned own p = true. *)
(* Admitted. *)

Lemma must_movable_prefix: forall p p' own init uninit universe
    (SOUND: sound_own own init uninit universe)
    (INIT: must_movable ce init uninit universe p = true)
    (PRE: is_prefix p p' = true),
    must_movable ce init uninit universe p' = true.
Admitted.


(* Lemma path_of_eval_place: forall e m p b ofs *)
(*     (EVAL: eval_place ce e m p b ofs), *)
(*   exists phl, path_of_place ce p (local_of_place p) phl. *)
(* Admitted. *)
    
    
(* The footprint contained in the location of a place *)
Lemma eval_place_sound: forall e m p b ofs own fpm init uninit universe
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch ce fpm m e own)
    (WFOWN: wf_env ce fpm e)
    (WT: wt_place (env_to_tenv e) ce p)
    (SOWN: sound_own own init uninit universe)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: dominators_must_init init uninit universe p = true),
  (* Do we need to specify the properties of fp? Do we need to show
  the permission of the location of p? *)
  exists fp phl, place_footprint ce fpm e p b (Ptrofs.unsigned ofs) fp
            /\ path_of_place ce p (local_of_place p, phl)
            /\ get_footprint_map (local_of_place p, phl) fpm = Some fp.
        (* /\ wt_footprint ce (typeof_place p) fp. *)
    (* if consider reference, we cannot say that p is a subplace of
    p', instead we need to state that the owner p points to is a
    subplace of p' *)
Proof.
  induction 1; intros.
  (* Plocal *)
  - rewrite Ptrofs.unsigned_zero.
    exploit wf_env_footprint; eauto. intros (fp & FP & WTFP).
    exists fp, nil. repeat apply conj. econstructor; eauto.
    simpl. econstructor.
    simpl. rewrite FP. auto.
  (* Pfield *)
  - inv WT.
    (* two type facts, reduce one *)
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    (** TODO: make it a lemma: prove p's dominators are init *)
    assert (PDOM: dominators_must_init init uninit universe p = true) by admit.    
    exploit IHEVAL. 1-5: auto.
    intros (fp & phl & PFP & POP & PHS).
    exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN).
    (** TODO: produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr.
    (** Inversion of WTFP *)
    exploit place_footprint_wt; eauto. intros WTFP.
    rewrite H in WTFP. inv WTFP.
    (* case1: the struct footprint is empty *)    
    exists fp_emp, (phl++[ph_field id0 tag]). repeat apply conj.
    eapply place_footprint_field_emp; eauto.
    econstructor; eauto.
    erewrite get_footprint_map_app; eauto. simpl. auto.
    (* case2 *)
    exploit WFFP; eauto. intros (ffp & FPNTH & WTFP1).
    exists ffp, (phl++[ph_field id0 tag]). repeat apply conj.
    econstructor; eauto.
    econstructor; eauto.
    erewrite get_footprint_map_app; eauto. simpl. rewrite FPNTH. auto.    
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
    assert (PDOM: dominators_must_init init uninit universe p = true) by admit.    
    exploit IHEVAL. 1-5: auto.
    intros (fp & phl & PFP & POP & GFM).
    (** TODO: produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr.
    (** Prove that p is_owned  *)
    unfold dominators_must_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).
    exploit MM. eauto.
    eapply must_init_sound; eauto.        
    (* inversion of bmatch *)
    intros (BM & FULL). rewrite H in BM. inv BM.
    (* rewrite some redundant premises *)
    rewrite H0 in CO. inv CO.
    simpl in H1. rewrite H1 in TAG. inv TAG. rewrite Int.unsigned_repr in H2.
    exists fp0, (phl++[ph_downcast id0 tagz]). repeat apply conj.
    econstructor; eauto.
    eapply place_footprint_wt in PFP. inv PFP. rewrite H in H5. inv H5.
    exploit WFFP; eauto.
    (* path_of_place *)
    econstructor; eauto. 
    (* get_footprint_map *)
    erewrite get_footprint_map_app; eauto.
    simpl. destruct Z.eq_dec; try congruence.    
    (* exploit FMATCH; eauto. intros BM1. simpl. *)
    (* eapply bmatch_implies_wt_footprint; eauto. *)
    2 : { simpl in *. congruence. }
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
    intros (fp & phl & FP & POP & GFM).
    exploit MM. eauto.
    eapply must_init_sound; eauto.
    intros (BM & FULL). destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2. inv BM.
    exists fp0, (phl++[ph_deref]). repeat apply conj.
    (* prove ofs' = 0 *)
    inv H; simpl in *; try congruence.
    simpl in *. inv H0. rewrite LOAD in H1. inv H1.
    rewrite Ptrofs.unsigned_zero.    
    econstructor; eauto.
    (* wt_footprint *)
    eapply place_footprint_wt in FP. rewrite PTY in FP. inv FP. 
    (* simpl. auto. *)
    simpl in *. congruence.
    (* path_of_place *)
    econstructor. auto.
    erewrite get_footprint_map_app; eauto.
    simpl. auto.
Admitted.

Lemma eval_place_unchanged: forall fpm m1 m2 le own b ofs fp p
        (MM: mmatch ce fpm m1 le own)
        (PFP: place_footprint ce fpm le p b ofs fp)
        (UNC: Mem.unchanged_on (fun b1 ofs1 => ~ In b1 (footprint_flat fp)
                                            /\ (b1 <> b \/ ~ ofs <= ofs1 < ofs + sizeof ce (typeof_place p))) m1 m2),
        eval_place ce le m2 p b (Ptrofs.repr ofs).
Admitted.

Lemma eval_place_determinate: forall ce le m p b1 b2 ofs1 ofs2,
    eval_place ce le m p b1 ofs1 ->
    eval_place ce le m p b2 ofs2 ->
    b1 = b2 /\ ofs1 = ofs2.
Admitted.


(* Lemma eval_place_no_mem_error: forall e m p own fpm *)
(*     (MM: mmatch ce fpm m e own) *)
(*     (WFOWN: wf_own_env own) *)
(*     (WT: wt_place (env_to_tenv e) ce p) *)
(*     (* evaluating the address of p does not require that p is *)
(*     owned. Shallow own is used in bmatch *) *)
(*     (POWN: place_dominator_own own p = true) *)
(*     (ERR: eval_place_mem_error ce e m p), *)
(*     False. *)
(* Proof. *)
(*   induction p; simpl; intros. *)
(*   (* Plocal *) *)
(*   - inv ERR. *)
(*   (* Pfield *) *)
(*   - inv ERR. eapply IHp; eauto. *)
(*     inv WT. auto. *)
(*   (* Pderef *) *)
(*   - inv ERR. *)
(*     (* eval p error *) *)
(*     + eapply IHp. 1-3: eauto. *)
(*       inv WT. auto. *)
(*       eapply wf_own_dominator. auto. auto. *)
(*       auto. *)
(*     (* deref error *) *)
(*     + inv WT. *)
(*       (* p is owned *) *)
(*       assert (OWN: is_owned own p = true) by auto. *)
(*       exploit eval_place_sound. 1-4: eauto. *)
(*       eapply wf_own_dominator; auto. *)
(*       intros (fp & PFP). *)
(*       exploit MM; eauto. *)
(*       intros BM. inv H2. apply H0. *)
(*       (* case analysis of the p type *) *)
(*       destruct (typeof_place p); simpl in H4; try congruence. *)
(*       (* Box type *) *)
(*       * simpl in H. inv H. inv BM. *)
(*         eapply Mem.load_valid_access; eauto. *)
(*         simpl in TY. congruence. *)
(*       (* reference type *) *)
(*       * admit. *)
(*   (* Pdowncast *) *)
(*   - inv ERR. *)
(*     (* eval_place p error *) *)
(*     + eapply IHp. 1-3: eauto. *)
(*       inv WT. auto. *)
(*       eapply wf_own_dominator; eauto. *)
(*       auto. *)
(*     (* load tag error *) *)
(*     + inv WT. *)
(*       assert (OWN: is_owned own p = true) by auto. *)
(*       exploit eval_place_sound. 1-4: eauto. *)
(*       eapply wf_own_dominator; eauto. *)
(*       intros (fp & PFP). *)
(*       exploit MM; eauto. rewrite H5. intros BM. *)
(*       inv BM. *)
(*       eapply H3. eapply Mem.load_valid_access; eauto. *)
(*       simpl in TY. congruence. *)
(*       (* auto. *) *)
(*       (* eapply place_dominator_shallow_own_shallow_prefix. eauto. *) *)
(*       (* unfold is_shallow_prefix. simpl. destruct (place_eq p p); try congruence. *) *)
(*       (* simpl. eapply orb_true_r. *) *)
(*       (* intros (p' & ABS & SUBP). *) *)
(*       (* (* The block of p' is valid block *) *) *)
(*       (* eapply MM in ABS. destruct ABS as (PERM & BM). *) *)
(*       (* (* show that the location of tag is valid *) *) *)
(*       (* eapply H3. *) *)
(*       (* red. split. *) *)
(*       (* * eapply Mem.range_perm_implies with (p1:= Freeable). *) *)
(*       (*   red. intros. eapply PERM. *) *)
(*       (*   exploit subplace_in_range; eauto. *) *)
(*       (*   assert (SZTAGLE: size_chunk Mint32 <= sizeof ce (typeof_place p)). *) *)
(*       (*   { rewrite H5. simpl. *) *)
(*       (*     rewrite H6. erewrite co_consistent_sizeof; eauto. *) *)
(*       (*     rewrite H8. simpl. *) *)
(*       (*     generalize (sizeof_variant_ge4 ce (co_members co)). intros A. *) *)
(*       (*     assert (ALGE: co_alignof co > 0). *) *)
(*       (*     { exploit co_alignof_two_p. intros (n & COAL). *) *)
(*       (*       rewrite COAL. apply two_power_nat_pos. } *) *)
(*       (*     generalize (align_le (sizeof_variant ce (co_members co)) _ ALGE). *) *)
(*       (*     lia. } *) *)
(*       (*   lia. *) *)
(*       (*   constructor. *) *)
(*       (* * exploit subplace_align; eauto. *) *)
(*       (*   assert (AL: (align_chunk Mint32 | alignof ce (typeof_place p))). *) *)
(*       (*   { rewrite H5. simpl. *) *)
(*       (*     rewrite H6. erewrite co_consistent_alignof; eauto. *) *)
(*       (*     rewrite H8. simpl. *) *)
(*       (*     (* easy but tedious *) *) *)
(*       (*     exploit alignof_composite_two_p'. *) *)
(*       (*     intros (n & AL). erewrite AL. *) *)
(*       (*     rewrite two_power_nat_equiv. *) *)
(*       (*     replace 4 with (2 ^ 2) by lia. *) *)
(*       (*     unfold Z.max. *) *)
(*       (*     destruct (2 ^ 2 ?= (2 ^ Z.of_nat n)) eqn:  LE. *) *)
(*       (*     eapply Z.divide_refl. *) *)
(*       (*     (* case 2^2 < 2 ^ n *) *) *)
(*       (*     eapply Z.pow_lt_mono_r_iff in LE. *) *)
(*       (*     exploit Z.le_exists_sub. eapply Z.lt_le_incl. *) *)
(*       (*     eauto. intros (p0 & PEQ & PLE). rewrite PEQ. *) *)
(*       (*     rewrite Z.pow_add_r. eapply Z.divide_factor_r. *) *)
(*       (*     auto. lia. lia. *) *)
(*       (*     eapply Nat2Z.is_nonneg. *) *)
(*       (*     eapply Z.divide_refl. } *) *)
(*       (*   intros ALTY. *) *)
(*       (*   eapply Z.divide_trans. eauto. *) *)
(*       (*   eauto. *) *)
(* Admitted. *)

(* This lemma proves two properties (should be separated): one is the
updated footprint map still satisfies mmatch and the other is the
sem_wt_loc in the moved place *)
Lemma move_place_mmatch: forall fpm1 m1 m2 e own1 own2 p b ofs fp
    (MM: mmatch ce fpm1 m1 e own1)
    (* p owns the ownership chain *)
    (MP: move_place own1 p = own2)
    (PFP: place_footprint ce fpm1 e p b ofs fp)
    (* we allow modify the block in fp because the moved out block may
    not be received by some place *)
    (UNC: Mem.unchanged_on (fun b _ => ~ In b (footprint_flat fp)) m1 m2),
    (* (PH: path_of_place ce p id phl), *)
    (* exists fpm2, clear_footprint_map id phl fpm1 = Some fpm2 *)
    exists fpm2, mmatch ce fpm2 m2 e own2.
Admitted.

Lemma movable_place_sem_wt: forall ce fp fpm m e own p b ofs init uninit universe
    (MM: mmatch ce fpm m e own)    
    (* p owns the ownership chain *)    
    (POWN: must_movable ce init uninit universe p = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: place_footprint ce fpm e p b ofs fp),
    sem_wt_loc ce m fp b ofs (typeof_place p)
.
(* with movable_struct_field_sem_wt: forall fpm m e own p orgs id ofs fpl fid fty co n ffp fofs b init uninit universe *)
(*         (MM: mmatch ce fpm m e own) *)
(*         (PTY: typeof_place p = Tstruct orgs id) *)
(*         (PFP: place_footprint ce fpm e p b ofs (fp_struct fpl)) *)
(*         (POWN: must_movable init uninit universe p = true) *)
(*         (SOUND: sound_own own init uninit universe) *)
(*         (CO: ce ! id = Some co) *)
(*         (TAG: field_tag fid (co_members co) = Some n) *)
(*         (FTY: field_type fid (co_members co) = OK fty) *)
(*         (FFP: list_nth_z fpl n = Some ffp) *)
(*         (FOFS: field_offset ce fid co.(co_members) = OK fofs), *)
(*     sem_wt_loc ce m ffp b (ofs + fofs) fty. *)
Proof.
  intros ce0; pattern ce0. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold must_movable, must_movable_fix in *.
  erewrite unroll_Fix in *.
  destruct (typeof_place p) eqn: PTY; simpl in POWN; try congruence.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). rewrite PTY in BM. inv BM.
    econstructor; eauto.    
  (* Tbox *)
  - destruct (must_init init uninit universe p) eqn: PINIT; try congruence.
    (* adhoc generalization *)
    generalize dependent p. generalize dependent b.
    generalize dependent fp. generalize dependent ofs.
    induction t; intros; simpl in *; try congruence.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). rewrite PTY in BM. inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      assert (PFP1: place_footprint ce1 fpm e (Pderef p Tunit) b1 0 fp0).
      { econstructor; eauto.
        eapply place_footprint_wt in PFP. inv PFP. rewrite PTY in H.
        inv H. auto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & FULL1). simpl in BM1. inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    (* The same as Tunit case *)
    + admit.
    + admit.
    + admit.
    (* Induction case *)
    + destruct (must_init init uninit universe (Pderef p (Tbox t))) eqn: INIT2; try congruence.
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). rewrite PTY in BM. inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      eapply IHt; eauto. simpl. auto.
      econstructor; eauto.
      eapply place_footprint_wt in PFP. inv PFP. rewrite PTY in H. inv H.
      auto.
    + (* destruct (ce1!i) eqn: CO. unfold get_composite in POWN. erewrite CO in POWN. *)
      destruct (get_composite ce1 i) eqn: GCE; try congruence. subst.
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). rewrite PTY in BM. inv BM; simpl in *; try congruence.
      rewrite P in *.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      (* assert (PFP1: place_footprint ce1 fpm e (Pderef p Tunit) b1 0 fp0). *)
      (* { econstructor; eauto. *)
      (*   eapply place_footprint_wt in PFP. inv PFP. rewrite PTY in H. *)
      (*   inv H. auto. } *)
      (** Use IH  *)
      destruct (must_init init uninit universe (Pderef p (Tstruct l id1))) eqn: INIT2; try congruence. admit.
      (** Do not know how to prove  *)
      admit.
      simpl. rewrite P. auto.
      (* eapply sem_wt_struct. *)
      (* exploit IH. eapply PTree_removeR. eauto. *)
      (* (* How to prove remove a composite does not invalidate mmatch *) *)

      
      
      (* exploit MM. eauto. eapply must_init_sound; eauto. *)
      (* intros (BM1 & FULL1). simpl in BM1. inv BM1; simpl in *; try congruence. *)
      (* econstructor; simpl; eauto. *)
    + admit.

  (* Tstruct *)
  - 
      
  induction fp using strong_footprint_ind; intros.

  (* induction fp; intros. *)
  (* empty footprint *)
  - assert (OWN: is_owned own p = true).
    { eapply must_movable_is_; eauto. }
    exploit MM. eauto. auto.
    intros BM. inv BM.
    eapply sem_wt_base; eauto.
  (* fp_box *)
  - assert (OWN: is_owned own p = true).
    { eapply must_movable_is_owned; eauto. }
    exploit MM. eauto. auto.
    intros BM. inv BM.
    econstructor. simpl. eauto.
    eauto.
    econstructor; auto.
    (* To prove the heap block is semantically well typed, use I.H. *)
    replace ty with (typeof_place (Pderef p ty)) by auto.
    eapply IHfp. eauto.
    (* prove *p is movable *)
    2: eauto.
    eapply must_movable_prefix. eauto. eauto.
    unfold is_prefix. simpl. destruct place_eq at 2. simpl. intuition. congruence.
    (* prove place_footprint *)
    econstructor. eauto.
    eapply place_footprint_wt in PFP. inv PFP.
    rewrite <- H in H0. inv H0. auto.
  (* fp_struct *)
  - assert (OWN: is_owned own p = true).
    { eapply must_movable_is_owned; eauto. }
    exploit MM. eauto. auto.
    intros BM. inv BM.
    eapply sem_wt_struct. eauto.
    intros. exploit FMATCH. 1-3: eauto.
    intros (ffp1 & NTH & BM1).
    replace fty with (typeof_place (Pfield p fid fty)) by auto.
    eapply H. eapply list_nth_z_in. eauto.
    eauto. 2: eauto.
    eapply must_movable_prefix. eauto. eauto.
    unfold is_prefix. simpl. destruct place_eq at 2. simpl. intuition. congruence.
    (* place_footprint *)
    econstructor; eauto.
    (* wt_footprint *)
    eapply place_footprint_wt in PFP.
    inv PFP. rewrite <- H2 in H6. inv H6.
    exploit WFFP; eauto.
    intros (fp & NTH1 & WT).
    rewrite NTH in NTH1. inv NTH1.
    rewrite H3 in NTH. inv NTH. auto.
    (* eapply movable_struct_field_sem_wt; eauto. *)
  (* fp_enum *)
  - assert (OWN: is_owned own p = true).
    { eapply must_movable_is_owned; eauto. }
    exploit MM. eauto. auto.
    intros BM. inv BM.
    eapply sem_wt_enum. 1-2: eauto.
    intros. replace fty with (typeof_place (Pdowncast p fid fty)) by auto.
    eapply IHfp. eauto.
    (* Pdowncast is movable *)
    2: eauto.
    eapply must_movable_prefix. eauto. eauto.
    unfold is_prefix. simpl. destruct place_eq at 2. simpl. intuition. congruence.
    (* place_footprint *)
    econstructor; eauto.
    (* wt_footprint *)
    eapply place_footprint_wt in PFP. inv PFP.
    rewrite <- H in H3. inv H3.
    eapply WFFP; eauto.
Qed.

(** IMPORTANT TODO  *)
Lemma mmatch_move_place_sound: forall p fpm1 fpm2 m le own phs
    (MM: mmatch ce fpm1 m le own)
    (SFM: set_footprint_map ce phs fp_emp fpm1 = Some fpm2)
    (POP: path_of_place ce p phs),
    (* valid_owner makes this proof difficult *)
    mmatch ce fpm2 m le (move_place own (valid_owner p)).
Proof.
  intros. constructor.
  - intros p1 b1 ofs1 fp1 PFP OWN.
    eapply mmatch_shallow. eauto.
    admit.
    admit.
  - intros p1 b1 ofs1 fp1 PFP OWN.
    eapply mmatch_deep. eauto.
Admitted.

(** Wrong way to prove by induction!  *)
(*   induction p; intros. *)
(*   - inv POP.  simpl in *. *)
(*     destruct (fpm1 ! i) eqn: FPM; try congruence. inv SFM. *)
(*     constructor. *)
(*     + intros p b1 ofs1 fp1 PFP OWN.       *)
(*       destruct (peq (local_of_place p) i); subst. *)
(*       * unfold is_init, move_place in OWN. simpl in OWN. *)
(*         (* require some well typedness?? *) *)
(*         admit. *)
(*       * eapply mmatch_shallow. eauto. *)
(*         (* set different local is noninterference *) *)
(*         admit. admit. *)
(*     + intros p b1 ofs1 fp1 PFP OWN. unfold is_movable in OWN. *)
(*       eapply andb_true_iff in OWN. destruct OWN as (UNI & MOVE). *)
(*       destruct (peq (local_of_place p) i); subst. *)
(*       * unfold move_place, is_init, remove_place in *. simpl in *. *)
(*         eapply Paths.for_all_2 in MOVE. *)
(*         eapply Paths.exists_2 in UNI. destruct UNI as (p' & IN & PRE). *)
(*         exploit MOVE. eapply Paths.filter_3. red. solve_proper. *)
(*         eauto. auto. *)
(*         intros MEM. eapply Paths.mem_2 in MEM. erewrite PathsMap.gsspec in MEM. *)
(*         erewrite <- is_prefix_same_local in MEM; eauto. destruct peq; try congruence. *)
(*         2-3 : red; solve_proper. *)
(*         eapply Paths.filter_2 in MEM.  *)
(*         (** TODO: Plocal (local_of_place p) t is prefix of p and derive contradition *) *)
(*         admit. red. solve_proper. *)
(*       * admit. *)

(*   - simpl. inv POP. *)
(* Admitted. *)


Lemma footprint_map_gss: forall p phs fpm1 fp1 fp2 ce le
  (WT: wt_place le ce p)
  (POP: path_of_place ce p phs)
  (WTFP1: wt_footprint ce (typeof_place p) fp2)
  (GFP: get_footprint_map phs fpm1 = Some fp1),
  exists fpm2, set_footprint_map ce phs fp2 fpm1 = Some fpm2
          /\ get_footprint_map phs fpm2 = Some fp2.
Admitted.
    
(** dereferce a semantically well typed location produces well typed value *)
Lemma deref_sem_wt_loc_sound: forall m fp b ofs ty v
    (WT: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs) ty)
    (DE: deref_loc ty m b ofs v),
    sem_wt_val ce m fp v ty.
Proof.
  intros. destruct ty; inv WT; inv DE; simpl in *; try congruence.
  (* struct *)
  - econstructor. eapply sem_wt_struct; eauto.
  (* enum *)
  - econstructor. eapply sem_wt_enum; eauto.
Qed.


(* The result of eval_expr is semantically well typed *)

(* The footprint must be fp_emp in pexpr *)
Lemma eval_pexpr_sem_wt: forall fpm m le own pe v init uninit universe
    (MM: mmatch ce fpm m le own)
    (EVAL: eval_pexpr ce le m pe v)
    (SOUND: sound_own own init uninit universe)
    (CHECK: move_check_pexpr init uninit universe pe = true),
    sem_wt_val ce m fp_emp v (typeof_pexpr pe).
Admitted.

Lemma eval_expr_sem_wt: forall fpm1 m le own1 own2 e v init uninit universe
    (MM: mmatch ce fpm1 m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (EVAL: eval_expr ce le m e v)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_expr init uninit universe e = true)
    (OWN: move_place_option own1 (moved_place e) = own2)
    (WFENV: wf_env ce fpm1 le)
    (WT: wt_expr le ce e),
  (** TODO: how to relate fp and fpm2 ? We should show that they are disjoint *)
  exists fp fpm2, sem_wt_val ce m fp v (typeof e)
             (* If expr is pure expr, fp is fp_emp and not from any phs *)
             (* /\ get_footprint_map phs fpm1 = Some fp *)
             (* /\ clear_footprint_map ce phs fpm1 = Some fpm2 *)
             /\ mmatch ce fpm2 m le own2
             /\ wf_env ce fpm2 le
             (* footprint disjointness *)
             /\ list_disjoint (footprint_flat fp) (flat_fp_map fpm2).
Proof.
  intros. destruct e.
  (* Emoveplace *)
  - simpl in *. inv EVAL. inv WT. inv H2.
    eapply andb_true_iff in CHECK. destruct CHECK as (DONW & MOVE).
    exploit eval_place_sound; eauto.        
    intros (pfp & phl & PFP & POP & GFM).
    (* location of p is sem_wt *)
    exploit movable_place_sem_wt; eauto.
    intros WT_LOC. 
    (* deref sem_wt location *)
    exploit deref_sem_wt_loc_sound; eauto. intros WT_VAL.
    (* get and set of footprint_map *)
    exploit footprint_map_gss; eauto. eapply wt_fp_emp.
    intros (fpm2 & SFPM & GFPM).        
    exploit mmatch_move_place_sound; eauto. intros MM1.
    exists pfp, fpm2. repeat apply conj; auto.
    (* wf_env *)
    constructor. intros.
    destruct (peq (local_of_place p) id).
    subst.
    (** set a wt_footprint in a wt_footprint is still wt *)
    admit.
    exploit wf_env_footprint; eauto.
    intros (fp & GFPM1 & WFFP). exists fp. split; auto.
    (** set (local_of_place p) unchanges the footprint of id *)
    admit.
    (** use GFP: get norepet footprint_map is disjoint  *)
    admit.
  - exists fp_emp, fpm1. simpl in *. subst.
    inv EVAL.
    exploit eval_pexpr_sem_wt; eauto. intros VWT.
    repeat apply conj; auto.
    red. intros. inv H.
Admitted.

Lemma sem_cast_sem_wt: forall v1 v2 ty1 ty2 m fp
    (CAST: RustOp.sem_cast v1 ty1 ty2 = Some v2)
    (WT: sem_wt_val ce m fp v1 ty1),
    sem_wt_val ce m fp v2 ty2.
Admitted.

(* Lemma eval_exprlist_sem_wt: forall fpm1 m le own1 own2 al tyl vl *)
(*     (MM: mmatch ce fpm1 m le own1) *)
(*     (EVAL: eval_exprlist ce le m al tyl vl) *)
(*     (OWN: own_check_exprlist own1 al = Some own2), *)
(*   exists fpl fpm2, sem_wt_val_list ce m fpl vl (type_list_of_typelist tyl) *)
(*         /\ mmatch ce fpm2 m le own2. *)
(* Admitted. *)


(* (* assign_loc remains sound. We need a more general one *) *)

(* Lemma assign_loc_sem_wt: forall ce m1 m2 fp v ty b ofs *)
(*         (WT: sem_wt_val ce m1 fp v ty) *)
(*         (AS: assign_loc ce ty m1 b ofs v m2), *)
(*         sem_wt_loc ce m2 fp b (Ptrofs.unsigned ofs) ty. *)
(* Admitted. *)

(** Important Lemma  *)
(* Consider assign to a variant? *)
Lemma assign_loc_sound: forall fpm1 m1 m2 own1 own2 b ofs v p vfp pfp e ty phl
    (MM: mmatch ce fpm1 m1 e own1)
    (TY: ty = typeof_place p)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val ce m1 vfp v ty)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: place_footprint ce fpm1 e p b (Ptrofs.unsigned ofs) pfp)
    (GET: get_footprint_map (local_of_place p, phl) fpm1 = Some pfp)
    (PATH: path_of_place ce p (local_of_place p, phl))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (* type of place is not enum *)
    (NOTENUM: forall orgs id, typeof_place p <> Tvariant orgs id)
    (NOREP: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_flat vfp) (flat_fp_map fpm1)),
  exists fpm2, set_footprint_map ce (local_of_place p, phl) vfp fpm1 = Some fpm2
          /\ place_footprint ce fpm2 e p b (Ptrofs.unsigned ofs) vfp
          /\ mmatch ce fpm2 m2 e own2
          /\ list_norepet (flat_fp_map fpm2).
Proof.
Admitted.


(* lemma assign_variant_sound: forall fpm1 m1 m2 m3 own1 own2 b ofs v p fp e ty orgs id fofs co fid tag *)
(*     (MM: mmatch ce fpm1 m1 e own1) *)
(*     (WT: sem_wt_val ce m1 fp v ty) *)
(*     (EP: eval_place ce e m1 p b ofs) *)
(*     (CKAS: own_check_assign own1 p = Some own2) *)
(*     (WTP: wt_place (env_to_tenv e) ce p) *)
(*     (TYP: typeof_place p = Tvariant orgs id) *)
(*     (CO: ce ! id = Some co) *)
(*     (FTY: field_type fid co.(co_members) = OK ty) *)
(*     (TAG: field_tag fid co.(co_members) = Some tag) *)
(*     (AS: assign_loc ce ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v m2) *)
(*     (STAG: Mem.store Mint32 m2 b (Ptrofs.unsigned ofs) (Vint (Int.repr tag)) = Some m3),     *)
(*    exists fpm2, mmatch ce fpm2 m3 e own2. *)
(* Admitted. *)


(* (** Similar to Frame Rule in separation logic?  *) *)
(* (* mmatch is preserved if its footprint is unchanged *) *)
(* Lemma unchanged_mem_preserves_mmatch: forall m1 m2 e own fpm *)
(*   (MM: mmatch ce fpm m1 e own) *)
(*   (UNC: Mem.unchanged_on (fun b _ => In b ((footprint_of_env e) ++ flat_fp_map fpm)) m1 m2), *)
(*     mmatch ce fpm m2 e own. *)
(* Admitted. *)


(* (** Properties of function_entry *) *)
(* Lemma function_entry_sound: forall m1 m2 fpl vl tyl f own le *)
(*     (WT: sem_wt_val_list ce m1 fpl vl tyl) *)
(*     (ENTRY: function_entry ge f vl m1 le m2 own), *)
(*   exists fpm, mmatch ce fpm m2 le own *)
(*          /\ wf_own_env own. *)
(* Admitted. *)

(* (* sound_cont is preserved if its footprint is unchanged *) *)

(* (* Similar to non-interference properties? *) *)
Lemma sound_cont_unchanged: forall m1 m2 fpf k an body cfg next cont brk nret
  (SOUND: sound_cont an body cfg k next cont brk nret m1 fpf)
  (UNC: Mem.unchanged_on (fun b _ => In b (flat_fp_frame fpf)) m1 m2),
    sound_cont an body cfg k next cont brk nret m2 fpf.
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
    sound_state s.
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

(* Lemma step_dropplace_sound: forall s1 t s2, *)
(*     sound_state s1 -> *)
(*     step_dropplace ge s1 t s2 -> *)
(*     sound_state s2. *)
(* Proof. *)
(*   intros s1 t s2 SOUND STEP. *)
(*   inv STEP. *)
(*   (* step_dropplace_init1 *) *)
(*   - inv SOUND. *)
(*     econstructor; eauto. *)
(*     econstructor. inv DP. inv SPLIT; eauto. *)
(*   (* step_dropplace_init2 *) *)
(*   - inv SOUND. *)
(*     econstructor; eauto. *)
(*     (** TODO: prove the split places are owned *) *)
(*     admit. *)
(*   (* step_dropplace_box *) *)
(*   - inv SOUND. *)
(*     inv DP. *)
(*     simpl in OWN. *)
(*     eapply andb_true_iff in OWN. *)
(*     destruct OWN as (POWN & LOWN). *)
(*     (* similar to move a place *) *)
(*     exploit eval_place_sound. 1-3: eauto. *)
(*     (** TODO: well typedness of the place  *) *)
(*     admit. *)
(*     eapply wf_own_dominator; eauto. *)
(*     intros (pfp & PFP). *)
(*     (* drop p is similar to move p *) *)
(*     exploit path_of_eval_place; eauto. intros (phl & PH). *)
(*     (* we use the more general move_place_mmatch *) *)
(*     exploit move_place_mmatch; eauto. *)
(*     instantiate (1 := m'). *)
(*     (** TODO: free b' does not change the memory outside pfp because *)
(*     b' is in the pfp *) *)
(*     admit. *)
(*     intros (fpm' & MM'). *)
(*     econstructor; eauto. *)
(*     (** TODO: use sound_cont_unchanged *) *)
(*     instantiate (1 := fpf). *)
(*     admit. *)
(*     (** TODO: to prove the norepet, we need to specify the fpm' in move_place_mmatch *) *)
(*     admit. *)
(*     (* accessibility *) *)
(*     instantiate (1:=sg). admit. *)
(*     (* some property of sound_drop_state *) *)
(*     admit. *)
(*     (* property of wf_own_env *) *)
(*     admit. *)
(*   (* step_dropplace_struct *) *)
(*   - inv SOUND. *)
(*     inv DP. *)
(*     (* easy: movable is owned *) *)
(*     assert (POWN: is_owned own p = true) by admit.  *)
(*     (* show that (b,ofs) is sem_wt of Tstruct and prove the soundness *)
(*     of members *) *)
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
(*   (* step_dropplace_struct *)     *)
(*   - admit. *)
(*   (* step_dropplace_next *) *)
(*   - inv SOUND. inv DP. *)
(*     econstructor; eauto. *)
(*     econstructor. auto. *)
(*   (* step_dropplace_return *) *)
(*   - inv SOUND. *)
(*     econstructor; eauto. *)
(* Admitted. *)

Ltac simpl_getIM IM :=
  generalize IM as IM1; intros;
  inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst;
  try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *.
    
Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    Step L s1 t s2 ->
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP. simpl in STEP.
  inv STEP.
  (* assign sound *)
  - inv SOUND. inv STMT. simpl in TR.    
    simpl_getIM IM.
    destruct (move_check_expr mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    destruct (move_check_assign mayinit mayuninit universe p) eqn: MOVE2; try congruence.
    inv TR.
    exploit eval_expr_sem_wt; eauto.
    admit.
    intros (vfp & phs & fpm2 & WT1 & GFP & CLFP & MM1 & DIS1).
    exploit sem_cast_sem_wt; eauto.
    intros WT2.
    exploit eval_place_sound; eauto.
    (** TODO: wf_env, wt_place, sound_own *)
    1-3: admit.
    intros (pfp & phl & PFP & POP & GFM).    
    exploit assign_loc_sound; eauto.
    (** TODO: wt_place  *)
    admit.
    intros (fpm3 & SFP & MM3).
    (* sound_state *)
    econstructor; eauto.
    econstructor.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    fail.
      
    admit.
    (* norepet *)
    admit.
    (* accessibility *)
    instantiate (1 := sg).
    admit.
    (* wf_own_env: show own_check_expr and own_check_assign preserve wf_own_env *)
    admit.
  (* assign_variant sound *)
  - inv SOUND.
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WT1 & MM1).
    exploit sem_cast_sem_wt; eauto.
    intros WT2.
    (** TODO: prove that the address of p does not change *)
    assert (PADDR3: eval_place (globalenv se prog) le m2 p b ofs).
    { exploit eval_place_sound. eapply PADDR1. eauto.
      (* own2 is wf_own_env *)
      admit.
      (* wt_place *)
      admit.
      unfold own_check_assign in CHKASSIGN.
      destruct (place_dominator_own own2 p); auto; try congruence.
      intros (pfp & PFP).
      (* use eval_place_unchanged *)
      exploit eval_place_unchanged; eauto.
      instantiate (1 := m2).
      (** TODO: assign_loc unchanged_on *)
      assert (ASUNC: Mem.unchanged_on (fun b0 ofs0 => b0 <> b \/ ~ Ptrofs.unsigned ofs <= ofs0 < Ptrofs.unsigned ofs + fofs) m1 m2). admit.
      eapply Mem.unchanged_on_implies. eauto.
      intros b0 ofs0 (A & B) C.
      destruct B; auto. right.
      (* easy: to prove fofs < sizeof ce (typeof_place p) *)
      admit.
      rewrite Ptrofs.repr_unsigned. auto. }
    (* b=b1 by the determinism of eval_place *)
    exploit eval_place_determinate. eapply PADDR2. eapply PADDR3.
    intros (A & B). subst.
    (** Use assign_variant_sound *)
    clear PADDR2 PADDR3.
    exploit assign_variant_sound;eauto.
    (* wt_place *)
    admit.
    intros (fpm3 & MM3).
    econstructor; eauto.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    admit.
    (* norepet *)
    admit.
    (* accessibility *)
    instantiate (1 := sg).
    admit.
    (* wf_own_env: show own_check_expr and own_check_assign preserve wf_own_env *)
    admit.
  (* step_box sound *)
  - inv SOUND.
    (* how to prove alloc a block and modify this block does not *)
(*     affect mmatch? Maybe we can use mmatch_unchanged *)
    assert (MM3: mmatch ce fpm m3 le own1).
    { eapply unchanged_mem_preserves_mmatch. eauto.
      (* modify the fresh block unchange m1 *)
      admit. }
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WT1 & MM3').
    exploit sem_cast_sem_wt; eauto.
    intros WT2.
    assert (MM4: mmatch ce fpm2 m4 le own2).
    { eapply unchanged_mem_preserves_mmatch. eauto.
      (* modify the fresh block unchange m3 *)
      admit. }
    (** show assign the value to the new allocated block would create a *)
(*         well-typed location *)
    exploit assign_loc_sem_wt; eauto. rewrite Ptrofs.unsigned_zero.
    intros WTLOC.
    (* show the box pointer is sem_wt *)
    assert (WTVAL: sem_wt_val ce m4 (fp_box b vfp) (Vptr b Ptrofs.zero) (Tbox ty)).
    { econstructor. auto.
      (* show b is freeable *)
      admit. }
    exploit assign_loc_sound. eapply MM4. 1-2: eauto.
    rewrite H. eauto.
    eauto. eauto.
    (* wt_place *)
    admit. rewrite H. congruence.
    intros (fpm3 & MM5).
    econstructor; eauto.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    admit.
    (* norepet *)
    admit.
    (* accessibility *)
    instantiate (1 := sg).
    admit.
    (* wf_own_env: show own_check_expr and own_check_assign preserve wf_own_env *)
    admit.
  (** NOTEASY: step_to_dropplace sound *)
  - inv SOUND.
    exploit split_drop_place_sound; eauto.
    intros SOUNDSPLIT.
    econstructor; eauto.
    econstructor. auto.
  (* step_in_dropplace sound *)
  - eapply step_dropplace_sound; eauto.
  (* step_dropstate sound *)
  - eapply step_drop_sound; eauto.
  (* step_storagelive sound *)
  - admit.
  (* step_storagedead sound *)
  - admit.
  (* step_call sound *)
  - inv SOUND.
    exploit eval_exprlist_sem_wt; eauto.
    intros (fpl & fpm2 & WT & MM2).
    econstructor. 1-3: eauto.
    (* sound_cont *)
    instantiate (1 := fpf_func le fpm2 fpf).
    econstructor. eauto. auto.
    (* wf_own_env *)
    admit.
    eauto.
    (* norepeat *)
    admit.
    (* accessibility *)
    instantiate (1 := sg).
    admit.
  (* step_internal_function sound *)
  - inv SOUND.
    exploit function_entry_sound; eauto.
    intros (fpm & MM & WFOWN).
    econstructor; eauto.
    (* prove sound_cont *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    (* prove unchanged_on of function_entry *)
    admit.
    (* new allocated blocks are disjoint with the frames *)
    admit.
    instantiate (1 := sg).
    (* accessibility *)
    admit.
    
(* (* Admitted. *) *)

(* Lemma reachable_state_sound: forall s, *)
(*     (* What about after external? *) *)
(*     reachable L s -> sound_state s. *)
(* Admitted. *)

Lemma external_sound_progress: forall s q,
    sound_state s ->
    at_external ge s q ->
    exists wA, symtbl_inv wt_rs wA se /\ query_inv wt_rs wA q /\
            forall r, reply_inv wt_rs wA r ->
                 (exists s', after_external s r s').
Admitted.

Lemma external_sound_preserve: forall s s' q r wA,
    sound_state s ->
    at_external ge s q ->
    query_inv wt_rs wA q ->
    reply_inv wt_rs wA r ->
    after_external s r s' ->
    sound_state s'.
Admitted.

Lemma final_sound_progress: forall s r,
    sound_state s ->
    final_state s r ->
    reply_inv wt_rs w r.
Admitted.

End BORCHK.

(** Specific definition of partial safe *)
Definition partial_safe ge (L: lts li_rs li_rs state) (s: state) : Prop :=
  not_stuck L s \/ step_mem_error ge s.

(* I is the generic partial safe invariant *)
Lemma move_check_module_safe (I: invariant li_rs) se p:
  Genv.valid_for (erase_program (program_of_program p)) se -> 
  move_check_program p = OK p ->
  module_safe_se (semantics p) I I (partial_safe (globalenv se p)) se ->
  module_safe_se (semantics p) (inv_compose I wt_rs) (inv_compose I wt_rs) not_stuck se.
Proof.  
  intros VSE MVCHK PSAFE.
  (* prove by progress and preservation *)
  eapply module_safe_se_components_sound.
  assert (CE_CON: composite_env_consistent (globalenv se p)).
  { eapply build_composite_env_consistent.
    instantiate (1 := (prog_types p)). destruct p; simpl; eauto. }
  set (IS := fun '(w1, w2) s =>
               reachable I I (semantics p se) w1 s
               /\ partial_safe (globalenv se p) (semantics p se) s
               /\ sound_state p w2 se s).
  eapply (Module_safe_se_components _ _ (semantics p) (inv_compose I wt_rs) (inv_compose I wt_rs) se IS).
  (* preservation *)
  - intros (w1 & w2) (SINV1 & SINV2). 
    exploit PSAFE; eauto. intros PLSAFE.
    constructor.
    (* preserve step *)
    + intros s t s' (REACH & PS & SOUND) STEP.
      red. repeat apply conj.
      * eapply step_reachable; eauto.
      * eapply reachable_safe; eauto.
        eapply step_reachable; eauto.
      (* step sound_state *)
      * eapply step_sound; eauto.        
    (* initial *)
    + intros q s VQ (QINV1 & QINV2) INIT.
      red. repeat apply conj.
      * eapply initial_reach; eauto.
        eapply star_refl.
      * eapply reachable_safe; eauto.
        eapply initial_reach; eauto.
        eapply star_refl.
      (* initial sound state *)
      * eapply initial_state_sound; eauto.
    (* external preserve *)
    + intros s s' q r (w1' & w2') (REACH & PS & SOUND) ATEXT (QINV1 & QINV2) (RINV1 & RINV2) AFEXT.
      red. repeat apply conj.
      * eapply external_reach; eauto.
        eapply star_refl.
      * eapply reachable_safe; eauto.
        eapply external_reach; eauto.
        eapply star_refl.
      (** external sound state: may be very difficult!!! *)
      * eapply external_sound_preserve; eauto.
  (* progress *)
  - intros (w1 & w2) (SINV1 & SINV2). 
    exploit PSAFE; eauto. intros PLSAFE.
    constructor.
    (* sound_state progress *)
    + intros s (REACH & PS & SOUND).
      unfold partial_safe in PS. destruct PS; auto.
      (** proof of no memory error in sound state *)
      admit.
    (* initial_progress *)
    + intros q VQ (QINV1 & QINV2).
      eapply initial_progress; eauto.
    (* external_progress *)
    + intros s q (REACH & PS & SOUND) ATEXT.
      exploit (@external_progress li_rs); eauto.
      intros (w1' & SINV1' & QINV1' & RINV1).
      (** To construct wA: prove sound_state external progress *)
      exploit external_sound_progress; eauto.
      intros (w2' & SINV2' & QINV2' & RINV2').
      exists (w1',w2'). repeat apply conj; eauto.
      intros r (RINV1'' & RINV2'').
      eapply RINV2'. auto.            
    (* final_progress *)
    + intros s r (REACH & PS & SOUND) FINAL.
      exploit (@final_progress li_rs); eauto.
      intros RINV1.
      (** final_progress of sound_state  *)
      exploit final_sound_progress; eauto.
      intros RINV2. constructor; auto.      
Admitted.

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
