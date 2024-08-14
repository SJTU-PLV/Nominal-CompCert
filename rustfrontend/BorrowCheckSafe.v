Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface Invariant.
Require Import Rusttypes RustlightBase.
Require Import RustIR BorrowCheckDomain BorrowCheckPolonius.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown.

Import ListNotations.

(* Some simple type checking (move to Rusttyping.v) *)

Definition type_deref (ty: type) : res type :=
  match ty with
  | Tbox tyelt
  | Treference _ _ tyelt => OK tyelt
  | _ => Error (msg "type_deref error")
  end.

Definition typenv := PTree.t type.

Section TYPING.

Variable te: typenv.
Variable ce: composite_env.

Inductive wt_place : place -> Prop :=
| wt_local: forall id ty,
    te ! id = Some ty ->
    wt_place (Plocal id ty)
| wt_deref: forall p ty,
    wt_place p ->
    type_deref (typeof_place p) = OK ty ->
    wt_place (Pderef p ty)
| wt_field: forall p ty fid co orgs id,
    wt_place p ->
    typeof_place p = Tstruct orgs id ->
    ce ! id = Some co ->
    field_type fid co.(co_members) = OK ty ->
    co.(co_sv) = Struct ->
    wt_place (Pfield p fid ty)
| wt_downcast: forall p ty fid co orgs id,
    wt_place p ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    field_type fid co.(co_members) = OK ty ->
    co.(co_sv) = TaggedUnion ->
    wt_place (Pdowncast p fid ty)
.

End TYPING.

Definition env_to_tenv (e: env) : typenv :=
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
    inv WT. rewrite TY in H3. inv H3.
    rewrite CO in H4. inv H4.
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
    inv WT. rewrite TY in H3. inv H3.
    rewrite CO in H4. inv H4.
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
    inv WT. rewrite TY in H3. inv H3. rewrite CO in H4. inv H4.
    assert (LE: fofs + sizeof ce fty <= sizeof ce (typeof_place p')).
    { rewrite TY. simpl. rewrite CO.
      erewrite co_consistent_sizeof; eauto.
      rewrite H6. simpl.
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
    inv WT. rewrite TY in H3. inv H3. rewrite CO in H4. inv H4.
    assert (LE: fofs + sizeof ce fty <= sizeof ce (typeof_place p')).
    { rewrite TY. simpl. rewrite CO.
      erewrite co_consistent_sizeof; eauto.
      rewrite H6. simpl.
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
| fp_box (b: block) (fp: footprint) (* A heap block storing values that occupy footprint fp *)
| fp_struct (fpl: list footprint)
| fp_enum (tag: Z) (fp: footprint)
.

(* Footprint used in interface *)
Definition flat_footprint : Type := list block.

(* Similar to inject_separated *)
Definition flat_footprint_separated (fp1 fp2: flat_footprint) (m : mem) : Prop :=
  forall b, ~ In b fp1 ->
       In b fp2 ->
       ~ Mem.valid_block m b.

Fixpoint footprint_flat (fp: footprint) : flat_footprint :=
  match fp with
  | fp_emp => nil
  | fp_box b fp' =>
      b :: footprint_flat fp'
  | fp_struct fpl =>
      concat (map footprint_flat fpl)
  | fp_enum _ fp =>
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
  

(* Similar to ProjectElem in rustc *)
Variant path : Type :=
  | ph_deref
  | ph_field (idx: Z)
  | ph_downcast (idx: Z).

(* relate place and path *)
Inductive path_of_place (ce: composite_env) : place -> ident -> list path -> Prop :=
| path_local: forall id ty,
    path_of_place ce (Plocal id ty) id nil
| path_deref: forall p ty l id
    (PH: path_of_place ce p id l),
    path_of_place ce (Pderef p ty) id (l ++ [ph_deref])
| path_field: forall p orgs id sid co idx fid fty l
    (TY: typeof_place p = Tstruct orgs sid)
    (CO: ce ! sid = Some co)
    (FID: list_nth_z co.(co_members) idx = Some (Member_plain fid fty))
    (PH: path_of_place ce p id l),
    path_of_place ce (Pfield p fid fty) id (l ++ [ph_field idx])
| path_downcast: forall p orgs id sid co idx fid fty l
    (TY: typeof_place p = Tvariant orgs sid)
    (CO: ce ! sid = Some co)
    (FID: list_nth_z co.(co_members) idx = Some (Member_plain fid fty))
    (PH: path_of_place ce p id l),
    path_of_place ce (Pdowncast p fid fty) id (l ++ [ph_downcast idx]).

(* Use path to set/remove a footprint *)

Definition set_footprint_path (ph: path) (v: footprint) (fp: footprint) : option footprint :=
  match ph, fp with
  | ph_deref, fp_box b fp' =>
      Some fp'
  | ph_field idx, fp_struct fpl =>
      list_nth_z fpl idx
  | ph_downcast idx1, fp_enum idx2 fp' =>
      if Z.eq_dec idx1 idx2 then
        Some fp'
      else
        None
  | _, _ => None
  end.

(** Prove some properties w.r.t list_nth_z  *)
Fixpoint list_set_nth_z {A: Type} (l: list A) (n: Z) (v: A)  {struct l}: list A :=
  match l with
  | nil => nil
  | hd :: tl => if zeq n 0 then (v :: tl) else hd :: (list_set_nth_z tl (Z.pred n) v)
  end.

(* set footprint [v] in the path [ph] of footprint [fp] *)
Fixpoint set_footprint (phl: list path) (v: footprint) (fp: footprint) : option footprint :=
  match phl with
  | [] => Some v
  | ph :: l =>
        match ph, fp with
        | ph_deref, fp_box b fp1 =>
            match set_footprint l v fp1 with
            | Some fp2 =>
                Some (fp_box b fp2)
            | None => None
            end                
        | ph_field idx, fp_struct fpl =>
            match list_nth_z fpl idx with
            | Some fp1 =>
                match set_footprint l v fp1 with
                | Some fp2 =>
                    Some (fp_struct (list_set_nth_z fpl idx fp2))
                | None => None
                end
            | None => None
            end
        | ph_downcast idx1, fp_enum idx2 fp1 =>
            if Z.eq_dec idx1 idx2 then
              match set_footprint l v fp1 with
              | Some fp2 =>
                  Some (fp_enum idx2 fp2)
              | None => None
              end
            else None
        | _, _ => None
        end
  end.

Definition clear_footprint (phl: list path) (fp: footprint) : option footprint :=
  set_footprint phl fp_emp fp.

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

Definition scalar_type (ty: type) : bool :=
  match ty with
  | Tunit
  | Tint _ _
  | Tlong _
  | Tfloat _
  | Tfunction _ _ _ _ _
  | Tarray _ _ => true
  | _ => false
  end.

(* Semantics well typed location is mutually defined with semantics
well typed value *)
Inductive sem_wt_loc (ce: composite_env) (m: mem) : footprint -> block -> Z -> type -> Prop :=
| sem_wt_base: forall ty b ofs fp chunk v
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val ce m fp v ty),
    sem_wt_loc ce m fp b ofs ty
| sem_wt_struct: forall b ofs co fpl orgs id
    (CO: ce ! id = Some co)   
    (* all fields are semantically well typed *)
    (FWT: forall n fid fty ffp fofs,
        nth_error co.(co_members) n = Some (Member_plain fid fty) ->
        nth_error fpl n = Some ffp ->
        field_offset ce fid co.(co_members) = OK fofs ->
        sem_wt_loc ce m ffp b (ofs + fofs) fty),
    sem_wt_loc ce m (fp_struct fpl) b ofs (Tstruct orgs id)
| sem_wt_enum: forall fp b ofs orgs id co tagz
    (CO: ce ! id = Some co)    
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz)))
    (FWT: forall fid fty fofs,
        list_nth_z co.(co_members) tagz = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK fofs ->
        sem_wt_loc ce m fp b (ofs + fofs) fty),
    sem_wt_loc ce m (fp_enum tagz fp) b ofs (Tvariant orgs id)


with sem_wt_val (ce: composite_env) (m: mem) : footprint -> val -> type -> Prop :=
| wt_val_unit:
  sem_wt_val ce m fp_emp (Vint Int.zero) Tunit
| wt_val_int: forall sz si n,
    Cop.cast_int_int sz si n = n ->
    sem_wt_val ce m fp_emp (Vint n) (Tint sz si)
| wt_val_float: forall n,
    sem_wt_val ce m fp_emp (Vfloat n) (Tfloat Ctypes.F64)
| wt_val_single: forall n,
    sem_wt_val ce m fp_emp (Vsingle n) (Tfloat Ctypes.F32)
| wt_val_long: forall si n,
    sem_wt_val ce m fp_emp (Vlong n) (Tlong si)
| wt_val_box: forall b ty fp
    (** Box pointer must be in the starting point of a block *)
    (* The value stored in (b,0) has type ty and occupies footprint fp *)
    (WTLOC: sem_wt_loc ce m fp b 0 ty)
    (VALID: Mem.range_perm m b 0 (sizeof ce ty) Cur Freeable),
    sem_wt_val ce m (fp_box b fp) (Vptr b Ptrofs.zero) (Tbox ty)
(* TODO *)
(* | wt_val_ref: forall b ofs ty org mut, *)
(*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *)
| wt_val_struct: forall id orgs b ofs fp
    (WTLOC: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs) (Tstruct orgs id)),
    sem_wt_val ce m fp (Vptr b ofs) (Tstruct orgs id)
| wt_val_enum: forall id orgs b ofs fp
    (WTLOC: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs) (Tvariant orgs id)),
    sem_wt_val ce m fp (Vptr b ofs) (Tvariant orgs id)
.

Inductive sem_wt_val_list (ce: composite_env) (m: mem) : list footprint -> list val -> list type -> Prop :=
| sem_wt_val_nil:
    sem_wt_val_list ce m nil nil nil
| sem_wt_val_cons: forall fpl fp vl tyl v ty,
    sem_wt_val_list ce m fpl vl tyl ->
    sem_wt_val ce m fp v ty ->
    sem_wt_val_list ce m (fp::fpl) (v::vl) (ty::tyl)
.

Lemma sem_wt_val_in_wt_loc: forall ce m fp b ofs ty v
    (WT: sem_wt_loc ce m fp b ofs ty)
    (LOAD: deref_loc ty m b (Ptrofs.repr ofs) v),
    sem_wt_val ce m fp v ty.
Admitted.

(** Semantics Interface *)

(** ** Rust Interface *)

Record rust_signature : Type := mksignature {
  sig_generic_origins: list origin;
  sig_origins_relation: list origin_rel;
  sig_args: list type;
  sig_res: type;
  sig_cc: calling_convention;
  sig_comp_env: composite_env;
}.
  
Record rust_query :=
  rsq {
    rsq_vf: val;
    rsq_sg: rust_signature;
    rsq_args: list val;
    rsq_mem: mem;
  }.

Record rust_reply :=
  rsr {
    rsr_retval: val;
    rsr_mem: mem;
  }.

Canonical Structure li_rs :=
  {|
    query := rust_query;
    reply := rust_reply;
    entry := rsq_vf;
  |}.

Inductive wt_rs_world :=
  rsw (sg: rust_signature) (fp: flat_footprint) (m: mem).


Inductive wt_rs_query : wt_rs_world -> rust_query -> Prop :=
| wt_rs_query_intro: forall sg m vf args fpl fp
    (DIS: footprint_disjoint_list fpl)
    (WT: sem_wt_val_list (sig_comp_env sg) m fpl args (sig_args sg))
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
    rsw_acc (rsw sg fp m) (rsw sg fp' m').

Inductive wt_rs_reply : wt_rs_world -> rust_reply -> Prop :=
| wt_rs_reply_intro: forall rfp m rv sg fp
    (WT: sem_wt_val (sig_comp_env sg) m rfp rv (sig_res sg))
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

(* relation between the selector and the (stmt, cont) pair *)
Inductive match_instr_stmt (body: statement) : instruction -> statement -> cont -> Prop :=
| sel_stmt_base: forall sel n s k,
    select_stmt body sel = Some s ->
    match_instr_stmt body (Isel sel n) s k
| sel_stmt_seq: forall sel n s1 s2 k,
    match_instr_stmt body (Isel sel n) s1 (Kseq s2 k) ->
    match_instr_stmt body (Isel sel n) (Ssequence s1 s2) k
| sel_stmt_kseq: forall sel n s k,
    match_instr_stmt body (Isel sel n) s k ->
    match_instr_stmt body (Isel sel n) Sskip (Kseq s k)
| sel_stmt_ifthenelse: forall e n1 n2 s1 s2 k,
    match_instr_stmt body (Icond e n1 n2) (Sifthenelse e s1 s2) k
| sel_stmt_loop: forall n s k,    
    match_instr_stmt body (Inop n) (Sloop s) k
| sel_stmt_break: forall n k,    
    match_instr_stmt body (Inop n) Sbreak k
| sel_stmt_continue: forall n k,
    match_instr_stmt body (Inop n) Scontinue k
.


(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* A footprint in a function frame *)
Definition fp_map := PTree.t footprint.

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

Definition set_footprint_map (id: ident) (phl: list path) (v: footprint) (fpm: fp_map) : option fp_map :=
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

Definition clear_footprint_map (id: ident) (phl: list path) (fpm: fp_map) : option fp_map :=
  set_footprint_map id phl fp_emp fpm.


Section MATCH.

Variable ce: composite_env.
Variable fpm: fp_map.

(* The location and footprint of a place *)
(* Fro place_footprint e p b ofs fp, it means that the location of [p]
is (b, ofs) and the value stored in [p] occupies the footprint [fp] *)
Inductive place_footprint (e: env) : place -> block -> Z -> footprint -> Prop :=
| place_footprint_deref: forall p fp ofs1 b1 b2 ty
    (* (b1, ofs1) *-> (b2, 0) *)
    (FP: place_footprint e p b1 ofs1 (fp_box b2 fp)),
    (* For now, we do not consider reference, so the location of *p is
    always in the start of a block b2 *)
    place_footprint e (Pderef p ty) b2 0 fp
| place_footprint_field: forall p fp ofs b orgs id fid fty co fofs fpl tagz
    (FP: place_footprint e p b ofs (fp_struct fpl))
    (TY: typeof_place p = Tstruct orgs id)
    (CO: ce!id = Some co)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (* find the location of fid to get the footprint *)
    (TAG: field_tag fid co.(co_members) = Some tagz)
    (FFP: list_nth_z fpl tagz = Some fp),
    place_footprint e (Pfield p fid fty) b (ofs + fofs) fp
| place_footprint_enum: forall p fp fid fty tagz b ofs orgs id co fofs
    (FP: place_footprint e p b ofs (fp_enum tagz fp))
    (TY: typeof_place p = Tvariant orgs id)
    (CO: ce!id = Some co)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (TAGZ: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty)),
    place_footprint e (Pdowncast p fid fty) b (ofs + fofs) fp
| place_footprint_local: forall id fp ty b
    (FP: fpm ! id = Some fp)
    (STK: e ! id = Some (b, ty)),
    place_footprint e (Plocal id ty) b 0 fp
.


(* The value stored in m[b, ofs] is consistent with the type of p. [p]
is owned. *)
Inductive bmatch (m: mem) (b: block) (ofs: Z) (p: place) (own: own_env) : footprint -> type -> Prop :=
| bm_box: forall ty b1 fp
    (* valid resource. If the loaded value is not a pointer, it is a *)
(*     type error instead of a memory error *)
    (* N.B. A compilcated situation is that [p] may fully own the *)
(*     resource so that the all the blocks of the owned chain it points *)
(*     to are not in the range of [own] environment. In this case, we *)
(*     should show that the ownership chain is semantics well typed. But *)
(*     if [p] just partially own the resoruce, we need to explicitly show *)
(*     that the owner of the block it points to is [*p]. *)
    (LOAD: Mem.load Mptr m b ofs = Some (Vptr b1 Ptrofs.zero))
    (VRES:
        (** Case1: p is partially owned *)
        (* p owns the location it points to. Box pointer must points *)
(*         to the start of a block and *p is the owner of this block *)
        (* (is_shallow_owned own p = true -> (ofs1 = Ptrofs.zero /\ abs b1 = Some (Pderef p ty))) *)
        (** Case2: p is fully owned: own b1 is None. How to get the *)
        (* footprint of this semantics well typedness? *)
        (* /\ (is_deep_owned own p = true -> *)
        (*    (exists fp, place_footprint p fp *)
      (*         /\ sem_wt_loc ce m fp b ofs (typeof_place p)))), *)
      Mem.range_perm m b1 0 (sizeof ce ty) Cur Freeable),
    bmatch m b ofs p own (fp_box b1 fp) (Tbox ty)
| bm_struct: forall co fpl orgs id
    (CO: ce ! id = Some co)
    (* all fields are semantically well typed *)
    (FMATCH: forall n fid fty ffp fofs,
        nth_error co.(co_members) n = Some (Member_plain fid fty) ->
        nth_error fpl n = Some ffp ->
        field_offset ce fid co.(co_members) = OK fofs ->
        bmatch m b (ofs + fofs) (Pfield p fid fty) own ffp fty),
    bmatch m b ofs p own (fp_struct fpl) (Tstruct orgs id)
| bm_enum: forall fp orgs id co tagz
    (CO: ce ! id = Some co)
    (* Interpret the field by the tag and prove that it is well-typed *)
    (* [p] whose value has footprint (fp_enum tagz fp) is actually has
    tag tagz *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz))) 
    (FMATCH: forall fid fty fofs,        
        list_nth_z co.(co_members) tagz = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK fofs ->
        bmatch m b (ofs + fofs) (Pdowncast p fid fty) own fp fty),
    bmatch m b ofs p own (fp_enum tagz fp) (Tvariant orgs id)
| bm_scalar: forall ty chunk v
    (TY: scalar_type ty = true)
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val ce m fp_emp v ty),
    bmatch m b ofs p own fp_emp ty
(** TODO: bm_reference  *)
.

(** Some bmatch properties *)

(* bmatch under subplace *)

(* Lemma bmatch_subplace: forall p p' ofs ofs' own m b, *)
(*     bmatch m b ofs p own (typeof_place p) -> *)
(*     subplace ce p p' ofs' -> *)
(*     bmatch m b (ofs + ofs') p' own (typeof_place p'). *)
(* Admitted. *)

(** TODO: support alias analysis domain *)
Definition mmatch (m: mem) (e: env) (own: own_env) : Prop :=
  forall p b ofs fp,
    place_footprint e p b ofs fp ->
    (* We only consider the initialized place *)
    is_owned own p = true ->
    bmatch m b ofs p own fp (typeof_place p).
    
    
(* Record wf_footprint (e: env) : Prop := *)
(*   { wf_local_env: forall id b ty, *)
(*       e ! id = Some (b, ty) -> *)
(*       abs b = Some (Plocal id ty); *)

(*     (* all mapped places are in the range of Ptrofs.max_unsigned *) *)
(*     wf_place_size: forall b p, *)
(*       abs b = Some p -> *)
(*       sizeof ce (typeof_place p) < Ptrofs.max_unsigned *)
(*   }. *)

End MATCH.


(** Some auxilary definitions *)

(* Well-formed ownership environment *)

Record wf_own_env (own: own_env) : Prop := {
    (* A place is owned then all its dominators are owned *)
    wf_own_dominator: forall p,
      is_owned own p = true ->
      place_dominator_own own p = true;

    wf_own_universe:
      PathsMap.eq (PathsMap.lub own.(own_init) own.(own_uninit)) own.(own_universe)

  }.


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

Lemma dominator_of_shallow_owned_place: forall own p,
    wf_own_env own ->    
    is_shallow_owned own p = true ->
    place_dominator_shallow_own own p = true.
Proof.
  intros own p WF SO.
  unfold place_dominator_shallow_own.
  unfold is_shallow_owned in *. eapply andb_true_iff in SO.
  destruct SO as (A & B).
  exploit wf_own_dominator. eauto. eauto. intros C.
  unfold place_dominator_own in C. destruct (place_dominator p) eqn: DOM; auto.
  rewrite C. erewrite andb_true_l.
  eapply Paths.exists_1. red. Morphisms.solve_proper.
  eapply Paths.exists_2 in B.
  unfold Paths.Exists in *. destruct B as (E & F & G).
  exists E. split. auto.
  erewrite <- place_dominator_local. eauto.
  auto.
  eapply is_prefix_strict_trans.
  eapply place_dominator_strict_prefix. eauto.
  auto.
  red. Morphisms.solve_proper.
Qed.  

Lemma place_dominator_shallow_own_shallow_prefix: forall own p p',
    place_dominator_shallow_own own p = true ->
    is_shallow_prefix p' p = true ->
    place_dominator_shallow_own own p' = true.
Admitted.

Section BORCHK.

Variable prog: program.
Variable w: inv_world wt_rs.
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Hypothesis INV: symtbl_inv wt_rs w se.
Let L := semantics prog se.
Let ge := globalenv se prog.

(* composite environment *)
Let ce := ge.(genv_cenv).

Hypothesis CONSISTENT: composite_env_consistent ce.

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
  deref_loc_rec_footprint m b ofs fp [] b ofs nil fp
| deref_loc_rec_footprint_cons: forall ty tys fp2 b1 ofs1 b2 phl
    (* The location (b1, ofs1) has footprint (fp_box b2 fp2) and the
    location of (b2,0) has footprint fp2 *)
    (FP: deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl (fp_box b2 fp2))
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 (Ptrofs.zero)))
    (* block b2 is freeable *)
    (FREE: Mem.range_perm m b2 0 (sizeof ce ty) Cur Freeable),
    (* how to relate ty and b *)
    deref_loc_rec_footprint m b ofs fp (ty :: tys) b2 0 (phl ++ [ph_deref]) fp2.

(* Invariant of deref_loc_rec_footprint *)

Lemma deref_loc_rec_footprint_inv: forall m b1 b2 ofs1 ofs2 fp1 fp2 tyl phl,
    deref_loc_rec_footprint m b1 ofs1 fp1 tyl b2 ofs2 phl fp2 ->
    exists fp3, clear_footprint phl fp1 = Some fp3 /\
             (* store fp2 to fp3 *)
             set_footprint phl fp2 fp3 = Some fp1 /\
             deref_loc_rec_footprint m b1 ofs1 fp3 tyl b2 ofs2 phl fp_emp
.
Admitted.

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
  | Kcall (Some p) _ _ _ _ =>
      Some (typeof_place p)
  | Kcall None _ _ _ _ =>
      None
  | Kstop => Some ttop
  | Kseq _ k
  | Kloop _ k
  (* impossible? *)
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k => typeof_cont_call ttop k
  end.

(* Every former element is the children of letter elements *)
Inductive sound_split_fully_own_place : list place -> Prop :=
| sound_split_fully_nil: sound_split_fully_own_place []
| sound_split_fully_cons: forall p l
    (CHILDREN: Forall (fun p' => is_prefix p p' = false) l) 
    (SOUND: sound_split_fully_own_place l),
    sound_split_fully_own_place (p::l).

(* May be difficult: algebraic property of split_drop_place *)
Inductive sound_split_drop_place (own: own_env) : list (place * bool) -> Prop :=
| sound_split_drop_nil: sound_split_drop_place own []
| sound_split_drop_cons_full: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun elt => is_prefix p (fst elt) = false) l ->
    (* p is fully owned so that p is owned equivalent to p is movable *)
    is_owned own p = check_movable own p ->
    sound_split_drop_place own l ->
    sound_split_drop_place own ((p, true) :: l)
| sound_split_drop_cons_partial: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun elt => is_prefix p (fst elt) = false) l ->
    sound_split_drop_place own l ->
    sound_split_drop_place own ((p, false) :: l)
.
    
(* Inductive sound_drop_fully_owned (own: own_env) : option drop_place_state -> Prop := *)
(* | sound_drop_fully_owned_none: sound_drop_fully_owned own None *)
(* | sound_drop_fully_owned_comp: forall p l *)
(*     (* drop the head place does not affect the ownership status in the *)
(*     rest of the list *) *)
(*     (SOUND: sound_split_fully_own_place l) *)
(*     (OWN: forallb (is_owned own) l = true) *)
(*     (MOVE: check_movable own p = true) *)
(*     (* we should show that move out p should not affect the ownership *)
(*     of l *) *)
(*     (SEP: Forall (fun elt => is_prefix p elt = false) l), *)
(*     sound_drop_fully_owned own (Some (drop_fully_owned_comp p l)) *)
(* | sound_drop_fully_owned_box: forall l *)
(*     (SOUND: sound_split_fully_own_place l) *)
(*     (OWN: forallb (is_owned own) l = true), *)
(*     sound_drop_fully_owned own (Some (drop_fully_owned_box l)) *)
(* . *)

(* combine sound_drop_fully_owned, sound_split_drop_place and require
that st and ps are disjoint *)
Inductive sound_drop_place (own: own_env) (ps: list (place * bool)) : option drop_place_state -> Prop :=
| sound_drop_place_none: forall
    (SPLIT: sound_split_drop_place own ps),
    sound_drop_place own ps None
| sound_drop_place_comp: forall p l
    (SOUND: sound_split_fully_own_place (p::l))
    (OWN: forallb (is_owned own) l = true)
    (MOVE: check_movable own p = true)
    (SPLIT: sound_split_drop_place own ps)
    (* we should show that p and l are both disjoint with ps *)
    (SEP: Forall (fun p' => Forall (fun elt => is_prefix p' (fst elt) = false) ps) (p::l)),
    sound_drop_place own ps (Some (drop_fully_owned_comp p l))
| sound_drop_place_box: forall l
    (SOUND: sound_split_fully_own_place l)
    (OWN: forallb (is_owned own) l = true)
    (SPLIT: sound_split_drop_place own ps)
    (* we should show that l is disjoint with ps *)
    (SEP: Forall (fun p' => Forall (fun elt => is_prefix p' (fst elt) = false) ps) l),
    sound_drop_place own ps (Some (drop_fully_owned_box l))
.

(* Soundness of continuation: the execution of current function cannot
modify the footprint maintained by the continuation *)

Inductive sound_cont (m: mem) : fp_frame -> cont -> Prop :=
| sound_Kstop:
  sound_cont m fpf_emp Kstop
| sound_Kseq: forall s k fpf
    (SOUND: sound_cont m fpf k),
    sound_cont m fpf (Kseq s k)
| sound_Kloop: forall s k fpf
    (SOUND: sound_cont m fpf k),
    sound_cont m fpf (Kloop s k)
| sound_Kcall: forall p f e own k fpm fpf
    (MM: mmatch ce fpm m e own)
    (SOUND: sound_cont m fpf k)
    (WF: wf_own_env own),
    sound_cont m (fpf_func e fpm fpf) (Kcall p f e own k)
| sound_Kdropplace: forall f e own k fpm fpf ps st    
    (MM: mmatch ce fpm m e own)
    (SOUND: sound_cont m fpf k)
    (DP: sound_drop_place own ps st)
    (WF: wf_own_env own),
    sound_cont m (fpf_func e fpm fpf) (Kdropplace f st ps e own k)
| sound_Kdropstate: forall k fpf st co fp ofs b membs fpl id
    (CO: ce ! id = Some co)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) st fp)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (SOUND: sound_cont m fpf k),
    sound_cont m (fpf_drop fp fpl fpf) (Kdropcall id (Vptr b ofs) st membs k)
.


(** TODO: add syntactic well typedness in the sound_state and
sound_cont *)
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f s k e own m entry cfg pc instr (* ae Σ Γ Δ *) fpm fpf flat_fp sg
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (INSTR: cfg ! pc = Some instr)
    (MSTMT: match_instr_stmt f.(fn_body) instr s k)
    (* (CHK: borrow_check ce f = OK ae) *)
    (* (AS: ae ! pc = Some (AE.State Σ Γ Δ)) *)
    (MM: mmatch ce fpm m e own)
    (CONT: sound_cont m fpf k)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (* footprint is separated *)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc (snd w) (rsw sg flat_fp m))
    (* we need to maintain the well-formed invariant of own_env *)
    (WF: wf_own_env own),
    sound_state (State f s k e own m)
| sound_dropplace: forall f st drops k e own m fpm fpf flat_fp sg
    (MM: mmatch ce fpm m e own)
    (CONT: sound_cont m fpf k)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc (snd w) (rsw sg flat_fp m))
    (* every place in the drop_fully_owned state is owned *)
    (DP: sound_drop_place own drops st)
    (WF: wf_own_env own),
    (* no need to maintain borrow check domain in dropplace? But how
    to record the pc and next statement? *)
    sound_state (Dropplace f st drops k e own m)
| sound_dropstate: forall id co fp fpl b ofs st m membs k fpf flat_fp sg
    (CO: ce ! id = Some co)
    (* The key is how to prove semantics well typed can derive the
    following two properties *)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) st fp)
    (* all the remaining members are semantically well typed *)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (CONT: sound_cont m fpf k)
    (FLAT: flat_fp = flat_fp_frame (fpf_drop fp fpl fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc (snd w) (rsw sg flat_fp m)),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k flat_fp sg
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WT: sem_wt_val_list ce m fpl args (type_list_of_typelist tyargs))
    (CONT: sound_cont m fpf k)
    (FLAT: flat_fp = flat_fp_frame fpf)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc (snd w) (rsw sg flat_fp m)),
    sound_state (Callstate vf args k m)
| sound_returnstate: forall sg flat_fp m k retty rfp v
    (ACC: rsw_acc (snd w) (rsw sg flat_fp m))
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (sig_res sg) k = Some retty)
    (WT: sem_wt_val ce m rfp v retty)
    (SEP: list_disjoint flat_fp (footprint_flat rfp)),
    sound_state (Returnstate v k m)
.


Lemma path_of_eval_place: forall e m p b ofs
    (EVAL: eval_place ce e m p b ofs),
  exists phl, path_of_place ce p (local_of_place p) phl.
Admitted.

    
(** The address of a place is consistent with the abstracter. For now,
we do not consider reference *)
Lemma eval_place_sound: forall e m p b ofs own fpm
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch ce fpm m e own)
    (WFOWN: wf_own_env own)
    (WT: wt_place (env_to_tenv e) ce p)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: place_dominator_own own p = true),
  (* Do we need to specify the properties of fp? Do we need to show
  the permission of the location of p? *)
    exists fp, place_footprint ce fpm e p b (Ptrofs.unsigned ofs) fp.
    (* if consider reference, we cannot say that p is a subplace of
    p', instead we need to state that the owner p points to is a
    subplace of p' *)
(* Proof. *)
(*   induction 1; intros. *)
(*   (* Plocal *) *)
(*   - rewrite Ptrofs.unsigned_zero. *)
(*     exists (Plocal id ty). split. *)
(*     eapply wf_local_env; eauto. *)
(*     econstructor. *)
(*   (* Pfield *) *)
(*   - inv WT. *)
(*     eapply place_dominator_shallow_own_shallow_prefix with (p':= p) in POWN. *)
(*     exploit IHEVAL. 1-5: auto. *)
(*     intros (p' & ABS & SUBP). *)
(*     exists p'. split. auto. *)
(*     (* two type facts, reduce one *) *)
(*     rewrite H in H6. inv H6. rewrite H0 in H7. inv H7. *)
(*     (* *** Begin range proof *** *) *)
(*     (* Can we require that the size of p' is in the range of *)
(*     Ptrofs.max_unsigned, so that any subplace is in this range *)
(*     (including its successor) *) *)
(*     exploit wf_place_size; eauto. intros PSIZE. *)
(*     generalize (subplace_upper_bound _ _ _ _ _ SUBP CONSISTENT H5 (Z.lt_le_incl _ _ PSIZE)).    rewrite H. simpl. rewrite H0. *)
(*     erewrite co_consistent_sizeof; eauto. rewrite H9. simpl. *)
(*     assert (ALPOS: co_alignof co0 > 0). *)
(*     { exploit co_alignof_two_p. intros (n & ALPOW). *)
(*       rewrite ALPOW. rewrite two_power_nat_equiv. *)
(*       generalize (Nat2Z.is_nonneg n). intros A. *)
(*       exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia. *)
(*       eauto. lia. } *)
(*     generalize (align_le (sizeof_struct ce (co_members co0)) _ ALPOS). *)
(*     intros STRUCTSZ BOUND. *)
(*     exploit field_offset_in_range; eauto. intros (RANGE1 & RANGE2). *)
(*     generalize (Ptrofs.unsigned_range ofs). intros OFSRANGE. *)
(*     generalize (sizeof_pos ce ty). intros TYSZPOS. *)
(*     (* *** End range proof *** *) *)
(*     rewrite Ptrofs.add_unsigned. *)
(*     do 2 rewrite Ptrofs.unsigned_repr. *)
(*     econstructor. auto. eauto. eauto. *)
(*     eauto. *)
(*     (** dirty work: specify the requirement to prevent overflow *) *)
(*     lia. lia. lia. *)
(*     unfold is_shallow_prefix. eapply orb_true_intro. *)
(*     right. simpl. destruct (place_eq p p). auto. congruence.     *)
(*   (* Pdowncast *) *)
(*   - inv WT. *)
(*     eapply place_dominator_shallow_own_shallow_prefix with (p':= p) in POWN. *)
(*     exploit IHEVAL. 1-5: auto. *)
(*     intros (p' & ABS & SUBP). *)
(*     exists p'. split. auto. *)
(*     (* two type facts, reduce one *) *)
(*     rewrite H in H8. inv H8. rewrite H0 in H9. inv H9. *)
(*     (* *** Begin range proof *** *) *)
(*     exploit wf_place_size; eauto. intros PSIZE. *)
(*     generalize (subplace_upper_bound _ _ _ _ _ SUBP CONSISTENT H7 (Z.lt_le_incl _ _ PSIZE)).    rewrite H. simpl. rewrite H0. *)
(*     erewrite co_consistent_sizeof; eauto. rewrite H11. simpl. *)
(*     assert (ALPOS: co_alignof co0 > 0). *)
(*     { exploit co_alignof_two_p. intros (n & ALPOW). *)
(*       rewrite ALPOW. rewrite two_power_nat_equiv. *)
(*       generalize (Nat2Z.is_nonneg n). intros A. *)
(*       exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia. *)
(*       eauto. lia. } *)
(*     generalize (align_le (sizeof_variant ce (co_members co0)) _ ALPOS). *)
(*     intros ENUMSZ BOUND. *)
(*     exploit variant_field_offset_in_range; eauto. intros (RANGE1 & RANGE2). *)
(*     generalize (Ptrofs.unsigned_range ofs). intros OFSRANGE. *)
(*     generalize (sizeof_pos ce ty). intros TYSZPOS. *)
(*     (* *** End range proof *** *) *)
(*     rewrite Ptrofs.add_unsigned. *)
(*     do 2 rewrite Ptrofs.unsigned_repr. *)
(*     econstructor. auto. eauto. eauto. *)
(*     eauto. *)
(*     (** dirty work: specify the requirement to prevent overflow *) *)
(*     lia. lia. lia. *)
(*     (* shallow prefix *) *)
(*     unfold is_shallow_prefix. eapply orb_true_intro. *)
(*     right. simpl. destruct (place_eq p p). auto. congruence. *)
(*   (* Pderef *) *)
(*   - inv WT. *)
(*     exploit IHEVAL. eauto. eauto. eauto. eauto. *)
(*     (* place dominator is shallow owned *) *)
(*     unfold place_dominator_shallow_own in POWN. simpl in POWN. *)
(*     eapply dominator_of_shallow_owned_place. auto. auto. *)
(*     intros (p' & ABS & SUBP). *)
(*     eapply MM in ABS. destruct ABS as (A & B). *)
(*     (* p is a subplace of p' and p' bmatch implies p bmatch *) *)
(*     exploit bmatch_subplace; eauto. rewrite Z.add_0_l. intros BM. *)
(*     (* typeof_place p must be box/reference *) *)
(*     destruct (typeof_place p) eqn: TYP; simpl in *; try congruence. *)
(*     (* Tbox *) *)
(*     + inv BM. *)
(*       (* deref_loc and LOAD in sem_wt_loc say the same thing *) *)
(*       inv H; simpl in *; try congruence. inv H0. rewrite LOAD in H1. inv H1. *)
(*       inv H3. *)
(*       (* Now we need to say that p is shallow owned *) *)
(*       unfold place_dominator_shallow_own in POWN. simpl in POWN. *)
(*       destruct VRES as (C & D). *)
(*       eapply C in POWN. destruct POWN as (E & F). subst. *)
(*       exists (Pderef p ty). split. auto. *)
(*       rewrite Ptrofs.unsigned_zero. constructor. *)
(*       (* box is not scalar type *) *)
(*       simpl in H0. congruence. *)
(*     (* reference *) *)
(*     + admit. *)
Admitted.


Lemma eval_place_no_mem_error: forall e m p own fpm
    (MM: mmatch ce fpm m e own)
    (WFOWN: wf_own_env own)
    (WT: wt_place (env_to_tenv e) ce p)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: place_dominator_own own p = true)
    (ERR: eval_place_mem_error ce e m p),
    False.
Proof.
  induction p; simpl; intros.
  (* Plocal *)
  - inv ERR.
  (* Pfield *)
  - inv ERR. eapply IHp; eauto.
    inv WT. auto.
  (* Pderef *)
  - inv ERR.
    (* eval p error *)
    + eapply IHp. 1-3: eauto.
      inv WT. auto.
      eapply wf_own_dominator. auto. auto.
      auto.
    (* deref error *)
    + inv WT.
      (* p is owned *)
      assert (OWN: is_owned own p = true) by auto.
      exploit eval_place_sound. 1-4: eauto.
      eapply wf_own_dominator; auto.
      intros (fp & PFP).
      exploit MM; eauto.
      intros BM. inv H2. apply H0.
      (* case analysis of the p type *)
      destruct (typeof_place p); simpl in H4; try congruence.
      (* Box type *)
      * simpl in H. inv H. inv BM.
        eapply Mem.load_valid_access; eauto.
        simpl in TY. congruence.
      (* reference type *)
      * admit.
  (* Pdowncast *)
  - inv ERR.
    (* eval_place p error *)
    + eapply IHp. 1-3: eauto.
      inv WT. auto.
      eapply wf_own_dominator; eauto.
      auto.
    (* load tag error *)
    + inv WT.
      assert (OWN: is_owned own p = true) by auto.
      exploit eval_place_sound. 1-4: eauto.
      eapply wf_own_dominator; eauto.
      intros (fp & PFP).
      exploit MM; eauto. rewrite H5. intros BM.
      inv BM.
      eapply H3. eapply Mem.load_valid_access; eauto.
      simpl in TY. congruence.
      (* auto. *)
      (* eapply place_dominator_shallow_own_shallow_prefix. eauto. *)
      (* unfold is_shallow_prefix. simpl. destruct (place_eq p p); try congruence. *)
      (* simpl. eapply orb_true_r. *)
      (* intros (p' & ABS & SUBP). *)
      (* (* The block of p' is valid block *) *)
      (* eapply MM in ABS. destruct ABS as (PERM & BM). *)
      (* (* show that the location of tag is valid *) *)
      (* eapply H3. *)
      (* red. split. *)
      (* * eapply Mem.range_perm_implies with (p1:= Freeable). *)
      (*   red. intros. eapply PERM. *)
      (*   exploit subplace_in_range; eauto. *)
      (*   assert (SZTAGLE: size_chunk Mint32 <= sizeof ce (typeof_place p)). *)
      (*   { rewrite H5. simpl. *)
      (*     rewrite H6. erewrite co_consistent_sizeof; eauto. *)
      (*     rewrite H8. simpl. *)
      (*     generalize (sizeof_variant_ge4 ce (co_members co)). intros A. *)
      (*     assert (ALGE: co_alignof co > 0). *)
      (*     { exploit co_alignof_two_p. intros (n & COAL). *)
      (*       rewrite COAL. apply two_power_nat_pos. } *)
      (*     generalize (align_le (sizeof_variant ce (co_members co)) _ ALGE). *)
      (*     lia. } *)
      (*   lia. *)
      (*   constructor. *)
      (* * exploit subplace_align; eauto. *)
      (*   assert (AL: (align_chunk Mint32 | alignof ce (typeof_place p))). *)
      (*   { rewrite H5. simpl. *)
      (*     rewrite H6. erewrite co_consistent_alignof; eauto. *)
      (*     rewrite H8. simpl. *)
      (*     (* easy but tedious *) *)
      (*     exploit alignof_composite_two_p'. *)
      (*     intros (n & AL). erewrite AL. *)
      (*     rewrite two_power_nat_equiv. *)
      (*     replace 4 with (2 ^ 2) by lia. *)
      (*     unfold Z.max. *)
      (*     destruct (2 ^ 2 ?= (2 ^ Z.of_nat n)) eqn:  LE. *)
      (*     eapply Z.divide_refl. *)
      (*     (* case 2^2 < 2 ^ n *) *)
      (*     eapply Z.pow_lt_mono_r_iff in LE. *)
      (*     exploit Z.le_exists_sub. eapply Z.lt_le_incl. *)
      (*     eauto. intros (p0 & PEQ & PLE). rewrite PEQ. *)
      (*     rewrite Z.pow_add_r. eapply Z.divide_factor_r. *)
      (*     auto. lia. lia. *)
      (*     eapply Nat2Z.is_nonneg. *)
      (*     eapply Z.divide_refl. } *)
      (*   intros ALTY. *)
      (*   eapply Z.divide_trans. eauto. *)
      (*   eauto. *)
Admitted.

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

Lemma movable_place_sem_wt: forall fp fpm m e own p b ofs
    (MM: mmatch ce fpm m e own)
    (* p owns the ownership chain *)
    (POWN: check_movable own p = true)
    (PFP: place_footprint ce fpm e p b ofs fp),
    sem_wt_loc ce m fp b ofs (typeof_place p)

with movable_struct_field_sem_wt: forall fpm m e own p orgs id ofs fpl fid fty co n ffp fofs b
        (MM: mmatch ce fpm m e own)
        (PTY: typeof_place p = Tstruct orgs id)
        (PFP: place_footprint ce fpm e p b ofs (fp_struct fpl))
        (POWN: check_movable own (Pfield p fid fty) = true)
        (CO: ce ! id = Some co)
        (MEMB: nth_error co.(co_members) n = Some (Member_plain fid fty))
        (FFP: nth_error fpl n = Some ffp)
        (FOFS: field_offset ce fid co.(co_members) = OK fofs),
    sem_wt_loc ce m ffp b (ofs + fofs) fty.
               
Proof.
  (* prove the first lemma *)
  { 
  clear movable_place_sem_wt.
  induction fp; intros.
  (* empty footprint *)
  - assert (OWN: is_owned own p = true). admit.
    exploit MM. eauto. auto.
    intros BM. inv BM.
    eapply sem_wt_base; eauto.
  (* fp_box *)
  - assert (OWN: is_owned own p = true). admit.
    exploit MM. eauto. auto.
    intros BM. inv BM.
    econstructor. simpl. eauto.
    eauto.
    econstructor; auto.
    (* To prove the heap block is semantically well typed, use I.H. *)
    replace ty with (typeof_place (Pderef p ty)) by auto.
    eapply IHfp. eauto.
    (* prove *p is movable *)
    admit.
    econstructor. eauto.
  (* fp_struct *)
  - assert (OWN: is_owned own p = true). admit.
    exploit MM. eauto. auto.
    intros BM. inv BM.
    eapply sem_wt_struct. eauto.
    intros. exploit FMATCH. 1-3: eauto.
    intros BM.
    (* apply the second lemma *)
    eapply movable_struct_field_sem_wt. 1-3: eauto.
    (* check movable of this field *)
    instantiate (1:= fid).  admit.
    1-4: eauto.
  (* fp_enum *)
  - assert (OWN: is_owned own p = true). admit.
    exploit MM. eauto. auto.
    intros BM. inv BM.    
    eapply sem_wt_enum. 1-2: eauto.
    intros. replace fty with (typeof_place (Pdowncast p fid fty)) by auto.
    eapply IHfp. eauto.
    (* Pdowncast is movable *)
    admit.
    econstructor; eauto.
    
  }

  (* prove the second lemma *)
  { clear movable_struct_field_sem_wt.
    intros. replace fty with (typeof_place (Pfield p fid fty)) by auto.
    eapply movable_place_sem_wt; eauto.
    econstructor. 1-4 : eauto.
    (* some inversion properties of nth_error *)
    instantiate (1 := (Z.of_nat n)). admit.
    admit.
Admitted.

(* The result of eval_expr is semantically well typed *)

Lemma eval_pexpr_sem_wt: forall fpm m le own pe v
    (MM: mmatch ce fpm m le own)
    (EVAL: eval_pexpr ce le m pe v)
    (OWN: own_check_pexpr own pe = true),
    exists fp, sem_wt_val ce m fp v (typeof_pexpr pe).
Admitted.

Lemma eval_expr_sem_wt: forall fpm1 m le own1 own2 e v
    (MM: mmatch ce fpm1 m le own1)
    (EVAL: eval_expr ce le m e v)
    (OWN: own_check_expr own1 e = Some own2),
  (* how to relate fp and fpm2 ? *)
  exists fp fpm2, sem_wt_val ce m fp v (typeof e)
        /\ mmatch ce fpm2 m le own2.
Admitted.

Lemma sem_cast_sem_wt: forall v1 v2 ty1 ty2 m fp
    (CAST: RustOp.sem_cast v1 ty1 ty2 = Some v2)
    (WT: sem_wt_val ce m fp v1 ty1),
    sem_wt_val ce m fp v2 ty2.
Admitted.
  
(* assign_loc remains sound. We need a more general one *)

Lemma assign_loc_sound: forall fpm1 m1 m2 own1 own2 b ofs v p fp e ty
    (MM: mmatch ce fpm1 m1 e own1)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (WT: sem_wt_val ce m1 fp v ty)
    (EP: eval_place ce e m1 p b ofs)
    (CKAS: own_check_assign own1 p = Some own2),
    (* (PH: path_of_place ce p id phl), *)
  (* require some relation between abstracter and footprint_map *)
   (* set_footprint_map id phl fp fpm1 = Some fpm2 *)
   exists fpm2, mmatch ce fpm2 m2 e own2.
Admitted.

(** Similar to Frame Rule in separation logic?  *)
(* mmatch is preserved if its footprint is unchanged *)
Lemma unchanged_mem_preserves_mmatch: forall m1 m2 e own fpm
  (MM: mmatch ce fpm m1 e own)
  (UNC: Mem.unchanged_on (fun b _ => In b ((footprint_of_env e) ++ flat_fp_map fpm)) m1 m2),
    mmatch ce fpm m2 e own.
Admitted.

(* sound_cont is preserved if its footprint is unchanged *)

(* Similar to non-interference properties? *)
Lemma sound_cont_unchanged: forall m1 m2 fpf k
  (SOUND: sound_cont m1 fpf k)
  (UNC: Mem.unchanged_on (fun b _ => In b (flat_fp_frame fpf)) m1 m2),
  sound_cont m2 fpf k.
Admitted.

Lemma deref_loc_rec_no_mem_error: forall m b ofs tys fp b1 ofs1 phl fp1,
    deref_loc_rec_mem_error m b (Ptrofs.repr ofs) tys ->
    deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl fp1 ->
    False.
Admitted.

(** TODO: Maybe we should require that fp is disjoint because the memory is
changed during the drop *)
Lemma drop_box_rec_no_mem_error: forall m b ofs tys fp b1 ofs1 phl fp1,
    list_norepet (footprint_flat fp) ->
    drop_box_rec_mem_error ge b (Ptrofs.repr ofs) m tys ->
    deref_loc_rec_footprint m b ofs fp tys b1 ofs1 phl fp1 ->
    False.
Admitted.


Lemma sound_dropstate_no_mem_error: forall s,
    step_drop_mem_error ge s -> sound_state s -> False.
Proof.
  intros s ERR SOUND.
  inv ERR.
  (* step_dropstate_struct_error1 *)
  - inv SOUND.
    unfold ce in CO. rewrite CO in CO1. inv CO1.    
    (* GOAL: To show that deref_loc_rec_mem_error is impossible if
    (b1,ofs1) has footprint fp *)
    inv DROPMEMB.
    (* co1.(co_sv) = Struct *)
    + rewrite STRUCT in FOFS.
      unfold ce in FOFS0.
      rewrite FOFS in FOFS0. inv FOFS0.
      rewrite Ptrofs.add_unsigned in DEREF.
      (* some overflow constrain *)
      assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit.
      rewrite Ptrofs.unsigned_repr in DEREF; eauto.
      eapply deref_loc_rec_no_mem_error; eauto.
    (* co1.(co_sv) = TaggedUnion *)
    + admit.
  (* step_dropstate_enum_error1 *)
  - inv SOUND.
    unfold ce in CO. rewrite CO in CO1. inv CO1.
    inv DROPMEMB.
    (* co1.(co_sv) = Struct *)
    + rewrite STRUCT in FOFS.
      unfold ce in FOFS0.
      rewrite FOFS in FOFS0. inv FOFS0.
      rewrite Ptrofs.add_unsigned in DEREF.
      (* some overflow constrain *)
      assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit.
      rewrite Ptrofs.unsigned_repr in DEREF; eauto.
      eapply deref_loc_rec_no_mem_error; eauto.
    (* co1.(co_sv) = TaggedUnion *)
    + admit.
  (* step_dropstate_enum_error2: load tag error *)
  - inv SOUND.
    unfold ce in CO. rewrite CO in CO1. inv CO1.
    inv DROPMEMB.
    (* co1.(co_sv) = Struct *)
    + rewrite STRUCT in FOFS.
      unfold ce in FOFS0.
      rewrite FOFS in FOFS0. inv FOFS0.
      rewrite Ptrofs.add_unsigned in DEREF.
      (* some overflow constrain *)
      assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit.
      rewrite Ptrofs.unsigned_repr in DEREF; eauto.
      (** Prove that deref_loc_rec and deref_loc_rec_footprint get the same address *)
      exploit deref_loc_rec_footprint_eq; eauto.
      intros (A & B). subst.
      (* (b0,ofs0) is semantically well typed location, so load tag
      error is impossible *)
      inv WT.
      simpl in MODE. congruence.
      eapply TAG.
      eapply Mem.load_valid_access.
      (* some overflow constrain *)
      assert (OFSRANGE: 0 <= ofs0 <= Ptrofs.max_unsigned) by admit.
      rewrite Ptrofs.unsigned_repr; eauto.
    (* co1.(co_sv) = TaggedUnion *)
    + admit.
  (* step_dropstate_box_error *)
  - inv SOUND.
    unfold ce in CO. rewrite CO in CO1. inv CO1.
    inv DROPMEMB.
    (* co1.(co_sv) = Struct *)
    + rewrite STRUCT in FOFS.
      unfold ce in FOFS0.
      rewrite FOFS in FOFS0. inv FOFS0.
      rewrite Ptrofs.add_unsigned in DROPB.
      (* some overflow constrain *)
      assert (FOFSRANGE: 0 <= fofs0 <= Ptrofs.max_unsigned) by admit.
      rewrite Ptrofs.unsigned_repr in DROPB; eauto.
      (** show that drop_box_rec_mem_error is impossible if there is
      deref_loc_rec_footprint *)
      eapply drop_box_rec_no_mem_error; eauto.
      (* norepet proof *)
      admit.
    (* co1.(co_sv) = TaggedUnion *)
    + admit.
Admitted.

Lemma sound_dropplace_no_mem_error: forall s,
    step_dropplace_mem_error ge s -> sound_state s -> False.
Proof.
  intros s ERR SOUND.
  inv ERR.
  (* step_dropplace_box_error1 *)
  - inv SOUND. inv DP.
Admitted.

        
Lemma sound_state_no_mem_error: forall s,
    step_mem_error ge s -> sound_state s -> False .
Admitted.

(* Lemma initial_state_sound: forall q s, *)
(*     query_inv wt_rs w q -> *)
(*     Smallstep.initial_state L q s -> *)
(*     sound_state s. *)
(* Admitted. *)

Lemma step_drop_sound: forall s1 t s2,
    sound_state s1 ->
    step_drop ge s1 t s2 ->
    (* how to prove sound_state in dropstate? *)
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP.
  inv STEP.
  (* step_dropstate_init *)
  - inv SOUND.
    (* fp is fp_emp *)
    inv DROPMEMB.
    inv MEMBFP. rename H2 into MEMBFP. rename H3 into MEMBS.
    econstructor; eauto. instantiate (1 := a1).
    (** TODO: relation between member_footprint and drop_member_footprint *)
    admit.
    (* easy: list norepet *)
    admit.
    (* easy: accessibility *)
    instantiate (1 := sg). admit.
  (* step_dropstate_struct *)
  - inv SOUND.
    inv DROPMEMB.
    (* clear fp1 from fp *)
    exploit deref_loc_rec_footprint_inv; eauto.
    intros (fp3 & CLEAR & SET & FPREC).
    econstructor. eauto.
    econstructor.
    (** TODO: show the footprint of the members in co2 using (b0,ofs0)
    is sem_wt_loc *)
    admit.
    (* sound_cont *)
    instantiate (1 := (fpf_drop fp3 fpl fpf)).
    econstructor; eauto.
    econstructor; eauto.
    (* end of sound_cont *)
    (* construct the flat footprint *)
    eauto.
    (* easy: norepet *)
    admit.
    (* easy: accessibility *)
    admit.
  (* step_dropstate_enum *)
  - admit.
  (* step_dropstate_box (memory is updated) *)
  - inv SOUND.
    inv DROPMEMB.
    (** TODO: prove that drop_box_rec unchanged_on (In b fp) *)
    assert (UNC: Mem.unchanged_on (fun b _ => ~ In b (footprint_flat fp)) m m').
    admit.
    econstructor. eauto.
    econstructor.
    (* prove the soundness of the remaining fields members *)
    instantiate (1 := fpl). admit.
    (* sound_cont: use unchanged property *)
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    (* easy: prove the disjointness between fpf and fp *)
    admit.
    eauto.
    (* easy: norepet *)
    admit.
    (* easy: accessibility *)
    instantiate (1 := sg).
    admit.
  (* step_dropstate_return1 *)
  - inv SOUND.
    inv CONT.
    econstructor; eauto.
    (* easy: norepet *)
    admit.
    (* easy: accessibility *)
    instantiate (1 := sg).
    admit.
  (* step_dropstate_return1 *)
  - inv SOUND.
    inv CONT.
    econstructor; eauto.
    (* easy: norepet *)
    admit.
    (* easy: accessibility *)
    instantiate (1 := sg).
    admit.
Admitted.

Lemma step_dropplace_sound: forall s1 t s2,
    sound_state s1 ->
    step_dropplace ge s1 t s2 ->
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP.
  inv STEP.
  (* step_dropplace_init1 *)
  - inv SOUND.
    econstructor; eauto.
    econstructor. inv DP. inv SPLIT; eauto.
  (* step_dropplace_init2 *)
  - inv SOUND.
    econstructor; eauto.
    (** TODO: prove the split places are owned *)
    admit.
  (* step_dropplace_box *)
  - inv SOUND.
    inv DP.
    simpl in OWN.
    eapply andb_true_iff in OWN.
    destruct OWN as (POWN & LOWN).
    (* similar to move a place *)
    exploit eval_place_sound. 1-3: eauto.
    (** TODO: well typedness of the place  *)
    admit.
    eapply wf_own_dominator; eauto.
    intros (pfp & PFP).
    (* drop p is similar to move p *)
    exploit path_of_eval_place; eauto. intros (phl & PH).
    (* we use the more general move_place_mmatch *)
    exploit move_place_mmatch; eauto.
    instantiate (1 := m').
    (** TODO: free b' does not change the memory outside pfp because
    b' is in the pfp *)
    admit.
    intros (fpm' & MM').
    econstructor; eauto.
    (** TODO: use sound_cont_unchanged *)
    instantiate (1 := fpf).
    admit.
    (** TODO: to prove the norepet, we need to specify the fpm' in move_place_mmatch *)
    admit.
    (* accessibility *)
    instantiate (1:=sg). admit.
    (* some property of sound_drop_state *)
    admit.
    (* property of wf_own_env *)
    admit.
  (* step_dropplace_struct *)
  - inv SOUND.
    inv DP.
    (* easy: movable is owned *)
    assert (POWN: is_owned own p = true) by admit. 
    (* show that (b,ofs) is sem_wt of Tstruct and prove the soundness
    of members *)
    exploit eval_place_sound. 1-3: eauto.
    (** TODO: how to show p is syntactic well typed?  *)
    admit.
    eapply wf_own_dominator. auto.
    auto.
    intros (pfp & PFP).
    exploit movable_place_sem_wt; eauto.
    rewrite PTY. intros WT.
    (* prove sound_state *)
    econstructor; eauto.
    econstructor.
    (** TODO: use sem_wt_loc to prove member_footprint *)
    admit.
    (* sound_cont *)
    instantiate (1 := fpf_func le fpm fpf).
    econstructor.
    (** TODO: shrinking the own_env preserves mmatch *)
    admit.
    auto.
    (** TODO: sound_drop_place *)
    inv SOUND.
    econstructor. auto.
    (* show that move out p does not change the ownership of l *)
    admit.
    (* use SEP to prove this goal *)
    admit.
    inv SEP. auto.
    (* property of wf_own_env *)
    admit.
    (* norepet *)
    admit.
    (* accessibility *)
    admit.
  (* step_dropplace_struct *)    
  - admit.
  (* step_dropplace_next *)
  - inv SOUND. inv DP.
    econstructor; eauto.
    econstructor. auto.
  (* step_dropplace_return *)
  - inv SOUND.
    econstructor; eauto.
    (* some TBD *)
    admit. admit. admit.
Admitted.
    
Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    Step L s1 t s2 ->
    (* how to prove sound_state in dropstate? *)
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP. simpl in STEP.
  inv STEP.
  (* assign sound *)
  - inv SOUND.
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WT1 & MM1).
    exploit sem_cast_sem_wt; eauto.
    intros WT2.
    exploit path_of_eval_place; eauto. intros (phl & PATH).
    exploit assign_loc_sound; eauto.
    intros (fpm3 & FPM3 & MM3).
    econstructor; eauto.
    admit.
    
Admitted.


Lemma reachable_state_sound: forall s,
    (* What about after external? *)
    reachable L s -> sound_state s.
Admitted.


(** Specific definition of partial safe *)
Definition partial_safe (s: state) : Prop :=
  safe L s \/ step_mem_error ge s.

Lemma borrow_check_lts_safe:
    borrow_check_program p = OK tt ->
    lts_safe se (semantics p se) wt_c wt_c (fun _ => partial_safe) w ->
    lts_safe se (semantics p se) wt_c wt_c safe w.
Proof.
  intros BORCHK PSAFE. inv PSAFE.  
  constructor.
  - intros s t s' REACH STEP.
    generalize (step_safe _ _ _ REACH STEP). intros PSAFE.
    destruct PSAFE as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply reachable_state_sound. eapply step_reachable; eauto.
  (* initial_progress *)
  - eauto.
  (* initial_safe *)
  - intros q s INIT.
    generalize (initial_safe _ _ INIT). intros PSAFE.
    destruct PSAFE as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply initial_state_sound; eauto.
  (* external_safe *)
  - intros s q REACH EXT.
    generalize (external_safe _ _ REACH EXT).
    intros (wA & SYMBINV & VQ & AFTEREXT).
    exists wA. split; auto. split; auto.
    intros r VR. generalize (AFTEREXT _ VR).
    intros ((s' & AFTER) & PSAFE).
    split. exists s'. eauto.
    intros s'' AFTER1.
    generalize (PSAFE s'' AFTER1). intros PSAFE1.
    destruct PSAFE1 as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply reachable_state_sound. eapply external_reach; eauto.
    eapply star_refl.
  - eauto.
Qed.    
    
End BORCHK.



(* Lemma borrow_check_safe: forall p, *)
(*     borrow_check_program p = OK tt -> *)
(*     module_safe (semantics p) wt_c wt_c partial_safe -> *)
(*     module_safe (semantics p) wt_c wt_c safe. *)
(* Proof. *)
(*   intros p BORCHK MSAFE. *)
(*   red. intros w se VALIDSE SYMBINV. *)
(* Admitted. *)

