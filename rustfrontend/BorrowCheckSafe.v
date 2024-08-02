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
Lemma subplace_align: forall ce p1 p2 ofs,
  subplace ce p1 p2 ofs ->
  (alignof ce (typeof_place p2) | ofs).
Proof.
  induction 1.
  - apply Z.divide_0_r.
  - simpl. eapply Z.divide_add_r.
    + admit.
    + eapply field_offset_aligned_gen
      

(** Test: try to define semantics well-typedness for a memory location *)

Definition footprint := block -> Z -> Prop. 

Definition empty_footprint : footprint := fun b ofs => False.

Definition footprint_equiv (fp1 fp2: footprint) :=
  forall b ofs, fp1 b ofs <-> fp2 b ofs.

Definition footprint_incr (fp1 fp2: footprint) :=
  forall b ofs, fp1 b ofs -> fp2 b ofs.

Definition remove_footprint (fp: footprint) b ofs sz :=
  fun b1 ofs1 =>
    ((b1 = b /\ ofs <= ofs1 < ofs + sz) -> False)
    /\ fp b1 ofs1.

Definition add_footprint (fp: footprint) b ofs sz :=
  fun b1 ofs1 =>
    ((b1 = b /\ ofs <= ofs1 < ofs + sz))
    \/ fp b1 ofs1.

Definition in_footprint (fp: footprint) b ofs sz :=
  forall ofs1, ofs <= ofs1 < ofs + sz -> fp b ofs1.

Definition merge_footprint (fp1 fp2: footprint) :=
  fun b ofs => fp1 b ofs \/ fp2 b ofs.

Definition merge_footprint_list (l: list footprint) :=
  fun b ofs => exists fp, In fp l -> fp b ofs.

Definition footprint_disjoint (fp1 fp2: footprint) :=
  forall b ofs, fp1 b ofs -> fp2 b ofs -> False.

Definition footprint_disjoint_list (l: list footprint) :=
  forall fp1 fp2, In fp1 l -> In fp2 l ->
             ~ footprint_equiv fp1 fp2 ->
             footprint_disjoint fp1 fp2.

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

Inductive sem_wt_loc (ce: composite_env) (m: mem) : footprint -> block -> Z -> type -> Prop :=
| sem_wt_box: forall ty b ofs fp
    (INFP: in_footprint fp b ofs (size_chunk Mptr))
    (VALID: Mem.valid_access m Mptr b ofs Freeable)
    (WT: forall b' ofs',
        (* We do not restrict the value in this location *)
        Mem.load Mptr m b ofs = Some (Vptr b' ofs') ->
        (* Box pointer must points to the start of a block *)
        (ofs' = Ptrofs.zero
         /\ sem_wt_loc ce m (remove_footprint fp b ofs (size_chunk Mptr)) b' 0 ty)),
    sem_wt_loc ce m fp b ofs (Tbox ty)
| sem_wt_struct: forall fp b ofs co fpl orgs id
    (CO: ce ! id = Some co)
    (INFP: in_footprint fp b ofs (co_sizeof co))
    (VALID: Mem.range_perm m b ofs (ofs + co_sizeof co) Cur Freeable)
    (FPL: footprint_disjoint_list fpl)
    (FPLCON: footprint_equiv fp (merge_footprint_list fpl))
    (* all fields are semantically well typed *)
    (FWT: forall n fid fty ffp fofs bf,
        nth_error co.(co_members) n = Some (Member_plain fid fty) ->
        nth_error fpl n = Some ffp ->
        field_offset ce fid co.(co_members) = OK (fofs, bf) ->
        sem_wt_loc ce m ffp b (ofs + fofs) fty),
    sem_wt_loc ce m fp b ofs (Tstruct orgs id)
| sem_wt_enum: forall fp b ofs orgs id co
    (CO: ce ! id = Some co)
    (INFP: in_footprint fp b ofs (co_sizeof co))
    (VALID: Mem.range_perm m b ofs (ofs + co_sizeof co) Cur Freeable)
    (* Interpret the field by the tag and prove that it is well-typed *)
    (FWT: forall tag fid fty fofs bf,
        Mem.load Mint32 m b ofs = Some (Vint tag) ->
        list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK (fofs, bf) ->
        sem_wt_loc ce m (remove_footprint fp b ofs fofs) b (ofs + fofs) fty),
    sem_wt_loc ce m fp b ofs (Tvariant orgs id)
| sem_wt_scalar: forall ty b ofs
    (TY: scalar_type ty = true)
    (VALID: Mem.range_perm m b ofs (ofs + sizeof ce ty) Cur Freeable)
    (* To make sure that well-typed footprint is closed? *)
    (WT: forall v chunk b' ofs',
        Mem.load chunk m b ofs = Some v ->
        v <> Vptr b' ofs'),
    sem_wt_loc ce m (add_footprint empty_footprint b ofs (sizeof ce ty)) b ofs ty
.

(* similar to val_casted ? *)
Inductive sem_wt_val (ce: composite_env) (m: mem) : footprint -> val -> type -> Prop :=
| wt_val_unit:
  sem_wt_val ce m empty_footprint (Vint Int.zero) Tunit
| wt_val_int: forall sz si n,
    Cop.cast_int_int sz si n = n ->
    sem_wt_val ce m empty_footprint (Vint n) (Tint sz si)
| wt_val_float: forall n,
    sem_wt_val ce m empty_footprint (Vfloat n) (Tfloat Ctypes.F64)
| wt_val_single: forall n,
    sem_wt_val ce m empty_footprint (Vsingle n) (Tfloat Ctypes.F32)
| wt_val_long: forall si n,
    sem_wt_val ce m empty_footprint (Vlong n) (Tlong si)
| wt_val_box: forall b ty fp,
    (** Box pointer must be in the starting point of a block *)
    sem_wt_loc ce m fp b 0 ty ->
    sem_wt_val ce m fp (Vptr b Ptrofs.zero) (Tbox ty)
(* TODO *)
(* | wt_val_ref: forall b ofs ty org mut, *)
(*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *)
| wt_val_struct: forall id orgs b ofs fp co fpl
    (CO: ce ! id = Some co)
    (FPL: footprint_disjoint_list fpl)
    (FPLCON: footprint_equiv fp (merge_footprint_list fpl))
    (* Because struct value is passed by its address, we need to show
    that all the fields in this address is well typed value *)
    (FWT: forall n fid fty fofs bf v ffp,
        nth_error co.(co_members) n = Some (Member_plain fid fty) ->
        nth_error fpl n = Some ffp ->
        field_offset ce fid co.(co_members) = OK (fofs, bf) ->
        deref_loc fty m b (Ptrofs.add ofs (Ptrofs.repr fofs)) v -> 
        sem_wt_val ce m ffp v fty),
    sem_wt_val ce m fp (Vptr b ofs) (Tstruct orgs id)
| wt_val_enum: forall id orgs b ofs fp co
    (CO: ce ! id = Some co)
    (FWT: forall tag fid fty fofs bf v,
        Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
        list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK (fofs, bf) ->
        deref_loc fty m b (Ptrofs.add ofs (Ptrofs.repr fofs)) v -> 
        sem_wt_val ce m fp v fty),
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
  rsw (sg: rust_signature) (fp: footprint) (m: mem).

Inductive wt_rs_query : wt_rs_world -> rust_query -> Prop :=
| wt_rs_query_intro: forall sg fp m vf args fpl
    (FPL: footprint_disjoint_list fpl)
    (FPLCON: footprint_equiv fp (merge_footprint_list fpl))                       
    (WT: sem_wt_val_list (sig_comp_env sg) m fpl args (sig_args sg)),
    wt_rs_query (rsw sg fp m) (rsq vf sg args m)
.

(* Only consider ownership transfer for now. The footprints of generic
origins are more complicated *)
Inductive rsw_acc : wt_rs_world -> wt_rs_world -> Prop :=
| rsw_acc_intro: forall sg fp fp' m m'
    (UNC: Mem.unchanged_on (fun b ofs => ~ fp b ofs) m m')
    (FPINCR: footprint_incr fp fp'),
    rsw_acc (rsw sg fp m) (rsw sg fp' m').

Inductive wt_rs_reply : wt_rs_world -> rust_reply -> Prop :=
| wt_rs_reply_intro: forall rfp m rv sg fp
    (WT: sem_wt_val (sig_comp_env sg) m rfp rv (sig_res sg))
    (FPINCR: footprint_incr rfp fp),
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

Definition fp_map := PTree.t footprint.

(** Definition of abstracter which maps a memory block to a place
(i.e. the owner of this block) *)

(* Definition mem_abstracter : Type := block -> Z -> option (place * Z). *)
Definition mem_abstracter : Type := block -> option place.
  
Section MATCH.

Variable ce: composite_env.
Variable abs: mem_abstracter.
Variable fpm: fp_map.

(* The footprint of a place *)
Inductive place_footprint : place -> footprint -> Prop :=
| place_footprint_deref: forall p p' fp ofs b ty
    (FP: place_footprint p fp)
    (ABS: abs b = Some p')
    (SUBP: subplace ce p' p ofs),
    place_footprint (Pderef p ty) (remove_footprint fp b ofs (sizeof ce (typeof_place p)))
| place_footprint_field: forall p p' fp ofs b orgs id fid fty co fofs bf
    (FP: place_footprint p fp)
    (ABS: abs b = Some p')
    (SUBP: subplace ce p' p ofs)
    (TY: typeof_place p = Tstruct orgs id)
    (CO: ce!id = Some co)
    (FOFS: field_offset ce id co.(co_members) = OK (fofs, bf)),
    (* fp - [(b,ofs), (b, ofs+sizeof(p))) + [(b,ofs+fofs), (b, ofs+fofs+sizeof(fty))) *)
    place_footprint (Pfield p fid fty)
    (add_footprint (remove_footprint fp b ofs (co_sizeof co)) b (ofs+fofs) (sizeof ce fty))
| place_footprint_enum: forall p fp fid fty
    (** FIXME: is it correct?  *)
    (FP: place_footprint p fp),
    place_footprint (Pdowncast p fid fty) fp
| place_footprint_local: forall id fp ty
    (FP: fpm ! id = Some fp),
    place_footprint (Plocal id ty) fp
.


(* The value stored in m[b, ofs] is consistent with the type of p *)
Inductive bmatch (m: mem) (b: block) (ofs: Z) (p: place) (own: own_env) : type -> Prop :=
| bm_box: forall ty
    (* valid resource. If the loaded value is not a pointer, it is a
    type error instead of a memory error *)
    (* N.B. A compilcated situation is that [p] may fully own the
    resource so that the all the blocks of the owned chain it points
    to are not in the range of [own] environment. In this case, we
    should show that the ownership chain is semantics well typed. But
    if [p] just partially own the resoruce, we need to explicitly show
    that the owner of the block it points to is [*p]. *)
    (VRES: forall b1 ofs1,
        Mem.load Mptr m b ofs = Some (Vptr b1 ofs1) ->
        (** Case1: p is partially owned *)
        (* p owns the location it points to. Box pointer must points
        to the start of a block and *p is the owner of this block *)
        (is_shallow_owned own p = true -> (ofs1 = Ptrofs.zero /\ abs b1 = Some (Pderef p ty)))
        (** Case2: p is fully owned: own b1 is None. How to get the
        footprint of this semantics well typedness? *)
        /\ (is_deep_owned own p = true ->
           (exists fp, place_footprint p fp
                  /\ sem_wt_loc ce m fp b ofs (typeof_place p)))),
    bmatch m b ofs p own (Tbox ty)
| bm_struct: forall orgs id
    (* all fields in the struct satisfy bmatch *)
    (FMATCH: forall co fid fty fofs bf,
        ce ! id = Some co ->
        In (Member_plain fid fty) co.(co_members) ->       
        field_offset ce fid co.(co_members) = OK (fofs, bf) ->
        bmatch m b (ofs + fofs) (Pfield p fid fty) own fty),
    bmatch m b ofs p own (Tstruct orgs id)
| bm_enum: forall orgs id
    (FMATCH: forall co fid fty fofs bf tag,
        ce ! id = Some co ->
        (* load tag *)
        Mem.load Mint32 m b ofs = Some (Vint tag) ->
        list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK (fofs, bf) ->        
        bmatch m b (ofs + fofs) (Pdowncast p fid fty) own fty),
    bmatch m b ofs p own (Tvariant orgs id)
| bm_scalar: forall ty,
    scalar_type ty = true ->
    bmatch m b ofs p own ty
(** TODO: bm_reference  *)
.

(** Some bmatch properties *)

(* bmatch under subplace *)

Lemma bmatch_subplace: forall p p' ofs ofs' own m b,
    bmatch m b ofs p own (typeof_place p) ->
    subplace ce p p' ofs' ->
    bmatch m b (ofs + ofs') p' own (typeof_place p').
Admitted.

(** TODO: support alias analysis domain *)
Definition mmatch (m: mem) (own: own_env) : Prop :=
  forall b p,
    abs b = Some p ->
    (Mem.range_perm m b 0 (sizeof ce (typeof_place p)) Cur Freeable
    /\ bmatch m b 0 p own (typeof_place p)).

Record wf_abs (e: env) : Prop :=
  { wf_local_env: forall id b ty,
      e ! id = Some (b, ty) ->
      abs b = Some (Plocal id ty) }.

End MATCH.


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
    wt_place (Pfield p fid ty)
| wt_downcast: forall p ty fid co orgs id,
    wt_place p ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    field_type fid co.(co_members) = OK ty ->
    wt_place (Pdowncast p fid ty)
.

End TYPING.

Definition env_to_tenv (e: env) : typenv :=
  PTree.map1 snd e.

(** Some auxilary definitions *)

(* Well-formed ownership environment *)

Record wf_own_env (own: own_env) : Prop := {
    (* A place is owned then all its dominators are owned *)
    wf_own_dominator: forall p,
      is_owned own p = true ->
      place_dominator_own own p = true
  }.


(* properties of place_dominator *)

Lemma place_dominator_local: forall p p',
    place_dominator p = Some p' ->
    local_of_place p = local_of_place p'.
Proof.
  induction p; simpl; auto.
  congruence.
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
  - exploit IHp. eauto. intros A. eapply is_prefix_strict_trans. eauto.
    unfold is_prefix_strict. simpl. destruct (place_eq p p). auto. congruence.
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

Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f s k e own m entry cfg pc instr ae Σ Γ Δ abs fpm
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (INSTR: cfg ! pc = Some instr)
    (MSTMT: match_instr_stmt f.(fn_body) instr s k)
    (CHK: borrow_check ce f = OK ae)
    (AS: ae ! pc = Some (AE.State Σ Γ Δ))
    (MM: mmatch ce abs fpm m own)
    (WF: wf_abs abs e),
    sound_state (State f s k e own m)
.


(** The address of a place is consistent with the abstracter. For now,
we do not consider reference *)
Lemma eval_place_sound: forall e m p b ofs abs own fpm
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch ce abs fpm m own)
    (WFABS: wf_abs abs e)
    (WFOWN: wf_own_env own)
    (WT: wt_place (env_to_tenv e) ce p)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: place_dominator_shallow_own own p = true),
  exists p', abs b = Some p'
        /\ subplace ce p' p (Ptrofs.unsigned ofs)
    (* if consider reference, we cannot say that p is a subplace of
    p', instead we need to state that the owner p points to is a
    subplace of p' *)
.
Proof.
  induction 1; intros.
  (* Plocal *)
  - rewrite Ptrofs.unsigned_zero.
    exists (Plocal id ty). split.
    eapply wf_local_env; eauto.
    econstructor.
  (* Pfield *)
  - inv WT.
    eapply place_dominator_shallow_own_shallow_prefix with (p':= p) in POWN.
    exploit IHEVAL. 1-5: auto.
    intros (p' & ABS & SUBP).
    exists p'. split. auto.
    rewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr.
    (* two type facts, reduce one *)
    rewrite H in H6. inv H6. rewrite H0 in H7. inv H7.
    econstructor. auto. eauto. eauto.
    rewrite Ptrofs.unsigned_repr. eauto.
    (** dirty work: specify the requirement of not overflow *)
    admit. admit. 
    unfold is_shallow_prefix. eapply orb_true_intro.
    right. simpl. destruct (place_eq p p). auto. congruence.    
  (* Pdowncast *)
  - inv WT.
    eapply place_dominator_shallow_own_shallow_prefix with (p':= p) in POWN.
    exploit IHEVAL. 1-5: auto.
    intros (p' & ABS & SUBP).
    exists p'. split. auto.
    rewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr.
    (* two type facts, reduce one *)
    rewrite H in H8. inv H8. rewrite H0 in H9. inv H9.
    econstructor. auto. eauto. eauto.
    rewrite Ptrofs.unsigned_repr. eauto.
    (** dirty work: specify the requirement of not overflow *)
    admit. admit. 
    unfold is_shallow_prefix. eapply orb_true_intro.
    right. simpl. destruct (place_eq p p). auto. congruence.
  (* Pderef *)
  - inv WT.
    exploit IHEVAL. eauto. eauto. eauto. eauto.
    (* place dominator is shallow owned *)
    unfold place_dominator_shallow_own in POWN. simpl in POWN.
    eapply dominator_of_shallow_owned_place. auto. auto.
    intros (p' & ABS & SUBP).
    eapply MM in ABS. destruct ABS as (A & B).
    (* p is a subplace of p' and p' bmatch implies p bmatch *)
    exploit bmatch_subplace; eauto. rewrite Z.add_0_l. intros BM.
    (* typeof_place p must be box/reference *)
    destruct (typeof_place p) eqn: TYP; simpl in *; try congruence.
    (* Tbox *)
    + inv BM.
      assert (LOAD: Mem.load Mptr m l (Ptrofs.unsigned ofs) = Some (Vptr l' ofs')).
      { inv H. simpl in H0. inv H0.  auto.
        simpl in H1. inv H1.
        simpl in H1. inv H1. }
      inv H3.
      generalize (VRES _ _ LOAD). intros ABS.
      (* Now we need to say that p is shallow owned *)
      unfold place_dominator_shallow_own in POWN. simpl in POWN.
      destruct ABS as (C & D).
      eapply C in POWN. destruct POWN as (E & F). subst.
      exists (Pderef p ty). split. auto.
      rewrite Ptrofs.unsigned_zero. constructor.
      (* box is not scalar type *)
      simpl in H0. congruence.
    (* reference *)
    + admit.
Admitted.


Lemma eval_place_no_mem_error: forall e m p abs own fpm
    (MM: mmatch ce abs fpm m own)
    (WFABS: wf_abs abs e)
    (WFOWN: wf_own_env own)
    (WT: wt_place (env_to_tenv e) ce p)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: place_dominator_shallow_own own p = true)
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
    + admit.
    (* deref error *)
    + inv WT.
      exploit eval_place_sound. 1-5: eauto.
      eapply dominator_of_shallow_owned_place. auto.
      unfold place_dominator_shallow_own in POWN. simpl in POWN.
      auto.
      intros (p' & ABS & SUBP).
      (* The block of p' is valid block *)
      eapply MM in ABS. destruct ABS as (PERM & BM).
      (* inv deref_loc_error *)
      inv H2. unfold Mem.valid_access in H0.
      Z.divide
      








        
Lemma sound_state_no_mem_error: forall s,
    step_mem_error ge s -> sound_state s -> False .
Admitted.

Lemma initial_state_sound: forall q s,
    wt_rs_query w q ->
    Smallstep.initial_state L q s ->
    sound_state s.
Admitted.

Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    Step L s1 t s2 ->
    (* how to prove sound_state in dropstate? *)
    sound_state s2.
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
    
