Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight.
Require Import Rustlight Rustlightown RustIR.
Require Import InitDomain.


Import ListNotations.

(** ** Ownership based operational semantics for RustIR (the semantics before drop elaboration equipped with an ownership local environment) *)

Section SEMANTICS.
          
(** Continuation *)
  
Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: place -> function -> env -> own_env -> cont -> cont
(* used to record Dropplace state *)
| Kdropplace: function -> option drop_place_state -> list (place * bool) -> env -> own_env -> cont -> cont
| Kdropcall: ident -> val -> option drop_member_state -> members -> cont -> cont
.


(** Pop continuation until a call or stop *)

(* Return from dropstate and dropplace is UB *)
Fixpoint call_cont (k: cont) : option cont :=
  match k with
  | Kseq _ k => call_cont k
  | Kloop _ k => call_cont k
  | Kdropplace _ _ _ _ _ _ => None
  | Kdropcall _ _ _ _ _  => None                             
  | _ => Some k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

Lemma call_cont_correct: forall k k',
    call_cont k = Some k' ->
    is_call_cont k'.
Proof.
  induction k; intros k' CC; simpl in *; auto; try (inv CC; econstructor; eauto).
Qed.

(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (m: mem) : state
(* Simulate elaborate drop *)
| Dropplace
    (f: function)
    (s: option drop_place_state)
    (l: list (place * bool))
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Dropstate
(* The reason why dropstate does not contain the function is to match the new stack frame in Clight. *)
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (m: mem): state.              


(* RustIRown specific function entry *)

Local Open Scope error_monad_scope.

(* just copy from Rustlightown except the extract_vars *)
Program Definition init_own_env (ce: composite_env) (f: function) : Errors.res own_env :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  (* let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in *)
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let init := empty_pathmap in
  (* initialize maybeUninit with the variables and parameters *)
  let vl := places_of_locals (f.(fn_params) ++ f.(fn_vars)) in
  let uninit := add_place_list whole vl empty_pathmap in
  (** Is it reasonable? Translation validation: check (whole = init ∪
  uninit) and (∅ = init ∩ uninit) *)
  match check_own_env_consistency empty_pathmap init uninit whole with
  | true =>
      OK {| own_init := init;
           own_uninit := uninit;
           own_universe := whole |}
  | _ =>
      Error (msg "validation fail in init_own_env")
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  eapply andb_true_iff in Heq_anonymous.
  destruct Heq_anonymous as (A & B).
  eapply PathsMap.beq_correct in A.
  eapply PathsMap.beq_correct in B.
  (* set (init:= (add_place_list whole *)
  (*             (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f)) *)
  (*             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *. *)
  set (init:= (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole)) in *.
  set (uninit :=(add_place_list whole
             (map (fun elt : ident * type => Plocal (fst elt) (snd elt))
                (fn_params f ++ fn_vars f))
             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *.
  clear B.
  eapply PathsMap_lub_union.
  auto.
Defined.
Next Obligation.
  symmetry in Heq_anonymous.
  eapply andb_true_iff in Heq_anonymous.
  destruct Heq_anonymous as (A & B).
  eapply PathsMap.beq_correct in A.
  eapply PathsMap.beq_correct in B.
  (* set (init:= (add_place_list whole *)
  (*             (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f)) *)
  (*             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *. *)
  set (init:= (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole)) at 1.
  fold init in A ,B.
  set (uninit :=(add_place_list whole
             (places_of_locals (f.(fn_params) ++ f.(fn_vars)))
             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *.
  red in B.
  generalize (B id). intros EQ.
  assert (EQ1: LPaths.eq (PathsMap.get id
                       (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))
                    Paths.empty).  
  {  unfold PathsMap.get in *.
     erewrite PTree.gmap in *.
     destruct (whole ! id). simpl. eapply LPaths.eq_refl.
     simpl. eapply LPaths.eq_refl. }  
  eapply LPaths.eq_trans; eauto.
  (* core proof *)
  eapply LPaths.eq_sym.
  eapply LPaths.eq_trans. eapply B.
  red. red. intros a.
  assert (C: inter_opt None None = None) by auto.
  exploit (PathsMap.gcombine inter_opt C init uninit).  
  instantiate (1 := id).
  intros OPTEQ. clear EQ EQ1.
  (* init is the same as empty map, we need to take care of them *)
  unfold init at 2. fold uninit.
  split; intros IN.
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine inter_opt init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      (* Set Printing All. *)
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      * eapply OPTEQ. auto.
      * exfalso. eapply Paths.empty_1.
        eapply OPTEQ. eauto.                 
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      exfalso.
      eapply Paths.empty_1. eauto.
      exfalso.
      eapply Paths.empty_1. eauto.      
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine inter_opt init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      * eapply OPTEQ. auto.
      * eapply Paths.inter_2 in IN.
        exfalso. eapply Paths.empty_1. eauto.
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      eapply Paths.inter_1 in IN.
      exfalso. eapply Paths.empty_1. eauto.
      eapply Paths.inter_1 in IN. auto.
Defined.  


Section SMALLSTEP.

Variable ge: genv.

(* Mostly the same as RustIRsem *)
Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) membs k m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (STRUCT: co2.(co_sv) = Struct),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fid2 fty2 fofs tag orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr cb cofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co2.(co_members) (Int.unsigned tag) = Some (Member_plain fid2 fty2)),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state ge fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) m)
| step_dropstate_box: forall b ofs id co fid fofs m m' tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (DROPB: drop_box_rec ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m) E0
      (Dropstate id (Vptr b ofs) None membs k m')
| step_dropstate_return1: forall b ofs id m f e own k ps s,
    step_drop
      (* maybe we should separate step_dropstate_return to reuse
      step_drop because of the mismatch between Kdropplace and Kcall
      in RustIRown and RUstIRsem *)
      (Dropstate id (Vptr b ofs) None nil (Kdropplace f s ps e own k) m) E0
      (Dropplace f s ps k e own m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k m)
.


Inductive step_drop_mem_error : state -> Prop :=
| step_dropstate_struct_error: forall id1 id2 co1 b1 ofs1 tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m)
| step_dropstate_enum_error1: forall id1 id2 co1 b1 ofs1 tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
    (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)
| step_dropstate_enum_error2: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* error in loading the tag *)
    (TAG: ~ Mem.valid_access m Mint32 cb (Ptrofs.unsigned cofs) Readable),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)      
| step_dropstate_box_error: forall b ofs id co fid fofs m tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (* error in dropping the box chain *)
    (DROPB: drop_box_rec_mem_error ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys),
    step_drop_mem_error
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m)
.

(* The procedure of dropping a place: we first check its intiialization status (is_init): 1. if false, skip this place; 2. if true, we then check if it is scalar type. 2.1. if true, update the own_env and then skip this place; 2.2 if false, start to drop this place *)

Inductive step_dropplace : state -> trace -> state -> Prop :=
| step_dropplace_init1: forall f p ps k le own m full
    (* p is not owned, so just skip it (How to relate this case with
    RustIRsem because drop elaboration removes this place earlier in
    generate_drop_flag) *)
    (NOTOWN: is_init own p = false),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f None ps k le own m)
| step_dropplace_init2: forall f p ps k le own m st (full: bool)
    (OWN: is_init own p = true)
    (NOTSCALAR: scalar_type (typeof_place p) = false)
    (DPLACE: st = (if full then gen_drop_place_state p else drop_fully_owned_box [p])),
    (* move p to match drop p *)
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f (Some st) ps k le (move_place own p) m)
| step_dropplace_scalar: forall f p ps k le own m full
    (OWN: is_init own p = true)
    (SCALAR: scalar_type (typeof_place p) = true),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f None ps k le (move_place own p) m)    

| step_dropplace_box: forall le m m' k ty b' ofs' f b ofs p own ps l
    (* simulate step_drop_box in RustIRsem *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    (* We are dropping p. fp is the fully owned place which is split into p::l *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m) E0
      (Dropplace f (Some (drop_fully_owned_box l)) ps k le own m')
| step_dropplace_struct: forall m k orgs co id p b ofs f le own ps l
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: eval_place ge le m p b ofs),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) m)
| step_dropplace_enum: forall m k p orgs co id fid fty tag b ofs f le own ps l
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) nil (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) m)
| step_dropplace_next: forall f ps k le own m,
    step_dropplace (Dropplace f (Some (drop_fully_owned_box nil)) ps k le own m) E0
      (Dropplace f None ps k le own m)
| step_dropplace_return: forall f k le own m,
    step_dropplace (Dropplace f None nil k le own m) E0
      (State f Sskip k le own m)
.


Inductive step_dropplace_mem_error: state -> Prop :=
| step_dropplace_box_error1: forall le m k f p own ps l
    (* eval_place error *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error2: forall le m k f p own ps l b ofs ty
    (* deref_loc error *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc_mem_error (Tbox ty) m b ofs),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error3: forall le m k f p own ps l b ofs ty b' ofs'
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* free error *)
    (FREE: extcall_free_sem_mem_error [Vptr b' ofs'] m),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_struct_error: forall m k p f le own ps l orgs id co
    (TYP: typeof_place p = Tstruct orgs id)
    (CO: (genv_cenv ge) ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (* p is struct or enum *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
| step_dropplace_enum_error1: forall m k p f le own ps l orgs id co
    (TYP: typeof_place p = Tvariant orgs id)
    (CO: (genv_cenv ge) ! id = Some co)
    (STRUCT: co_sv co = TaggedUnion)
    (* p is struct or enum *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
| step_dropplace_enum_error2: forall m k p orgs co id b ofs f le own ps l
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* error in loading the tag *)
    (ERR: ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m1 m2 b ofs v v1 own1 own2 own3
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (TYP: forall orgs id, typeof_place p <> Tvariant orgs id),
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 ge e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    step (State f (Sassign p e) k le own1 m1) E0 (State f Sskip k le own3 m2)
| step_assign_variant: forall f e p ty k le m1 m2 m3 b ofs b1 ofs1 v v1 tag co fid enum_id orgs own1 own2 own3 fofs
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (* evaluate the expr, return the value *)
    (EXPR: eval_expr ge le m1 ge e v)
    (* evaluate the location of the variant in p (in memory m1) *)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* sem_cast to simulate Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* set the value *)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (** different from normal assignment: update the tag and assign value *)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (* eval the location of the tag: to simulate the target statement:
    because we cannot guarantee that store value in m1 does not change
    the address of p! (Non-interference is a difficult problem!) *)
    (PADDR2: eval_place ge le m2 p b1 ofs1)
    (* set the tag *)
    (STAG: Mem.storev Mint32 m2 (Vptr b1 ofs1) (Vint (Int.repr tag)) = Some m3),
   step (State f (Sassign_variant p enum_id fid e) k le own1 m1) E0 (State f Sskip k le own3 m3)
| step_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs own1 own2 own3
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3),
    typeof_place p = Tbox ty ->
    (* Simulate malloc semantics to allocate the memory block *)
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* evaluate the expression after malloc to simulate*)
    eval_expr ge le m3 ge e v ->
    (* sem_cast the value to simulate function call in Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (* assign the value to the allocated location *)
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* assign the address to p *)
    eval_place ge le m4 p pb pofs ->
    assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5 ->
    step (State f (Sbox p e) k le own1 m1) E0 (State f Sskip k le own3 m5)

(** dynamic drop semantics: simulate the drop elaboration *)
| step_to_dropplace: forall f p le own m drops k universe
    (UNI: PathsMap.get (local_of_place p) own.(own_universe) = universe)
    (SPLIT: split_drop_place ge universe p (typeof_place p) = OK drops),
    (* get the owned place to drop *)
    step (State f (Sdrop p) k le own m) E0
      (Dropplace f None drops k le own m)
| step_in_dropplace: forall f s ps k le own m E S
    (SDROP: step_dropplace (Dropplace f s ps k le own m) E S),
    step (Dropplace f s ps k le own m) E S
| step_dropstate: forall id v s membs k m S E
    (SDROP: step_drop (Dropstate id v s membs k m) E S),
    step (Dropstate id v s membs k m) E S
    
| step_storagelive: forall f k le m id own,
    step (State f (Sstoragelive id) k le own m) E0 (State f Sskip k le own m)
| step_storagedead: forall f k le m id own,
    step (State f (Sstoragedead id) k le own m) E0 (State f Sskip k le own m)
         
| step_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels own1 own2
    (TFEXPRLIST: move_place_list own1 (moved_place_list al) = own2)
    (GFUN: function_not_drop_glue fd),
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m ge a vf ->
    eval_exprlist ge le m ge al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    step (State f (Scall p a al) k le own1 m) E0 (Callstate vf vargs (Kcall p f le own2 k) m)

| step_internal_function: forall vf f vargs k m e m' own1 own2
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None)
    (* initialize own_env *)
    (INITOWN: init_own_env ge f = OK own1)
    (INITPARAMS: init_place_list own1 (places_of_locals f.(fn_params)) = own2)
    (ENTRY: function_entry ge f vargs m e m'),  
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e own2 m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')

(** Return cases. For the reason why we do not support return None and
skip return, see Rustlightown.v *)
(* | step_return_0: forall e lb m1 m2 f k own, *)
(*     blocks_of_env ge e = lb -> *)
(*     (* drop the stack blocks *) *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     (* return unit or Vundef? *) *)
(*     step (State f (Sreturn None) k e own m1) E0 (Returnstate Vundef (call_cont k) m2) *)
| step_return_1: forall le p v v1 lb m1 m2 f k ck own1 (* own2 *)
    (CONT: call_cont k = Some ck)
    (* (TFEXPR: move_place_option own1 (moved_place a) = own2), *)
    (EVAL: eval_expr ge le m1 ge (Epure (Eplace p (typeof_place p))) v)
    (* sem_cast to the return type *)
    (CAST: sem_cast v (typeof_place p) f.(fn_return) = Some v1)
    (* drop the stack blocks *)
    (STK: blocks_of_env ge le = lb)
    (FREE: Mem.free_list m1 lb = Some m2),
    step (State f (Sreturn p) k le own1 m1) E0 (Returnstate v1 ck m2)
(* no return statement but reach the end of the function *)
(* | step_skip_call: forall e lb m1 m2 f k own, *)
(*     is_call_cont k -> *)
(*     blocks_of_env ge e = lb -> *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     step (State f Sskip k e own m1) E0 (Returnstate Vundef (call_cont k) m2) *)

| step_returnstate: forall p v b ofs m1 m2 e f k own1 own2
    (TFASSIGN: own_transfer_assign own1 p = own2),
    eval_place ge e m1 p b ofs ->
    val_casted v (typeof_place p) ->
    assign_loc ge (typeof_place p) m1 b ofs v m2 ->    
    step (Returnstate v (Kcall p f e own1 k) m1) E0 (State f Sskip k e own2 m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m own,
    step (State f (Ssequence s1 s2) k e own m)
      E0 (State f s1 (Kseq s2 k) e own m)
| step_skip_seq: forall f s k e m own,
    step (State f Sskip (Kseq s k) e own m)
      E0 (State f s k e own m)
| step_continue_seq: forall f s k e m own,
    step (State f Scontinue (Kseq s k) e own m)
      E0 (State f Scontinue k e own m)
| step_break_seq: forall f s k e m own,
    step (State f Sbreak (Kseq s k) e own m)
      E0 (State f Sbreak k e own m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty own1,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m ge a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e own1 m)
      E0 (State f (if b then s1 else s2) k e own1 m)
| step_loop: forall f s k e m own,
    step (State f (Sloop s) k e own m)
      E0 (State f s (Kloop s k) e own m)
| step_skip_or_continue_loop:  forall f s k e m x own,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e own m)
      E0 (State f s (Kloop s k) e own m)
| step_break_loop:  forall f s k e m own,
    step (State f Sbreak (Kloop s k) e own m)
      E0 (State f Sskip k e own m)
.


(** Open semantics *)

Inductive initial_state: rust_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (* This function must not be drop glue *)
    f.(fn_drop_glue) = None ->
    (* how to use it? *)
    val_casted_list vargs targs ->
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    initial_state (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs m)
      (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> rust_query -> Prop:=
| at_external_intro: forall vf name args k m targs tres cconv orgs org_rels,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv) ->
    at_external (Callstate vf args k m) (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args m).

Inductive after_external: state -> rust_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (rsr v m')
      (Returnstate v k m').

Inductive final_state: state -> rust_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (rsr v m).

(* Definition of memory error state in RustIR *)

Inductive function_entry_mem_error (f: function) (vargs: list val) (m: mem) (e: env) : Prop :=
  | function_entry_mem_error_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters_mem_error ge e m1 f.(fn_params) vargs ->
      function_entry_mem_error f vargs m e.

Inductive step_mem_error : state -> Prop :=
| step_assign_error1: forall f e p k le m own,    
    eval_expr_mem_error ge le m e ->
    step_mem_error (State f (Sassign p e) k le own m)
| step_assign_error2: forall f e p k le m own v,
    eval_expr ge le m ge e v ->
    eval_place_mem_error ge le m p ->
    step_mem_error (State f (Sassign p e) k le own m)
| step_assign_error3: forall f e p k le m b ofs v v1 own,
    eval_place ge le m p b ofs ->
    eval_expr ge le m ge e v ->
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    assign_loc_mem_error ge (typeof_place p) m b ofs v1 ->
    step_mem_error (State f (Sassign p e) k le own m)
| step_assign_variant_error1: forall f e p k le m enum_id fid own,
    (* error in evaluating the expression *)
    eval_expr_mem_error ge le m e ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le own m)
| step_assign_variant_error2: forall f e p k le v m enum_id fid own,
    eval_expr ge le m ge e v ->
    (* error in evaluating lhs *)
    eval_place_mem_error ge le m p ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le own m)                   
| step_assign_variant_error3: forall f e p ty k le m1 b ofs v v1 co fid enum_id orgs own fofs
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* error in assigning the value to the enum body *)
    (ERR: assign_loc_mem_error ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1),
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le own m1)
| step_assign_variant_error4: forall f e p ty k le m1 m2 b ofs v v1 co fid enum_id orgs own fofs
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (* error in evaluating the place in the second time *)
    (ERR: eval_place_mem_error ge le m2 p),
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le own m1)
| step_assign_variant_error5: forall f e p ty k le m1 m2 b ofs b1 ofs1 v v1 co fid enum_id orgs own fofs tag
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (PADDR: eval_place ge le m2 p b1 ofs1)
    (TAG: field_tag fid (co_members co) = Some tag)
    (* error in storing the tag *)
    (ERR: ~ Mem.valid_access m2 Mint32 b1 (Ptrofs.unsigned ofs1) Writable),
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le own m1)
| step_box_error1: forall le e p k m1 m2 f b ty own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    (* error in storing the size *)
    ~ Mem.valid_access m2 Mptr b (- size_chunk Mptr) Writable ->
    step_mem_error (State f (Sbox p e) k le own m1)
| step_box_error2: forall le e p k m1 m2 m3 f b ty own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* error in evaluating the rhs *)
    eval_expr_mem_error ge le m3 e ->
    step_mem_error (State f (Sbox p e) k le own m1)
| step_box_error3: forall le e p k m1 m2 m3 f b ty v v1 own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    (* error in storing the rhs *)
    assign_loc_mem_error ge ty m3 b Ptrofs.zero v1 ->
    step_mem_error (State f (Sbox p e) k le own m1)
| step_box_error4: forall le e p k m1 m2 m3 m4 f b ty v v1 own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* error in evaluating the address of lhs *)
    eval_place_mem_error ge le m4 p ->
    step_mem_error (State f (Sbox p e) k le own m1)
| step_box_error5: forall le e p k m1 m2 m3 m4 f b ty v v1 pb pofs own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    eval_place ge le m4 p pb pofs ->
    (* error in assigning the allocated block to the lhs *)
    assign_loc_mem_error ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) ->
    step_mem_error (State f (Sbox p e) k le own m1)
| step_dropplace_error: forall f st ps k le own m,
    step_dropplace_mem_error (Dropplace f st ps k le own m) ->
    step_mem_error (Dropplace f st ps k le own m)

| step_dropstate_error: forall id v s membs k m,
    step_drop_mem_error (Dropstate id v s membs k m) ->
    step_mem_error (Dropstate id v s membs k m)

| step_call_error1: forall f a al k le m p own,
    (* error in evaluating the function pointer *)
    eval_expr_mem_error ge le m a ->
    step_mem_error (State f (Scall p a al) k le own m)
| step_call_error2: forall f a al k le m  tyargs vf p own,
    eval_expr ge le m ge a vf ->
    (* error in evaluating the expression list *)
    eval_exprlist_mem_error ge le m ge al tyargs ->
    step_mem_error (State f (Scall p a al) k le own m)
| step_internal_function_error: forall vf f vargs k m e own1 own2
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (OWN1: init_own_env ge f = OK own1)
    (OWN2: init_place_list own1 (places_of_locals (fn_params f)) = own2),
    function_entry_mem_error f vargs m e ->
    step_mem_error (Callstate vf vargs k m)
(* | step_return_0_error: forall f k le m own, *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f (Sreturn p) k le own m) *)
| step_return_1_error1: forall f p k le m own,
    eval_expr_mem_error ge le m (Epure (Eplace p (typeof_place p)))->
    step_mem_error (State f (Sreturn p) k le own m)
| step_return_2_error2: forall f p k le m own,
    Mem.free_list m (blocks_of_env ge le) = None ->
    step_mem_error (State f (Sreturn p) k le own m)
| step_returnstate_error1: forall p v m f k e own,
    eval_place_mem_error ge e m p ->
    step_mem_error (Returnstate v (Kcall p f e own k) m)
| step_returnstate_error2: forall p v m f k e b ofs ty own,
    ty = typeof_place p ->
    eval_place ge e m p b ofs ->
    assign_loc_mem_error ge ty m b ofs v ->
    step_mem_error (Returnstate v (Kcall p f e own k) m)
| step_ifthenelse_error:  forall f a s1 s2 k e m own,
    eval_expr_mem_error ge e m a ->
    step_mem_error (State f (Sifthenelse a s1 s2) k e own m)
.
         

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

