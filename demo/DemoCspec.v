Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.
Require Import ValueAnalysis.
Require Import LanguageInterface.
Require Import CallConv Compiler Invariant.
Require Import CKLRAlgebra Extends Inject InjectFootprint.
Require Import Asm Asmrel.
Require Import Integers.
Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.
Require Import Demo.


(** * C-level Abstract Specification for M_C *)

Inductive state: Type :=
| Callstatef
    (ai: int)
    (m: mem)
| Callstateg
    (vf: val)
    (aif: int)
    (m: mem)
| Returnstateg
    (aif: int)
    (rig: int)
    (m: mem)
| Returnstatef
    (ri: int)
    (m: mem).

Definition genv := Genv.t Clight.fundef Ctypes.type.

Section WITH_SE.
  Context (se: Genv.symtbl).
  
Inductive initial_state (ge:genv) : query li_c -> state -> Prop :=
| initial_state_intro
    v m i
    (FIND: Genv.find_funct ge v = Some (Ctypes.Internal func_f)):
    initial_state ge (cq v int_int_sg ((Vint i) :: nil) m) (Callstatef i m).

Inductive at_external (ge:genv): state -> query li_c -> Prop :=
| at_external_intro
    aif m vf id
    (FIND: Genv.find_funct ge vf = Some (Ctypes.External (EF_external id int_int_sg) (Tcons tint Tnil) tint cc_default)):
    at_external ge (Callstateg vf aif m) (cq vf int_int_sg ((Vint (Int.sub aif Int.one)) :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    aif ti m m' vf:
    after_external (Callstateg vf aif m) (cr (Vint ti) m') (Returnstateg aif ti m').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m
    (ZERO: i.(Int.intval) = 0%Z):
    step (Callstatef i m) E0 (Returnstatef (Int.zero) m)
| step_sum_nz
    i sum b_mem m
    (NZERO: i.(Int.intval) <> 0%Z)
    (SUMNZERO: sum.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)) ) = Some (Vint sum)):
      step (Callstatef i m) E0 (Returnstatef sum m)
| step_call
    i m sum b_mem vg
    (NZERO: i.(Int.intval) <> 0%Z)
    (SUMZERO: sum.(Int.intval) = 0%Z)
    (FINDM: Genv.find_symbol se _memoized = (Some b_mem))
    (LOAD: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) = Some (Vint sum))
    (FINDF: Genv.symbol_address se g_id Ptrofs.zero = vg)
    (VG: vg <> Vundef):
    step (Callstatef i m) E0 (Callstateg vg i m)
| step_return
    b_mem m m' sum sum' i
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE: Mem.storev Mint32 m (Vptr b_mem (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) (Vint sum') = Some m')
    (SUM: sum' = Int.add sum i):
    step (Returnstateg i sum m) E0 (Returnstatef sum' m').

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      s m:
      final_state (Returnstatef s m) (cr (Vint s) m).

End WITH_SE.

(** The specification of M_C  *)
Definition L_C : Smallstep.semantics li_c li_c :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv M_C.

(** ** Refinement: L_C ⫹ (semantics M_C) *)

Definition cont_callg sp le:=
  (Kcall (Some _t'1) func_f (Maps.PTree.set _x (sp, tint) empty_env)
          le
          (Kseq
             (Sset _t (Ebinop Oadd (Etempvar _t'1 tint) (Evar _x tint) tint))
             (Kseq
                (Sassign
                   (Ederef
                      (Ebinop Oadd (Evar _memoized (tarray tint 1000))
                         (Evar _x tint) (tptr tint)) tint)
                   (Etempvar _t tint))
                (Kseq (Sreturn (Some (Etempvar _t tint))) Kstop)))).

Section MS.

Variable w: injp_world.
Variable se tse : Genv.symtbl.

Let tge := Clight.globalenv tse M_C.

Hypothesis MSTB : match_stbls injp w se tse.

(** Definition of the simulation relation  *)
Inductive match_state : state -> Clight.state -> Prop :=
| match_callf i m tm vf j Hm
    (FINDF: Genv.find_funct tge vf = Some (Ctypes.Internal func_f))
    (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Callstatef i m) (Callstate vf (Vint i :: nil) Kstop tm)
| match_callg i m tm vg tvg j Hm sp le m0 tm0 f Hm0
    (* (FINDF: Genv.find_funct tge vg = Some (Ctypes.External (EF_external "g" int_int_sg) (Tcons tint Tnil) tint cc_default)) *)
    (VINJ: Val.inject j vg tvg)
    (INJP: injp_acc w (injpw j m tm Hm))
    (WORLD: w = injpw f m0 tm0 Hm0)
    (INVALID: ~ Mem.valid_block tm0 sp)
    (OUTREACH: forall ofs, 0<= ofs < 4 -> loc_out_of_reach j m sp ofs)
    (FREEABLE: Mem.range_perm tm sp 0 4 Cur Freeable)
    (LOADSP: Mem.load Mint32 tm sp 0 = Some (Vint i)):
  match_state (Callstateg vg i m) (Callstate tvg (Vint (Int.sub i Int.one) :: nil) (cont_callg sp le) tm)
| match_returng i sum m tm j Hm sp le m0 tm0 f Hm0
    (INJP: injp_acc w (injpw j m tm Hm))
    (WORLD: w = injpw f m0 tm0 Hm0)
    (INVALID: ~ Mem.valid_block tm0 sp)
    (OUTREACH: forall ofs, 0<= ofs < 4 -> loc_out_of_reach j m sp ofs)
    (FREEABLE: Mem.range_perm tm sp 0 4 Cur Freeable)
    (LOADSP: Mem.load Mint32 tm sp 0 = Some (Vint i)):
  match_state (Returnstateg i sum m) (Returnstate (Vint sum) (cont_callg sp le) tm)
| match_returnf sum m tm j Hm
    (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Returnstatef sum m) (Returnstate (Vint sum) Kstop tm).

Lemma find_fung_inf:
  forall gb,
  Genv.find_symbol tge g_id = Some gb ->
  Genv.find_funct tge (Vptr gb Ptrofs.zero) =
    Some (Ctypes.External (EF_external "g" int_int_sg) (Ctypes.Tcons Ctypesdefs.tint Ctypes.Tnil)  Ctypesdefs.tint cc_default).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold Genv.find_funct_ptr.
  unfold tge in *.
  rewrite Genv.find_def_spec.
  apply Genv.find_invert_symbol in H. cbn.
  simpl in H.
  rewrite H.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold g_id, _memoized. congruence.
  unfold g_id, f_id. congruence.
Qed.

End MS.

Lemma intval_zero:
  Int.intval (Int.repr 0) = 0.
Proof.
  auto.
Qed.

Lemma int_one_not_eq_zero:
  Int.eq Int.one Int.zero = false.
Proof.
  destruct (Int.eq Int.one Int.zero) eqn:EQ. exfalso.
  eapply Int.one_not_zero. exploit Int.eq_spec. rewrite EQ.
  auto. auto.
Qed.

Lemma sem_cast_int_int: forall v m,
    Cop.sem_cast (Vint v) Ctypesdefs.tint Ctypesdefs.tint m = Some (Vint v).
Proof.
  intros.
  unfold Cop.sem_cast. simpl.
  destruct Archi.ptr64. simpl. auto.
  destruct Ctypes.intsize_eq;try congruence.
Qed.

Lemma sem_cmp_int_int: forall v1 v2 m c,
    Cop.sem_cmp c (Vint v1) Ctypesdefs.tint (Vint v2) Ctypesdefs.tint m = Some (Val.of_bool (Int.cmp c v1 v2)).
Proof.
  intros. unfold Cop.sem_cmp. simpl.
  unfold Cop.sem_binarith. simpl. repeat rewrite sem_cast_int_int.
  auto.
Qed.

Lemma intval_zero_int_zero: forall i,
    Int.intval i = 0 -> Int.eq i (Int.repr 0) = true.
Proof.
  intros. 
  rewrite Int.eq_signed. rewrite Int.signed_repr.
  destruct i. simpl in H. subst.
  simpl. auto.
  generalize Int.min_signed_neg.
  generalize Int.max_signed_pos. lia.
Qed.

Lemma intval_nzero_int_nzero: forall i,
    Int.intval i <> 0 -> Int.eq i (Int.repr 0) = false.
Proof.
  intros.
  eapply Int.eq_false. intro. subst.
  rewrite intval_zero in H. congruence.
Qed.


(* i == 0 *)
Lemma exec_mem1: forall j m tm i (Hm :Mem.inject j m tm),
  exists tm1 sp tm2 tm3 Hm' Hm'',
    Mem.alloc tm 0 4 =(tm1,sp) /\
      Mem.store Mint32 tm1 sp 0 (Vint i) = Some tm2 /\
      Mem.free tm2 sp 0 4 = Some tm3 /\
      injp_acc (injpw j m tm Hm) (injpw j m tm2 Hm') /\
      injp_acc (injpw j m tm Hm) (injpw j m tm3 Hm'').
Proof.
  intros.
  destruct (Mem.alloc tm 0 4) as [tm1 sp] eqn:ALLOCTM .
  exists tm1,sp.
  exploit Mem.alloc_right_inject;eauto. intros INJ1.
  assert ({ tm2 : mem | Mem.store Mint32 tm1 sp 0 (Vint i) = Some tm2}).
  eapply Mem.valid_access_store.
  eapply Mem.valid_access_implies.
  eapply Mem.valid_access_alloc_same;simpl;eauto.
  lia. lia. apply Z.divide_0_r. econstructor.
  destruct X as (tm2 & STORETM1).
  exists tm2.
  exploit Mem.store_outside_inject;eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ2.
  (* free *)
  assert (FREE: {tm3:mem | Mem.free tm2 sp 0 4 = Some tm3}).
  eapply Mem.range_perm_free.
  unfold Mem.range_perm. intros .
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_2;eauto.
  destruct FREE as (tm3 & FREE).
  exists tm3.
  exploit Mem.free_right_inject. eapply INJ2. eauto.
  intros.  eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ3.
  exists INJ2,INJ3.
  (* injp acc *)
  assert (RO1: ro_acc m m).
  eapply ro_acc_refl.
  assert (RO3: ro_acc tm tm3).
  eapply ro_acc_trans. eapply ro_acc_alloc;eauto.
  eapply ro_acc_trans. eapply ro_acc_store;eauto.
  eapply ro_acc_free;eauto.
  assert (RO2: ro_acc tm tm2).
  eapply ro_acc_trans. eapply ro_acc_alloc;eauto.
  eapply ro_acc_store;eauto.
  inv RO1. inv RO2. inv RO3.
  assert (INJP1: injp_acc (injpw j m tm Hm) (injpw j m tm2 INJ2)).  
  econstructor;eauto.
  eapply Mem.unchanged_on_refl.
  econstructor;eauto.
  (* unchanged_on_perm *)
  intros.
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. auto.
  eapply iff_trans. split. eapply Mem.perm_alloc_1;eauto.
  intros. eapply Mem.perm_alloc_4;eauto.
  split. eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_store_2;eauto.
  (* mem contents *)
  intros.
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. eapply Mem.perm_valid_block;eauto.
  assert (PERM1: Mem.perm tm1 b ofs Cur Readable).
  eapply Mem.perm_alloc_1;eauto.
  assert (PERM2: Mem.perm tm2 b ofs Cur Readable).
  eapply Mem.perm_store_1;eauto.
  etransitivity.
  eapply Mem.store_unchanged_on with (P:= fun b _ => b <> sp);eauto.
  eapply Mem.alloc_unchanged_on;eauto.
  eapply inject_separated_refl.
  repeat apply conj;eauto.
  econstructor;eauto.
  eapply Mem.unchanged_on_refl.
  inv INJP1.
  econstructor;eauto;intros.  
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. auto.
  etransitivity. eapply H19;eauto.    
  split. eapply Mem.perm_free_1;eauto.
  eapply Mem.perm_free_3;eauto.
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. eapply Mem.perm_valid_block;eauto.
  assert (PERM1: Mem.perm tm1 b ofs Cur Readable).
  eapply Mem.perm_alloc_1;eauto.
  assert (PERM2: Mem.perm tm2 b ofs Cur Readable).
  eapply Mem.perm_store_1;eauto.
  assert (PERM3: Mem.perm tm3 b ofs Cur Readable).
  eapply Mem.perm_free_1;eauto.
  etransitivity.
  eapply Mem.free_unchanged_on with (P:= fun b _ => b <> sp);eauto.
  eapply H19;eauto.
  eapply inject_separated_refl.
Qed.

  
  
  
(* i<>0. sum<>0 *)
Lemma exec_mem2: forall j m tm i mb tmb ofs sum (Hm :Mem.inject j m tm),
    Mem.loadv Mint32 m (Vptr mb ofs) = Some (Vint sum) ->
    j mb = Some (tmb,0) ->
  exists tm1 sp tm2 tm3 Hm',
    Mem.alloc tm 0 4 =(tm1,sp) /\
      Mem.store Mint32 tm1 sp 0 (Vint i) = Some tm2 /\
      Mem.loadv Mint32 tm2 (Vptr tmb ofs) = Some (Vint sum) /\
      Mem.free tm2 sp 0 4 = Some tm3 /\
      injp_acc (injpw j m tm Hm) (injpw j m tm3 Hm').
Proof.
  intros until Hm. intros LOADM INJMB.
  exploit exec_mem1.  
  intros (tm1 & sp & tm2 & tm3 & Hm' & Hm'' & ALLOCTM & STORETM1 & FREETM2 & INJP1 & INJP2).
  instantiate (1:= tm) in ALLOCTM.
  instantiate (1:= m) in Hm'. instantiate (1:= j) in Hm'.
  exists tm1,sp,tm2.
  exploit Mem.load_inject. eapply Hm'. eapply LOADM. eauto.
  rewrite Z.add_0_r. intros (v & LOADTM2 & VINJ).
  inv VINJ.
  exists tm3,Hm''.
  repeat eapply conj;eauto.
Qed.
  

(* i<>0. sum==0, before call g *)
Lemma exec_mem3: forall j m tm i mb tmb ofs sum (Hm :Mem.inject j m tm),
    Mem.loadv Mint32 m (Vptr mb ofs) = Some (Vint sum) ->
    j mb = Some (tmb,0) ->
  exists tm1 sp tm2 Hm',
    Mem.alloc tm 0 4 =(tm1,sp) /\
      Mem.store Mint32 tm1 sp 0 (Vint i) = Some tm2 /\
      Mem.loadv Mint32 tm2 (Vptr tmb ofs) = Some (Vint sum) /\
      Mem.range_perm tm2 sp 0 4 Cur Freeable /\
      injp_acc (injpw j m tm Hm) (injpw j m tm2 Hm').
Proof.
  intros until Hm. intros LOADM INJMB.
  exploit exec_mem1.  
  intros (tm1 & sp & tm2 & tm3 & Hm' & Hm'' & ALLOCTM & STORETM1 & FREETM2 & INJP1 & INJP2).
  instantiate (1:= tm) in ALLOCTM.
  instantiate (1:= m) in Hm'. instantiate (1:= j) in Hm'.
  exists tm1,sp,tm2.
  exploit Mem.load_inject. eapply Hm'. eapply LOADM. eauto.
  rewrite Z.add_0_r. intros (v & LOADTM2 & VINJ).
  inv VINJ.
  exists Hm'.
  repeat apply conj;eauto.
  (* range perm freeable *)
  eapply Mem.free_range_perm;eauto.
Qed.  

(* continuation after returning from g *)
Lemma exec_mem4: forall j m m1 tm mb tmb sp ofs sum (Hm: Mem.inject j m tm),
          Mem.store Mint32 m mb ofs (Vint sum) = Some m1 ->
          j mb = Some (tmb,0) ->
          Mem.range_perm tm sp 0 4 Cur Freeable ->
          (forall ofs, 0 <= ofs < 4 -> loc_out_of_reach j m sp ofs) ->
          exists tm1 tm2 Hm',
            Mem.store Mint32 tm tmb ofs (Vint sum) = Some tm1 /\
              Mem.free tm1 sp 0 4 = Some tm2 /\
              injp_acc (injpw j m tm Hm) (injpw j m1 tm1 Hm') /\
              Mem.inject j m1 tm2.
Proof.
  intros until Hm.
  intros STORE INJMB PERM OUT.
  exploit Mem.store_mapped_inject;eauto.
  intros (tm1 & STORETM & INJ1).
  assert (FREE: { tm2: mem | Mem.free tm1 sp 0 4 = Some tm2}).
  eapply Mem.range_perm_free. unfold Mem.range_perm. intros.
  eapply Mem.perm_store_1;eauto.
  destruct FREE as (tm2 & FREE).
  exists tm1,tm2,INJ1.
  exploit Mem.free_right_inject;eauto.
  assert (OUT1: forall ofs : Z, 0 <= ofs < 4 -> loc_out_of_reach j m1 sp ofs).
  { intros. unfold loc_out_of_reach.
    intros. intro. eapply OUT;eauto.
    eapply Mem.perm_store_2;eauto. }    
  intros.
  eapply OUT1. instantiate (1 := ofs0 + delta).
  eauto. eauto. rewrite <-Z.add_sub_assoc.
  rewrite Z.sub_diag. rewrite Z.add_0_r.
  eapply Mem.perm_implies. instantiate (1:= p).
  destruct k. eauto.
  eapply Mem.perm_cur_max. eauto. destruct p;econstructor.
  intros INJ2.
  rewrite Z.add_0_r in *.
  repeat eapply conj;eauto.
  (* injp_acc *)
  eapply injp_acc_store;eauto. rewrite Z.add_0_r.
  auto.
Qed.

Lemma match_program_id :
  match_program (fun _ f0 tf => tf = id f0) eq M_C M_C.
Proof.
  red. red. constructor; eauto.
    constructor. constructor. eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor. constructor; eauto. constructor; eauto.
    constructor; eauto.
    constructor; eauto. constructor; eauto. simpl. econstructor; eauto.
    apply linkorder_refl.
    constructor.
Qed.

(** L_C ⫹_injp (semantics M_C) *)
Lemma cspec_simulation:
  forward_simulation (cc_c injp) (cc_c injp) L_C (Clight.semantics1 M_C).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state w se2 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  destruct w as [f0 m0 tm0 Hm0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  (* valid query *)
  - intros. inv H. simpl in *.
    eapply Genv.is_internal_transf. eapply match_program_id.
    eauto. eauto. eauto. auto.
  (* initial state *)
  - intros. simpl in *. inv H0.
    inv H. inv H6. inv H3. inv H1.
    inv Hse.
    simpl in *. inv H7.
    exists (Callstate vf2 (Vint i :: nil) Kstop m2).
    assert (FINDF: Genv.find_funct (globalenv se2
       {|
       prog_defs := global_definitions_c;
       prog_public := public_idents_c;
       prog_main := main_id;
       prog_types := composites;
       prog_comp_env := Maps.PTree.empty composite;
       prog_comp_env_eq := eq_refl |}) vf2 = Some (Internal func_f)).
    { eapply Genv.find_funct_transf in FIND.
      instantiate (1:= id) in FIND. unfold id in FIND.
      unfold globalenv. simpl. eauto.
      eapply match_program_id. eauto.
      auto. }
    
    split.
    set (targs:= (Ctypes.Tcons (Ctypes.Tint Ctypes.I32 Ctypes.Signed {| Ctypes.attr_volatile := false; Ctypes.attr_alignas := None |}) Ctypes.Tnil)).
    assert (Ctypes.signature_of_type targs tint cc_default = int_int_sg).
    eauto.
     replace ({|
                 cq_vf := vf2;
                 cq_sg := int_int_sg;
                 cq_args := Vint i :: nil;
                 cq_mem := m2 |}) with
       (cq vf2 (Ctypes.signature_of_type targs tint cc_default) (Vint i :: nil) m2) by auto.
     econstructor. eauto. 
     auto. econstructor. econstructor. eauto.
     econstructor.
     simpl. eauto.
     econstructor. unfold globalenv. simpl. eauto.
     reflexivity.
  (* final *)
  - simpl. intros.
    inv H0. inv H. exists (cr (Vint s) tm).
    split. econstructor.
    econstructor. split. eapply INJP.
    econstructor. econstructor. econstructor.
  (* at external *)
  - simpl. intros.
    inv H0. inv H. inv Hse.
    generalize INJP. intros INJP1.
    inv INJP.
    eapply Genv.match_stbls_incr in H2;eauto.
    2:{ intros. exploit H15; eauto. intros [A B].
        unfold Mem.valid_block in *. split; eauto with mem. }
    exists (injpw j m tm Hm), (cq tvg int_int_sg (Vint (Int.sub aif Int.one) :: nil)tm).
    repeat apply conj.
    + econstructor. simpl.
      generalize  match_program_id. intro TRAN.
      eapply Genv.find_funct_transf in TRAN; eauto.
    + econstructor;eauto. econstructor. 
      eapply Genv.find_funct_inv in FIND.
      destruct FIND. subst. congruence.
    + econstructor. eauto. 
      eapply Mem.sup_include_trans. eauto. eapply H12.
      eapply Mem.sup_include_trans. eauto. eapply H13.
    (* after external *)
    + intros. inv H. destruct H1.
      simpl in H. generalize H. intros INJP2.
      inv H. inv H1. inv H0.
      eexists. split.
      econstructor.
      inv H. inv H3.
      econstructor.
      instantiate (1:= Hm').
      etransitivity;eauto. 
      eauto.
      (* sp invalid block *)
      eauto.
      (* sp out of reach *)
      intros. eapply loc_out_of_reach_incr.
      eauto. eapply inject_implies_dom_in;eauto.
      eauto. eauto. instantiate (1:= tm).
      eapply Mem.perm_valid_block. eapply FREEABLE. eauto.
      unfold inject_incr_disjoint. intros.
      eapply H24;eauto.
      (* sp range perm *)      
      unfold Mem.range_perm. intros.
      eapply H21. eapply OUTREACH. auto.
      (* valid block sp in tm*)
      eapply Mem.perm_valid_block. eapply FREEABLE. eauto.
      eauto.
      (* load sp equals i *)
      eapply Mem.load_unchanged_on;eauto.
      
  (* step *)
  - simpl. intros s1 t s2' STEP s2 MATCH.
    inv STEP;inv MATCH;cbn in *.
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP1.
      inv INJP1. inv Hse.           
      exploit (exec_mem1 j m tm i). instantiate (1 := Hm).
      intros (tm1 & sp & tm2 & tm3 & Hm'' & Hm' & ALLOCTM & STORETM1 & FREETM2 & INJPUNUSE & INJP2).
      clear Hm'' INJPUNUSE.
      eexists. split.
      econstructor.
      (* function entry *)
      econstructor. simpl. eauto.
      econstructor. simpl. econstructor. eapply in_nil.
      constructor.
      econstructor. eauto.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eauto.
      econstructor. simpl. eauto.
      (* i == 0 *)
      eapply star_step. econstructor.
      eapply star_step. econstructor.
      econstructor. econstructor. eapply eval_Evar_local.
      eapply Maps.PTree.gss. econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      econstructor. econstructor. simpl.
      rewrite intval_zero_int_zero;eauto.
      unfold bool_val. simpl.
      rewrite int_one_not_eq_zero. simpl. eauto.
      simpl.
      (* free sp *)
      eapply star_step. econstructor.
      econstructor. simpl. eapply sem_cast_int_int.
      simpl. rewrite FREETM2.
      eauto.
      (* return *)
      simpl.
      eapply star_refl.
      all: eauto.
      
      (* match state *)
      econstructor. etransitivity.
      eauto. eauto.
      
    (* i <> 0 , sum <> 0 *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP1.
      inv INJP1. inv Hse.
      eapply Genv.find_symbol_match in FINDM as FINDM';eauto.
      destruct FINDM' as (tmb & INJM & FINDM').
      exploit exec_mem2. eauto. eapply H9. eauto.
      intros (tm1 & sp & tm2 & tm3 & Hm' & ALLOCTM & STORETM1 & LOADTM2 & FREETM2 & INJP2).
      instantiate (1 := Hm) in INJP2.
      instantiate (1 := i) in STORETM1.
      eexists. split.
      (* function entry *)
      econstructor. simpl. eauto.
      econstructor. simpl. eauto.
      econstructor. simpl. econstructor. eapply in_nil.
      constructor.
      econstructor. eauto.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eauto.
      econstructor. simpl. eauto.
      (* i<>0 *)
      eapply star_step. econstructor.
      eapply star_step. econstructor.
      econstructor. econstructor. eapply eval_Evar_local.
      eapply Maps.PTree.gss. econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      econstructor. econstructor. simpl.
      rewrite intval_nzero_int_nzero;eauto.
      unfold bool_val. simpl.
      rewrite Int.eq_true. eauto.
      simpl.
      (* load memoize[i] *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      (* evaluate memoize *)
      econstructor. econstructor. econstructor.
      econstructor.
      eapply eval_Evar_global. auto.
      eauto. eapply deref_loc_reference. simpl. auto.
      econstructor. econstructor.
      eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      simpl. unfold sem_add. simpl.
      rewrite Ptrofs.add_zero_l. eauto.      
      econstructor.  simpl. eauto. eauto.
      (* sum <> 0 *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl.
      erewrite sem_cmp_int_int. simpl.
      rewrite intval_nzero_int_nzero;eauto.
      simpl. unfold bool_val;simpl.
      rewrite Int.eq_true. eauto.
      simpl.
      (* return *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. eapply Maps.PTree.gss.
      simpl. rewrite sem_cast_int_int. eauto.
      simpl. rewrite FREETM2.
      eauto.
      eapply star_refl.
      all:eauto.

      (* match state *)
      econstructor. etransitivity;eauto.

    (* i<>0, sum==0 *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP1.
      inv INJP1. inv Hse.
      eapply Genv.find_symbol_match in FINDM as FINDM';eauto.
      destruct FINDM' as (tmb & INJM & FINDM').
      unfold Genv.symbol_address in VG.
      destruct (Genv.find_symbol se1 g_id) eqn:FINDG.
      2: congruence.
      eapply Genv.find_symbol_match in FINDG as FINDG';eauto.
      destruct FINDG' as (tgb & INJG & FINDG').      
      exploit exec_mem3. eauto. eapply H9. eauto.
      intros (tm1 & sp & tm2 & Hm' & ALLOCTM & STORETM1 & LOADTM2 & SPFREE & INJP2).
      instantiate (1 := Hm) in INJP2.
      instantiate (1 := i) in STORETM1.
      eexists. split.
      (* function entry *)
      econstructor. simpl. eauto.
      econstructor. simpl. eauto.
      econstructor. simpl. econstructor. eapply in_nil.
      constructor.
      econstructor. eauto.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eauto.
      econstructor. simpl. eauto.
      (* i<>0 *)
      eapply star_step. econstructor.
      eapply star_step. econstructor.
      econstructor. econstructor. eapply eval_Evar_local.
      eapply Maps.PTree.gss. econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      econstructor. econstructor. simpl.
      rewrite intval_nzero_int_nzero;eauto.
      unfold bool_val. simpl.
      rewrite Int.eq_true. eauto.
      simpl.
      (* load memoize[i] *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      (* evaluate memoize *)
      econstructor. econstructor. econstructor.
      econstructor.
      eapply eval_Evar_global. auto.
      eauto. eapply deref_loc_reference. simpl. auto.
      econstructor. econstructor.
      eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      simpl. unfold sem_add. simpl.
      rewrite Ptrofs.add_zero_l. eauto.      
      econstructor.  simpl. eauto. eauto.
      (* sum == 0 *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl.
      erewrite sem_cmp_int_int. simpl.
      rewrite intval_zero_int_zero;eauto.
      simpl. unfold bool_val;simpl.
      rewrite int_one_not_eq_zero. eauto.
      simpl.
      (* evaluate the arguments of callg *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      simpl. eauto.
      econstructor. eapply eval_Evar_global. auto.
      eauto.
      eapply deref_loc_reference. simpl. auto.
      econstructor. econstructor. econstructor.
      econstructor. eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eapply Mem.load_store_same;eauto.
      econstructor. simpl.
      unfold sem_sub. simpl. unfold sem_binarith. simpl.
      rewrite! sem_cast_int_int. eauto.
      simpl. rewrite! sem_cast_int_int. eauto.
      econstructor.
      eapply find_fung_inf;eauto.
      simpl. auto.
      eapply star_refl.
      all:eauto.

      (* match state *)
      econstructor.
      unfold Genv.symbol_address. rewrite FINDG.
      instantiate (1:= j).
      econstructor;eauto.
      etransitivity;eauto.
      eauto.
      (* invalid sp in m2 *)
      intro.
      eapply Mem.fresh_block_alloc. eapply ALLOCTM.
      eapply H8. eauto.
      (* sp is out_of_reach in m *)
      intros. unfold loc_out_of_reach. intros.
      intro. eapply Mem.fresh_block_alloc. eapply ALLOCTM.
      eapply Mem.perm_valid_block in H1.
      eapply Mem.valid_block_inject_2;eauto.
      (* sp freeable *)
      eauto.
      (* load sp *)
      eapply Mem.load_store_same in STORETM1;eauto.
      
    (* continuation of return g *)      
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP1.
      inv INJP1. inv Hse.
      eapply Genv.find_symbol_match in FINDM as FINDM';eauto.
      destruct FINDM' as (tmb & INJM & FINDM').
      exploit exec_mem4. eauto. eapply H11. eauto.
      eauto. eauto. instantiate (1:= Hm).
      intros (tm1 & tm2 & INJM' & STORETM & FREETM1 & INJP2 & INJ).
      eexists. split.
      (* set _t' *)
      econstructor. econstructor. 
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. econstructor. simpl.
      eapply Maps.PTree.gss.
      econstructor. econstructor. eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eauto.
      simpl. unfold sem_add. simpl. unfold sem_binarith. simpl.
      rewrite! sem_cast_int_int. eauto.
      (* set memo *)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. econstructor. econstructor.
      eapply eval_Evar_global. auto. eauto.
      eapply deref_loc_reference. simpl. auto.
      econstructor. eapply eval_Evar_local.
      eapply Maps.PTree.gss.
      econstructor. simpl. eauto.
      eauto.
      simpl. unfold sem_add. simpl. unfold sem_binarith. simpl.
      rewrite Ptrofs.add_zero_l. eauto.
      econstructor. eapply Maps.PTree.gss.
      simpl. rewrite sem_cast_int_int.
      eauto.
      econstructor. simpl. eauto.
      eauto.
      (* return, free*)
      eapply star_step;eauto. econstructor.
      eapply star_step;eauto. econstructor.
      econstructor. eapply Maps.PTree.gss.
      simpl. rewrite sem_cast_int_int. eauto.
      simpl. rewrite FREETM1.
      eauto. simpl.
      eapply star_refl.
      eauto.

      (* match_state *)
      econstructor.
      instantiate (1:= INJ).
      assert (INJP3: injp_acc (injpw f m1 tm0 Hm0) (injpw j m' tm1 INJM')).
      etransitivity;eauto.
      assert (RO1: ro_acc m1 m' ).
      eapply ro_acc_trans. instantiate (1:= m).
      econstructor. eauto. eapply H9. eauto.
      eapply ro_acc_store;eauto.
      assert (RO2: ro_acc tm0 tm2).
      eapply ro_acc_trans. instantiate (1:= tm).
      econstructor. eauto. eapply H10. eauto.
      eapply ro_acc_trans. eapply ro_acc_store;eauto.
      eapply ro_acc_free;eauto.
      inv RO1. inv RO2.
      econstructor;eauto.
      eapply Mem.unchanged_on_trans. eauto.
      eapply Mem.store_unchanged_on;eauto.
      intros. unfold loc_unmapped. rewrite INJM.
      congruence.
      (* unchanged_on tm *)
      econstructor;eauto.
      (* perm *)
      intros.
      assert (b <> sp). intro. subst. congruence.
      etransitivity. eapply H10;eauto.
      etransitivity.
      split.
      eapply Mem.perm_store_1. eauto.
      eapply Mem.perm_store_2. eauto.
      split.
      eapply Mem.perm_free_1. eauto. left. auto.
      eapply Mem.perm_free_3. eauto.
      (* contents *)
      intros.
      assert (b <> sp). intro. subst.
      eapply INVALID. eapply Mem.perm_valid_block. eauto.
      etransitivity.
      eapply Mem.free_unchanged_on. eauto.
      instantiate (1:= fun b _ => b <> sp). simpl. intros.
      congruence. simpl. auto.
      eapply Mem.perm_store_1;eauto.
      eapply H10;eauto.
      eapply Mem.perm_valid_block. eauto.
      etransitivity.
      inv INJP3. eapply H30. eauto. auto.
      eauto.

  - constructor. intros. inv H.
Qed.


Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_callf : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callstatef i m)
| sound_callg : forall i m vg,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callstateg vg i m)
| sound_returnf : forall i sum m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Returnstateg i sum m)
| sound_returng : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Returnstatef i m).

End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma LC_ro : preserves L_C ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0;inv H.
    + econstructor;eauto.
    + econstructor;eauto.
    + econstructor;eauto.
    + econstructor;eauto.
      eapply ro_acc_trans. eauto.
      eapply ro_acc_store. eauto.
      eapply ro_acc_sound. eauto.
      eapply ro_acc_store. eauto.
  - intros.
    inv H;inv H0.
    econstructor. eapply ro_acc_refl.
    eauto.
  - intros. inv H0;inv H.
    exists (row se1 m). split;auto.
    split. econstructor. eauto.
    intros.
    inv H;inv H0. econstructor;eauto.
    eapply ro_acc_trans;eauto.
    eapply ro_acc_sound;eauto.
  - intros. inv H0;inv H.    
    econstructor. auto.
Qed.

(** L_C ⫹_ro L_C  *)
Theorem cspec_ro :
  forward_simulation ro ro L_C L_C.
Proof.
  eapply preserves_fsim. eapply LC_ro; eauto.
Qed.

(** L_C ⫹_wt L_C  *)
Theorem cspec_self_simulation_wt :
  forward_simulation wt_c wt_c L_C L_C.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [se' sg].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd w = int_int_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. reflexivity.
  - intros. inv H. exists s1. exists s1. constructor; eauto. inv H0.
    inv H1. cbn. eauto.   
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
  - intros. subst.
    exists (se2, int_int_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0. econstructor. simpl. auto.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H.  auto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.


