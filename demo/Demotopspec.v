Require Import Integers Values Memory.
Require Import Clight.
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Require Import Demo Demospec DemoCspec.
Require Import Smallstep Linking SmallstepLinking.
Require Import LanguageInterface.


Definition s_unit :=
  {|
    gvar_info := tt;
    gvar_init := (Init_int32 Int.zero) :: (Init_int32 Int.zero) :: nil;
    gvar_readonly := false;
    gvar_volatile := false |}.

Definition memoized_unit :=
  {| 
    gvar_info := tt;
    gvar_init := Init_space 4000 :: nil;
    gvar_readonly := false;
    gvar_volatile := false |}.


Definition linked_skel : program unit unit :=
  {|
    prog_defs := (g_id, Gfun tt) :: (_s, Gvar s_unit) :: (f_id, Gfun tt) :: (_memoized, Gvar memoized_unit) :: nil;
    prog_public := f_id :: g_id :: f_id :: g_id :: nil;
    prog_main := main_id |}.

Theorem link_ok :
  link (skel L_C) (skel L_A) = Some linked_skel.
Proof. reflexivity. Qed.

Definition L := fun i : bool => if i then L_C else L_A.
Definition composed_spec := semantics L linked_skel.

Theorem link_result :
  compose L_C L_A = Some composed_spec.
Proof.
  unfold compose. rewrite link_ok. simpl. reflexivity.
Qed.


(** * C-level top specification *)

Inductive state :=
| Callf (i:int) (m:mem)
| Callg (i:int) (m:mem)
| Returnf (ret:int) (m:mem)
| Returng (ret:int) (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.

Context (se:Genv.symtbl).


Inductive initial_state : c_query -> state -> Prop :=
| initf i m fb
    (FINDF: Genv.find_symbol se f_id = Some fb):
    initial_state (cq (Vptr fb Ptrofs.zero) int_int_sg (Vint i :: nil) m) (Callf i m)
| initg i m gb
    (FINDF: Genv.find_symbol se g_id = Some gb):
    initial_state (cq (Vptr gb Ptrofs.zero) int_int_sg (Vint i :: nil) m) (Callg i m).

Inductive at_external : state -> c_query -> Prop :=.

Inductive after_external : state -> c_reply -> state -> Prop :=.

Inductive final_state : state -> c_reply -> Prop :=
| finalf ret m:
  final_state (Returnf ret m) (cr (Vint ret) m)
| finalg ret m:
  final_state (Returng ret m) (cr (Vint ret) m).

Definition valid_query (q: c_query) :=
  match (cq_vf q) with
  | Vptr b ofs =>  if Ptrofs.eq_dec ofs Ptrofs.zero then
                  match Genv.invert_symbol se b with
                  | Some 154%positive | Some 176%positive => true
                  | _ => false
                  end
                  else false
  |_  => false
  end.

Fixpoint sum_from_nat_rec i acc:=
  match i with
  | O => acc
  | S i' =>
      let acc' := Int.add acc (Int.repr (Z.of_nat i)) in
      sum_from_nat_rec i' acc'
  end.

Definition sum_from_nat (i: nat) :=
  sum_from_nat_rec i Int.zero.


Inductive sum_cache_memo mb sb m: nat -> int -> mem -> Prop :=
| sum_cache_memo_base:
  sum_cache_memo mb sb m O Int.zero m
| sum_cache_memo_cached n i sum
    (IEQ: i = Int.repr (Z.of_nat n))
    (INZ: i.(Int.intval) <> 0%Z)
    (LOAD: Mem.loadv Mint32 m (Vptr mb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) = Some (Vint sum))
    (SUMNZERO: sum.(Int.intval) <> 0%Z):
  sum_cache_memo mb sb m n sum m
| sum_cachef_memo_S n csum sum sum' m1 m2 i
    (IEQ: i = (Int.repr (Z.of_nat (S n))))
    (LOAD: Mem.loadv Mint32 m (Vptr mb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) = Some (Vint csum))
    (CSUMZERO: csum.(Int.intval) = 0%Z)
      (* sum = 1+2+..+n *)
    (CACHES: sum_cache_s mb sb m n sum m1)    
    (SUM: Int.add sum i = sum')
    (STORES0: Mem.storev Mint32 m1 (Vptr mb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Z.of_nat (S n))))) (Vint sum') = Some m2):
  sum_cache_memo mb sb m (S n) sum' m2
  
with sum_cache_s mb sb m : nat -> int ->  mem -> Prop :=
| sum_cache_s_base:
  sum_cache_s mb sb m O Int.zero m
| sum_cache_s_cached i i' n sum
    (IEQ: i = Int.repr (Z.of_nat n))
    (INZ: i.(Int.intval) <> 0%Z)
    (LOAD0: Mem.loadv Mint32 m (Vptr sb Ptrofs.zero) = Some (Vint i'))
    (LOAD1: Mem.loadv Mint32 m (Vptr sb (Ptrofs.repr 4)) = Some (Vint sum))
    (IEQI': Int.intval i = Int.intval i'):
    sum_cache_s mb sb m n sum m
| sum_cache_s_S n sum sum' m1 m2 m3 i i'
    (IEQ: i = (Int.repr (Z.of_nat (S n))))
    (LOAD0: Mem.loadv Mint32 m (Vptr sb Ptrofs.zero) = Some (Vint i'))
    (INEQI': Int.intval i <> Int.intval i')
    (* sum = 1+2+..+n *)
    (CACHEMEMO: sum_cache_memo mb sb m n sum m1)
    (SUM: Int.add sum i = sum')
    (STORES0: Mem.storev Mint32 m1 (Vptr sb Ptrofs.zero) (Vint i) = Some m2)
    (STORES1: Mem.storev Mint32 m2 (Vptr sb (Ptrofs.repr 4)) (Vint sum') = Some m3):
    sum_cache_s mb sb m (S n) sum' m3.

Inductive step : state -> trace -> state -> Prop :=
| stepf i n m m' mb sb sum fb gb
    (ItoN: Int.repr (Z.of_nat n) = i)
    (FINDMEMO: Genv.find_symbol se _memoized = Some mb)
    (FINDS: Genv.find_symbol se _s = Some sb)
    (FINDF: Genv.find_symbol se f_id = Some fb)
    (FINDG: Genv.find_symbol se g_id = Some gb)
    (CACHE: sum_cache_memo mb sb m n sum m'):
  step (Callf i m) E0 (Returnf sum m')
| stepg i n m m' mb sb sum fb gb
    (ItoN: Int.repr (Z.of_nat n) = i)
    (FINDMEMO: Genv.find_symbol se _memoized = Some mb)
    (FINDS: Genv.find_symbol se _s = Some sb)
    (FINDF: Genv.find_symbol se f_id = Some fb)
    (FINDG: Genv.find_symbol se g_id = Some gb)    
    (CACHE: sum_cache_s mb sb m n sum m'):
  step (Callg i m) E0 (Returng sum m').

End WITH_SE.

Program Definition top_spec : Smallstep.semantics li_c li_c :=
    {|
      Smallstep.skel := linked_skel;
      Smallstep.state := state;
      Smallstep.activate se :=
        {|
          Smallstep.step _ := step se;
          Smallstep.valid_query := valid_query se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external;
          Smallstep.after_external := after_external;
          Smallstep.final_state := final_state;
          globalenv := tt;
        |}
    |}.



(** * top_spec ⊑ (L_C ⊕ L_A) *)

Section MS.

Variable w: injp_world.
Variable se tse : Genv.symtbl.

Let tge1 := Clight.globalenv tse M_C.
Let tge2 := Genv.globalenv tse M_A.

Hypothesis MSTB : match_stbls injp w se tse.

Inductive match_state: state -> list (frame L) -> Prop :=
| match_callf i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Callf i m) (st L true (DemoCspec.Callstatef i tm) :: nil)
| match_callg i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Callg i m) (st L false (Demospec.Callstateg i tm) :: nil)
| match_returnf i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Returnf i m) (st L true (DemoCspec.Returnstatef i tm) :: nil)
| match_returng i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Returng i m) (st L false (Demospec.Returnstateg i tm) :: nil).

End MS.


Lemma intval_zero:
  Int.intval (Int.repr 0) = 0.
Proof.
  auto.
Qed.

Lemma intval_repr: forall z,
    Int.intval (Int.repr z) = Int.Z_mod_modulus z.
  auto.
Qed.

Lemma intval_Sn_nz: forall n,
    (Z.of_nat (S n)) < Int.modulus ->
    Int.intval (Int.repr (Z.of_nat (S n))) <> 0.
Proof.
  intro. rewrite intval_repr. rewrite Int.Z_mod_modulus_eq.
  rewrite Nat2Z.inj_succ. unfold Z.succ. intro.
  rewrite Z.mod_small. lia.
  lia.
Qed.

Lemma int_sub_one_sn: forall n,
    (Z.of_nat (S n)) < Int.modulus ->
    Int.sub (Int.repr (Z.of_nat (S n))) Int.one = Int.repr (Z.of_nat n).
Proof.
  intros.
  unfold Int.sub, Int.one. rewrite! Int.unsigned_repr. f_equal.
  lia. generalize Int.max_signed_pos. generalize Int.max_signed_unsigned.
  lia. unfold Int.max_unsigned.
  split. generalize Nat2Z.is_nonneg. lia.
  lia.
Qed.

Lemma exec_mem: forall n i m m' tm mb sb tmb tsb j sum (Hm: Mem.inject j m tm),
    i = Int.repr (Z.of_nat n) ->
    (Z.of_nat n) < Int.modulus ->
    j mb = Some (tmb,0) ->
    j sb = Some (tsb,0) ->
    (sum_cache_memo mb sb m n sum m' ->
    exists tm' Hm',
      sum_cache_memo tmb tsb tm n sum tm' /\
        injp_acc (injpw j m tm Hm) (injpw j m' tm' Hm')) /\
      (sum_cache_s mb sb m n sum m' ->
       exists tm' Hm',
         sum_cache_s tmb tsb tm n sum tm' /\
           injp_acc (injpw j m tm Hm) (injpw j m' tm' Hm')).
Proof.
  induction n;intros until Hm;intros IEQ BOUND INJM INJS.
  - split;intros CACHE.
    + inv CACHE.
      * exists tm,Hm. split.
      econstructor. reflexivity.
      * exists tm,Hm. split. eapply sum_cache_memo_cached;eauto.
        exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        reflexivity.
    + inv CACHE.
      * exists tm,Hm. split.
        econstructor. reflexivity.
      * exists tm,Hm. split. eapply sum_cache_s_cached;eauto.
        exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        exploit Mem.load_inject. eauto. eapply LOAD1. eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        reflexivity.
  - split;intros CACHE.
    + inv CACHE.
      (* cache hit *)
      * exists tm,Hm. split. eapply sum_cache_memo_cached;eauto.
        exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        reflexivity.
      (* cache miss *)
      * exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM.
        (* use I.H. *)
        exploit IHn. eauto. lia. eapply INJM. eapply INJS.
        intros (P1 & P2). eapply P2 in CACHES. clear P1 P2.
        destruct CACHES as (tm' & Hm' & CACHES' & INJP).
        exploit Mem.store_mapped_inject;eauto.
        rewrite Z.add_0_r.
        intros (tm'' & STORETM' & INJ).
        exists tm'', INJ. split.
        -- eapply sum_cachef_memo_S. eauto.
           eauto. auto. eapply CACHES'.
           auto. eauto.
        -- etransitivity. eapply INJP.
           eapply injp_acc_store;eauto.
           rewrite Z.add_0_r. auto.
    + inv CACHE.
      (* cache hit *)
      * exists tm,Hm. split. eapply sum_cache_s_cached;eauto.
        exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        exploit Mem.load_inject. eauto. eapply LOAD1. eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM. eauto.
        reflexivity.
      (* cache miss *)
      * exploit Mem.load_inject;eauto.
        intros (v & LOADTM & VINJ). inv VINJ.
        rewrite Z.add_0_r in LOADTM.
        (* use I.H. *)
        exploit IHn. eauto. lia. eapply INJM. eapply INJS.
        intros (P1 & P2). eapply P1 in CACHEMEMO. clear P1 P2.
        destruct CACHEMEMO as (tm' & Hm' & CACHEMEMO' & INJP).
        exploit Mem.store_mapped_inject. eauto. eapply STORES0. eauto.        
        eapply Val.inject_int.
        rewrite Z.add_0_r.
        intros (tm'' & STORETM' & INJ).
        exploit Mem.store_mapped_inject. eauto. eapply STORES1. eauto.        
        eapply Val.inject_int.
        rewrite Z.add_0_r.
        intros (tm''' & STORETM'' & INJ1).
        exists tm''', INJ1. split.
        -- eapply sum_cache_s_S. eauto.
           eauto. auto. eapply CACHEMEMO'.
           auto. eauto. eauto.
        -- etransitivity. eapply INJP.
           etransitivity.
           eapply injp_acc_store. eauto.
           rewrite Z.add_0_r. eauto. econstructor. eauto.
           instantiate (1:= INJ).
           eapply injp_acc_store;eauto.
           rewrite Z.add_0_r. auto.
Qed.

Section FIND_FUNCT.

Variable tse : Genv.symtbl.
Let tge1 := Clight.globalenv tse M_C.
Let tge2 := Genv.globalenv tse M_A.

Lemma find_fung_inf:
  forall gb,
  Genv.find_symbol tge1 g_id = Some gb ->
  Genv.find_funct tge1 (Vptr gb Ptrofs.zero) =
    Some (Ctypes.External (EF_external "g" int_int_sg) (Ctypes.Tcons Ctypesdefs.tint Ctypes.Tnil)  Ctypesdefs.tint cc_default).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold Genv.find_funct_ptr.
  unfold tge1 in *.
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

Lemma find_funf_inf:
  forall fb,
  Genv.find_symbol tge1 f_id = Some fb ->
  Genv.find_funct tge1 (Vptr fb Ptrofs.zero) =
    Some (Ctypes.Internal func_f).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold Genv.find_funct_ptr.
  unfold tge1 in *.
  rewrite Genv.find_def_spec.
  apply Genv.find_invert_symbol in H. cbn.
  simpl in H.
  rewrite H.  
  rewrite Maps.PTree.gss. reflexivity.
Qed.

  
Lemma find_funf_ing:
  forall fb,
  Genv.find_symbol tge2 f_id = Some fb ->
  Genv.find_funct tge2 (Vptr fb Ptrofs.zero) =
    Some (External (EF_external "f" int_int_sg)).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold Genv.find_funct_ptr.
  unfold tge2 in *.
  rewrite Genv.find_def_spec.
  apply Genv.find_invert_symbol in H. cbn.
  simpl in H.
  rewrite H.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold f_id, _s. congruence.
  unfold g_id, f_id. congruence.
Qed.


Lemma find_fung_ing:
  forall gb,
  Genv.find_symbol tge2 g_id = Some gb ->
  Genv.find_funct tge2 (Vptr gb Ptrofs.zero) =
    Some (Internal func_g).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold Genv.find_funct_ptr.
  unfold tge2 in *.
  rewrite Genv.find_def_spec.
  apply Genv.find_invert_symbol in H. cbn.
  simpl in H.
  rewrite H.  
  rewrite Maps.PTree.gss. reflexivity.
Qed.

  
Lemma exec_state: forall n i m m' mb sb fb gb sum k,
    i = Int.repr (Z.of_nat n) ->
    (Z.of_nat n) < Int.modulus ->
    Genv.find_symbol tse _memoized = Some mb ->
    Genv.find_symbol tse _s = Some sb ->
    Genv.find_symbol tse f_id = Some fb ->
    Genv.find_symbol tse g_id = Some gb ->
    (sum_cache_memo mb sb m n sum m' ->
     star (fun _ : unit => SmallstepLinking.step L tse) tt
       (st L true (DemoCspec.Callstatef i m) :: k) E0 (st L true (DemoCspec.Returnstatef sum m') :: k)) /\
    (sum_cache_s mb sb m n sum m' ->
     star (fun _ : unit => SmallstepLinking.step L tse) tt
       (st L false (Demospec.Callstateg i m) :: k) E0 (st L false (Demospec.Returnstateg sum m') :: k)).
Proof.
  induction n.
  - intros until k.
    intros IEQ LT FIND1 FIND2 FIND3 FIND4. split;intros SUMCACHE.
    + inv SUMCACHE.
      * eapply star_step;eauto. econstructor.
        simpl. eapply DemoCspec.step_zero. eauto.
        eapply star_refl;eauto. auto.
      * simpl in INZ. rewrite intval_zero in INZ.
        congruence.
    + inv SUMCACHE.
      * eapply star_step;eauto. econstructor.
        simpl. eapply Demospec.step_zero. eauto.
        eapply star_refl;eauto. auto.
      * simpl in INZ. rewrite intval_zero in INZ.
        congruence.
  - intros until k.
    intros IEQ LT FIND1 FIND2 FIND3 FIND4.
    split;intros SUMCACHE.
    + inv SUMCACHE.
      (* cache hits *)
      * eapply star_step;eauto. econstructor.
        simpl. eapply DemoCspec.step_sum_nz. eapply INZ.
        eapply SUMNZERO.
        eauto. eauto.
        eapply star_refl;eauto. auto.
      (* cache miss *)
      * eapply star_step;eauto. econstructor.
        eapply DemoCspec.step_call. 
        eapply intval_Sn_nz. lia.
        eapply CSUMZERO. eauto.
        eauto. simpl. unfold Genv.symbol_address. rewrite FIND4.
        eauto. congruence.
        (* step push *)
        eapply star_step;eauto. eapply step_push.
        econstructor.
        eapply find_fung_inf;eauto.
        instantiate (1:= false). simpl.
        unfold Genv.is_internal.
        erewrite find_fung_ing;eauto.
        econstructor. eapply find_fung_ing;eauto.
        (* use I.H. *)
        rewrite! int_sub_one_sn.
        eapply star_trans.
        exploit IHn;eauto. lia.
        intros (P1 & P2). eapply P2. eauto. 
        (* return from L_A *)
        eapply star_step;eauto. eapply step_pop.
        simpl. econstructor. simpl. econstructor.
        (* one step from returnstateg to returnstatef *)
        eapply star_step;eauto. econstructor. econstructor.
        simpl. unfold Genv.symbol_address. rewrite FIND1.
        eauto. unfold Ptrofs.of_ints. rewrite Int.signed_repr.
        eauto. unfold Int.max_unsigned. lia.
        eauto.
        eapply star_refl.
        all: eauto.
    + inv SUMCACHE.
      (* cache hits *)
      * eapply star_step;eauto. econstructor.
        simpl. eapply Demospec.step_read. eapply INZ.
        eapply IEQI'.
        eauto. eauto. eauto.
        eapply star_refl;eauto. auto.
      (* cache miss *)
      * eapply star_step;eauto. econstructor.
        eapply Demospec.step_call. 
        eapply intval_Sn_nz. lia.
        eauto.       
        eauto. simpl. unfold Genv.symbol_address. rewrite FIND3.
        eauto. congruence.
        eapply INEQI'.
        (* step push *)
        eapply star_step;eauto. eapply step_push.
        econstructor.
        eapply find_funf_ing;eauto.
        instantiate (1:= true). simpl.
        unfold Genv.is_internal.
        erewrite find_funf_inf;eauto.
        econstructor. eapply find_funf_inf;eauto.
        (* use I.H. *)
        rewrite! int_sub_one_sn.
        eapply star_trans.
        exploit IHn;eauto. lia.
        intros (P1 & P2). eapply P1. eauto. 
        (* return from L_A *)
        eapply star_step;eauto. eapply step_pop.
        simpl. econstructor. simpl. econstructor.
        (* one step from returnstateg to returnstatef *)
        eapply star_step;eauto. econstructor. econstructor.
        simpl. unfold Genv.symbol_address. rewrite FIND2.
        eauto. eauto. eauto. 
        eapply star_refl.
        all: eauto.
Qed.

End FIND_FUNCT.
