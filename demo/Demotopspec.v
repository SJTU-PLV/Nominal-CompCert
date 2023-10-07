Require Import Integers Values Memory.
Require Import Clight.
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Require Import Demo Demospec DemoCspec.
Require Import Smallstep Linking SmallstepLinking.
Require Import LanguageInterface Compiler.

(** * C-level composed specification *)

(** Definition of the semantics linking between L_C (specification of M_C) and L_A (specification of M_A) *)

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


(** ** C-level top specification *)

Inductive state :=
| Callf (i:int) (m:mem)
| Callg (i:int) (m:mem)
| Returnf (ret:int) (m:mem)
| Returng (ret:int) (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.

Context (se:Genv.symtbl).


Inductive initial_state : c_query -> state -> Prop :=
| initf i m fb n
    (FINDF: Genv.find_symbol se f_id = Some fb)
    (IEQ:  i = (Int.repr (Z.of_nat n)))
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed):
    initial_state (cq (Vptr fb Ptrofs.zero) int_int_sg (Vint i :: nil) m) (Callf i m)
| initg i m gb n
    (FINDF: Genv.find_symbol se g_id = Some gb)
    (IEQ:  i = (Int.repr (Z.of_nat n)))
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed):
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
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed)
    (FINDMEMO: Genv.find_symbol se _memoized = Some mb)
    (FINDS: Genv.find_symbol se _s = Some sb)
    (FINDF: Genv.find_symbol se f_id = Some fb)
    (FINDG: Genv.find_symbol se g_id = Some gb)
    (CACHE: sum_cache_memo mb sb m n sum m'):
  step (Callf i m) E0 (Returnf sum m')
| stepg i n m m' mb sb sum fb gb
    (ItoN: Int.repr (Z.of_nat n) = i)
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed)
    (FINDMEMO: Genv.find_symbol se _memoized = Some mb)
    (FINDS: Genv.find_symbol se _s = Some sb)
    (FINDF: Genv.find_symbol se f_id = Some fb)
    (FINDG: Genv.find_symbol se g_id = Some gb)    
    (CACHE: sum_cache_s mb sb m n sum m'):
  step (Callg i m) E0 (Returng sum m').

End WITH_SE.

(** The definition of the top specification  *)
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



(** ** Refinement: top_spec ⫹ (L_C ⊕ L_A) *)

Section MS.

Variable w: injp_world.
Variable se tse : Genv.symtbl.

Let tge1 := Clight.globalenv tse M_C.
Let tge2 := Genv.globalenv tse M_A.

Hypothesis MSTB : match_stbls injp w se tse.

(** The definition of the simulation relation  *)
Inductive match_state: state -> list (frame L) -> Prop :=
| match_callf i m tm j Hm n
    (INJP: injp_acc w (injpw j m tm Hm))
    (IEQ:  i = (Int.repr (Z.of_nat n)))
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed):
  match_state (Callf i m) (st L true (DemoCspec.Callstatef i tm) :: nil)
| match_callg i m tm j Hm n
    (INJP: injp_acc w (injpw j m tm Hm))
    (IEQ:  i = (Int.repr (Z.of_nat n)))
    (BOUND: Int.min_signed <= Z.of_nat n <= Int.max_signed):  
  match_state (Callg i m) (st L false (Demospec.Callstateg i tm) :: nil)
| match_returnf i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Returnf i m) (st L true (DemoCspec.Returnstatef i tm) :: nil)
| match_returng i m tm j Hm
  (INJP: injp_acc w (injpw j m tm Hm)):
  match_state (Returng i m) (st L false (Demospec.Returnstateg i tm) :: nil).

End MS.

Lemma int_modulus: Int.modulus = 4294967296.
Proof.
  reflexivity.
Qed.

Lemma int_half_modulus: Int.half_modulus = 2147483648.
Proof.
  reflexivity.
Qed.

Lemma intval_zero:
  Int.intval (Int.repr 0) = 0.
Proof.
  auto.
Qed.

Lemma intval_repr: forall z,
    Int.intval (Int.repr z) = Int.Z_mod_modulus z.
Proof.
  auto.
Qed.


Lemma intval_Sn_nz: forall n,
    (Z.of_nat (S n)) < Int.modulus ->
    Int.intval (Int.repr (Z.of_nat (S n))) <> 0.
Proof.
  intros.
  (* assert (Z.of_nat (S n) < Int.modulus). *)
  (* rewrite int_modulus. rewrite int_half_modulus in H. lia. *)
  rewrite intval_repr. rewrite Int.Z_mod_modulus_eq.
  rewrite Nat2Z.inj_succ. unfold Z.succ. 
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
    (Z.of_nat n) < Int.half_modulus ->
    Genv.find_symbol tse _memoized = Some mb ->
    Genv.find_symbol tse _s = Some sb ->
    Genv.find_symbol tse f_id = Some fb ->
    Genv.find_symbol tse g_id = Some gb ->
    (sum_cache_memo mb sb m n sum m' ->
     plus (fun _ : unit => SmallstepLinking.step L tse) tt
       (st L true (DemoCspec.Callstatef i m) :: k) E0 (st L true (DemoCspec.Returnstatef sum m') :: k)) /\
    (sum_cache_s mb sb m n sum m' ->
     plus (fun _ : unit => SmallstepLinking.step L tse) tt
       (st L false (Demospec.Callstateg i m) :: k) E0 (st L false (Demospec.Returnstateg sum m') :: k)).
Proof.
  induction n.
  - intros until k.
    intros IEQ LT FIND1 FIND2 FIND3 FIND4. split;intros SUMCACHE.
    + inv SUMCACHE.
      * eapply plus_left;eauto. econstructor.
        simpl. eapply DemoCspec.step_zero. eauto.
        eapply star_refl;eauto. auto.
      * simpl in INZ. rewrite intval_zero in INZ.
        congruence.
    + inv SUMCACHE.
      * eapply plus_left;eauto. econstructor.
        simpl. eapply Demospec.step_zero. eauto.
        eapply star_refl;eauto. auto.
      * simpl in INZ. rewrite intval_zero in INZ.
        congruence.
  - intros until k.
    intros IEQ LT FIND1 FIND2 FIND3 FIND4.
    split;intros SUMCACHE.
    + inv SUMCACHE.
      (* cache hits *)
      * eapply plus_left;eauto. econstructor.
        simpl. eapply DemoCspec.step_sum_nz. eapply INZ.
        eapply SUMNZERO.
        eauto. eauto.
        eapply star_refl;eauto. auto.
      (* cache miss *)
      * eapply plus_left;eauto. econstructor.
        eapply DemoCspec.step_call. 
        eapply intval_Sn_nz.
        rewrite Int.half_modulus_modulus.
        generalize Int.modulus_pos.
        lia.
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
        eapply plus_star.
        eapply plus_trans.
        exploit IHn;eauto. lia.
        intros (P1 & P2). eapply P2. eauto. 
        (* return from L_A *)
        eapply plus_left;eauto. eapply step_pop.
        simpl. econstructor. simpl. econstructor.
        (* one step from returnstateg to returnstatef *)
        eapply star_step;eauto. econstructor. econstructor.
        simpl. unfold Genv.symbol_address. rewrite FIND1.
        eauto. unfold Ptrofs.of_ints. rewrite Int.signed_repr.
        eauto.
        generalize (Int.min_signed_neg).
        split. lia.        
        unfold Int.max_signed. lia.
        eauto.
        eapply star_refl.
        all: eauto.
        rewrite Int.half_modulus_modulus. lia.
        
    + inv SUMCACHE.
      (* cache hits *)
      * eapply plus_left;eauto. econstructor.
        simpl. eapply Demospec.step_read. eapply INZ.
        eapply IEQI'.
        eauto. eauto. eauto.
        eapply star_refl;eauto. auto.
      (* cache miss *)
      * eapply plus_left;eauto. econstructor.
        eapply Demospec.step_call. 
        eapply intval_Sn_nz.
        rewrite Int.half_modulus_modulus.
        lia.
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
        eapply plus_star.
        eapply plus_trans.
        exploit IHn;eauto. lia.
        intros (P1 & P2). eapply P1. eauto. 
        (* return from L_A *)
        eapply plus_left;eauto. eapply step_pop.
        simpl. econstructor. simpl. econstructor.
        (* one step from returnstateg to returnstatef *)
        eapply star_step;eauto. econstructor. econstructor.
        simpl. unfold Genv.symbol_address. rewrite FIND2.
        eauto. eauto. eauto. 
        eapply star_refl.
        all: eauto.
        rewrite Int.half_modulus_modulus.
        lia.
Qed.

End FIND_FUNCT.


Lemma int_repr_eq: forall n1 n2,
    Int.min_signed <= Z.of_nat n1 <= Int.max_signed ->
    Int.min_signed <= Z.of_nat n2 <= Int.max_signed ->
    Int.repr (Z.of_nat n1) = Int.repr (Z.of_nat n2) ->
    n1 = n2.
Proof.
  intros.
  assert (Int.signed (Int.repr (Z.of_nat n1)) = Int.signed (Int.repr (Z.of_nat n2))).
  f_equal. auto.
  rewrite! Int.signed_repr in H2.    
  eapply Nat2Z.inj.  auto.
  lia. lia.
Qed.

(** top_spec ⫹_injp (L_C ⊕ L_A)  *)
Theorem top_simulation:
  forward_simulation (cc_c injp) (cc_c injp) top_spec composed_spec.
Proof.
   constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state w s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  destruct w as [f0 m0 tm0 Hm0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
   (* valid query *)
   - intros. inv H.
     unfold SmallstepLinking.valid_query.
     simpl. unfold valid_query. simpl.
     inv H0;simpl in *;auto;try congruence.
     destruct (Genv.invert_symbol se1 b1) eqn:INV.
     2: {
      unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
      rewrite !Genv.find_def_spec.
      assert (Genv.invert_symbol se2 b2 = None).
      destruct (Genv.invert_symbol se2 b2) as [i|] eqn:FIND2; eauto.
      apply Genv.invert_find_symbol in FIND2.
      inv H2.
      eapply mge_symb in FIND2 as FIND1; eauto.
      apply Genv.find_invert_symbol in FIND1. congruence.
      rewrite H0.
      destruct Ptrofs.eq_dec; destruct Ptrofs.eq_dec; eauto.
    }
    apply Genv.invert_find_symbol in INV as FIND.
    assert (delta = 0).
    { inv H2. exploit mge_dom. eapply Genv.genv_symb_range; eauto.
      intros [a b]. rewrite H in b. inv b. reflexivity.
    }
    subst delta.
     destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero).
    2: {
      unfold Genv.is_internal. unfold Genv.find_funct.
      rewrite !pred_dec_false. reflexivity.
      rewrite Ptrofs.add_zero. auto.
      rewrite Ptrofs.add_zero. auto.
    }
    unfold Genv.is_internal.
    rewrite !Ptrofs.add_zero. subst ofs1.
    destruct (peq i 154).
     + subst.
       eapply Genv.find_symbol_match in FIND. 2: eapply H2.
       destruct FIND as (tb1 & INJ & FINDT).
       rewrite INJ in H. inv H.
       exploit find_funf_inf. simpl. eapply FINDT.
       intros FINDFUNF. simpl in *. rewrite FINDFUNF.
       simpl. auto.
     + destruct (peq i 176).
       * eapply Genv.find_symbol_match in FIND. 2: eapply H2.
         destruct FIND as (tb1 & INJ & FINDT).
         rewrite INJ in H. inv H.
         exploit find_fung_ing. simpl. eapply FINDT.
         intros FINDFUNG. simpl in *. rewrite FINDFUNG.         
         eapply orb_true_intro. right. auto.
       * unfold Genv.find_funct.
         destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero);try congruence.
         unfold Genv.find_funct_ptr.
         assert (FIND_DEF_MC: forall f, Genv.find_def (Genv.globalenv se2 (Ctypes.program_of_program M_C)) b2 <> Some (Gfun f)).
         { unfold Genv.globalenv. simpl.
           intros.
           unfold Genv.add_globdef.
           (* destruct all the get *)
           simpl.
           (* se2 b2 = i *)
           assert (A: Maps.PTree.get i (Genv.genv_symb se2) = Some b2).
           erewrite <- Genv.mge_symb. 2: eapply H2.
           eauto. eauto.
           (* destruct and denote the names *)
            destruct Maps.PTree.get as [db1|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db2|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
              destruct Maps.PTree.get as [db3|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *.
             all :try assert (NEQ1: b2 <> db2) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
               try assert (NEQ2: b2 <> db3) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence).

             1-4: setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence.
             1-2,5-6: unfold NMap.get;erewrite NMap.gso;eauto.
             1,3,5,7: unfold NMap.get;erewrite NMap.gso;eauto.
             all: unfold NMap.get;rewrite NMap.gi;congruence. }

         assert (FIND_DEF_MA: forall f, Genv.find_def (Genv.globalenv se2 M_A) b2 <> Some (Gfun f)).
         { unfold Genv.globalenv. simpl.
           intros.
           unfold Genv.add_globdef.
           (* destruct all the get *)
           simpl.
           (* se2 b2 = i *)
           assert (A: Maps.PTree.get i (Genv.genv_symb se2) = Some b2).
           erewrite <- Genv.mge_symb. 2: eapply H2.
           eauto. eauto.
           (* destruct and denote the names *)
            destruct Maps.PTree.get as [db1|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db2|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
              destruct Maps.PTree.get as [db3|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *.
             all :try assert (NEQ1: b2 <> db1) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
               try assert (NEQ2: b2 <> db3) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence).

             1-4: unfold NMap.get;erewrite NMap.gso;eauto.            
             1-2,5-6: setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence.
             1,3,5,7: unfold NMap.get;erewrite NMap.gso;eauto.
             all: unfold NMap.get;rewrite NMap.gi;congruence. }

          assert (RHS: match i with
           | 154%positive | 176%positive => true
           | _ => false
                      end = false).
         { destruct i;try congruence;destruct i;try congruence;auto;
             destruct i;try congruence;auto;destruct i;try congruence;auto;
             destruct i;try congruence;destruct i;try congruence;
             destruct i;try congruence;destruct i;try congruence. }
         rewrite RHS.

         destruct Genv.find_def eqn:?. destruct g. specialize (FIND_DEF_MC f). contradiction.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_MA. specialize (FIND_DEF_MA f). contradiction.
         auto. auto.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_MA. specialize (FIND_DEF_MA f). contradiction.
         auto. auto.    
           
   (* initial state *)
   - intros.
     generalize Hse. intros Hse'.
     inv Hse.
     inv H. inv H0.
     + inv H5. inv H8. inv H10. inv H4. inv H6.
       simpl in *.
       (* find symbol *)
       eapply Genv.find_symbol_match in FINDF.
       2: eapply H1.
       destruct FINDF as (tb1 & INJ & FINDF). rewrite H5 in INJ.
       inv INJ. fold Ptrofs.zero.       
       (* find funct *)
       exploit find_funf_inf. simpl. eapply FINDF.
       intros FINDFUNF.     
       simpl in *. rewrite Ptrofs.add_zero_l.       
       eexists. split.
       econstructor. instantiate (1:= true).
       (* valid query *)
       simpl. unfold Genv.is_internal.
       simpl in *. rewrite FINDFUNF.
       auto.
       (* initial *)
       simpl. econstructor.
       simpl. rewrite FINDFUNF. auto.
       (* match state *)
       econstructor. reflexivity.
       eauto. auto.
     + inv H5. inv H8. inv H10. inv H4. inv H6.
       simpl in *.
       (* find symbol *)
       eapply Genv.find_symbol_match in FINDF.
       2: eapply H1.
       destruct FINDF as (tb1 & INJ & FINDF). rewrite H5 in INJ.
       inv INJ. fold Ptrofs.zero.       
       (* find funct *)
       exploit find_fung_ing. simpl. eapply FINDF.
       intros FINDFUNF.     
       simpl in *. rewrite Ptrofs.add_zero_l.       
       eexists. split.
       econstructor. instantiate (1:= false).
       (* valid query *)
       simpl. unfold Genv.is_internal.
       simpl in *. rewrite FINDFUNF.
       auto.
       (* initial *)
       simpl. econstructor.
       simpl. rewrite FINDFUNF. auto.
       (* match state *)
       econstructor. reflexivity.
       eauto. auto.

   (* final state *)
   - intros. inv H0;inv H.
     + eexists. split. econstructor.
       econstructor. econstructor.
       split. eauto. econstructor.
       simpl. econstructor.
       simpl. econstructor.
     + eexists. split. econstructor.
       econstructor. econstructor.
       split. eauto. econstructor.
       simpl. econstructor.
       simpl. econstructor.

   - simpl. intros. inv H0.
   (* step *)
   - simpl. intros.
     inv H;inv H0.
     + inv Hse.
       eapply int_repr_eq in IEQ;eauto. subst.
       exploit (match_stbls_acc injp); eauto.
       econstructor. eauto. eauto. eauto.
       intros Hse'. inv Hse'.
       
       (* find symbol match *)
       eapply (Genv.find_symbol_match H5) in FINDMEMO.
       destruct FINDMEMO as (tmb & FINDTMB & FINDMEMO).
       eapply (Genv.find_symbol_match H5) in FINDS.
       destruct FINDS as (tsb & FINDTSB & FINDS).
       eapply (Genv.find_symbol_match H5) in FINDF.
       destruct FINDF as (tfb & FINDTFB & FINDF).
       eapply (Genv.find_symbol_match H5) in FINDG.
       destruct FINDG as (tgb & FINDTGB & FINDG).
       
       exploit exec_mem. instantiate (1:= n0).
       eauto.
       unfold Int.max_signed in *. rewrite Int.half_modulus_modulus.
       generalize (Int.modulus_pos). lia.
       eapply FINDTMB. eapply FINDTSB.
       intros P. eapply P in CACHE. clear P.
       destruct CACHE as (tm' & Hm' & CACHE' & INJP1).
       
       exploit exec_state. instantiate (1:= n0).
       eauto. 
       unfold Int.max_signed in *. 
       generalize (Int.modulus_pos). lia.
       eauto. eauto. eauto. eauto.
       intros P.
       eapply P in CACHE'. clear P.

       eexists. split. eauto.
       econstructor. etransitivity. eauto.
       eauto.

     + inv Hse.
       eapply int_repr_eq in IEQ;eauto. subst.
       exploit (match_stbls_acc injp); eauto.
       econstructor. eauto. eauto. eauto.
       intros Hse'. inv Hse'.
       
       (* find symbol match *)
       eapply (Genv.find_symbol_match H5) in FINDMEMO.
       destruct FINDMEMO as (tmb & FINDTMB & FINDMEMO).
       eapply (Genv.find_symbol_match H5) in FINDS.
       destruct FINDS as (tsb & FINDTSB & FINDS).
       eapply (Genv.find_symbol_match H5) in FINDF.
       destruct FINDF as (tfb & FINDTFB & FINDF).
       eapply (Genv.find_symbol_match H5) in FINDG.
       destruct FINDG as (tgb & FINDTGB & FINDG).
       
       exploit exec_mem. instantiate (1:= n0).
       eauto.
       unfold Int.max_signed in *. rewrite Int.half_modulus_modulus.
       generalize (Int.modulus_pos). lia.
       eapply FINDTMB. eapply FINDTSB.
       intros P. eapply P in CACHE. clear P.
       destruct CACHE as (tm' & Hm' & CACHE' & INJP1).
       
       exploit exec_state. instantiate (1:= n0).
       eauto. 
       unfold Int.max_signed in *. 
       generalize (Int.modulus_pos). lia.
       eauto. eauto. eauto. eauto.
       intros P.
       eapply P in CACHE'. clear P.

       eexists. split. eauto.
       econstructor. etransitivity. eauto.
       eauto.
       
   - econstructor. intros. inv H.
Qed.


Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_callf : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callf i m)
| sound_callg : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callg i m)
| sound_returnf : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Returnf i m)
| sound_returng : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Returng i m).

End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma cache_ro_acc: forall n mb sb m1 i m2,
    (sum_cache_memo mb sb m1 n i m2 \/ sum_cache_s mb sb m1 n i m2) ->
    ro_acc m1 m2.
Proof.
  induction n;simpl;intros.
  - destruct H.
    + inv H. eapply ro_acc_refl. eapply ro_acc_refl.
    + inv H. eapply ro_acc_refl. eapply ro_acc_refl.
  - destruct H.
    + inv H.
      * eapply ro_acc_refl.
      * eapply ro_acc_trans.
        eapply IHn. right. eauto.
        eapply ro_acc_store;eauto.
    + inv H.
      * eapply ro_acc_refl.
      * eapply ro_acc_trans.
        eapply IHn. left. eauto.
        eapply ro_acc_trans.
        eapply ro_acc_store;eauto.
        eapply ro_acc_store;eauto.
Qed.

        
Lemma topspec_ro : preserves top_spec ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros.  inv H0;inv H.
    + assert (RO: ro_acc m m').
      eapply cache_ro_acc;eauto.
      econstructor.
      eapply ro_acc_trans. eapply H2.
      eauto.
      eapply ro_acc_sound;eauto.
    + assert (RO: ro_acc m m').
      eapply cache_ro_acc;eauto.
      econstructor.
      eapply ro_acc_trans. eapply H2.
      eauto.
      eapply ro_acc_sound;eauto.
  - intros.
    inv H;inv H0.
    + econstructor;eauto.
      eapply ro_acc_refl.
    + econstructor;eauto.
      eapply ro_acc_refl.
  - intros. inv H0;inv H.
  - intros. inv H0;inv H.
    + econstructor;eauto.
    + econstructor;eauto.
Qed.

(** top_spec ⫹_ro top_spec  *)
Theorem top_ro :
  forward_simulation ro ro top_spec top_spec.
Proof.
  eapply preserves_fsim. eapply topspec_ro; eauto.
Qed.

(** top_spec ⫹_wt top_spec  *)
Theorem topspec_self_simulation_wt :
  forward_simulation wt_c wt_c top_spec top_spec.
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
    inv H1. cbn. eauto.
  - intros. inv H. exists r1.
    constructor; eauto.
    constructor; eauto.
    cbn. inv H0. constructor; eauto.
    constructor; eauto.
  - intros. subst.
    exists (se2, int_int_sg).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + inv H0.
    + constructor; eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      inv H0. 
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

Require Import CallconvAlgebra InjectFootprint CKLRAlgebra CA CallConv.
Require Import Errors ClientServer Demoproof.

(** ** L_C ⊕ L_A ⫹ sem(Compile(M_C) + M_A) *)
Lemma compose_LC_LA_correct:
  forall tp M_C',
    transf_clight_program M_C = OK M_C' ->
    link M_C' M_A = Some tp ->
    forward_simulation cc_compcert cc_compcert composed_spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       eapply AsmLinking.asm_linking; eauto. }  
  eapply compose_simulation.
  (* L_C ⊑ M_C *)
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply cspec_self_simulation_wt.
  eapply compose_forward_simulations.
  eapply cspec_ro.  
  eapply compose_forward_simulations.
  eapply cspec_simulation.
  (* M_C ⊑ Compile(M_C) *)
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  (* L_A ⊑ M_A *)
  eapply M_A_semantics_preservation.
  eapply link_result.
  unfold compose. cbn.
  apply link_erase_program in H0. rewrite H0. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.


(** ** Final theorem : topspec ⫹ sem(Compile(M_C) + M_A) *)
Theorem topspec_correct:
  forall tp M_C',
    transf_clight_program M_C = OK M_C' ->
    link M_C' M_A = Some tp ->
    forward_simulation cc_compcert cc_compcert top_spec (Asm.semantics tp).
Proof.
  intros.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply topspec_self_simulation_wt.
  eapply compose_forward_simulations.
  eapply top_ro.
  eapply compose_forward_simulations.
  eapply top_simulation.
  eapply compose_LC_LA_correct;eauto.
Qed.  
