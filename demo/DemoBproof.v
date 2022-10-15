Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler.

Require Import CKLRAlgebra Inject InjectFootprint.

(** * Step1 : self_simulation of Bspec *)

Section SELF_INJP.

Section ms.
Variable w : world injp.

Inductive match_states' : state -> state -> Prop :=
|match_callstate_intro f m1 m2 Hm i:
     w = injpw f m1 m2 Hm ->
     match_states' (Callstate i m1) (Callstate i m2)
  |match_Interstate_intro f m1 m2 Hm i:
     w = injpw f m1 m2 Hm ->
     match_states' (Interstate i m1) (Interstate i m2)
  |match_Returnstate_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstate i m1) (Returnstate i m2).
End ms.

Theorem self_simulation_C :
  forward_simulation (cc_c injp) (cc_c injp) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => match_states' w s1 s2).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H0. inv H. inv H4. inv H6. inv H2. inv H4. cbn in *.
    inv Hse. inv H7.
    eapply Genv.find_symbol_match in H; eauto. destruct H as [tb [A B]].
    exists (Callstate i m2). split.
    econstructor; eauto. simpl in H1. rewrite H1 in A. inv A.
    rewrite Ptrofs.add_zero. reflexivity.
    econstructor; eauto.
  - intros. inv H; inv H0.
    exists (cr (Vint i) m2). split; econstructor; eauto.
    split. eauto. constructor. simpl. eauto.
    constructor.
  - intros. inv H; inv H0. inversion Hse. subst.
    eapply Genv.find_symbol_match in H2 as H'; eauto.
    destruct H' as [tb [A B]].
    exists (injpw f m1 m2 Hm) , (cq (Vptr tb Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m2).
    repeat apply conj; eauto.
    + constructor. eauto.
    + constructor. simpl.
    replace (Vptr tb Ptrofs.zero) with (Vptr tb (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))).
    econstructor; eauto. rewrite Ptrofs.add_zero. reflexivity.
    simpl. constructor. constructor. constructor. constructor. congruence.
    + intros r1 r2 s1' [w'[ Hw Hr]] F.
      destruct w' as [f' m1' m2' INJ0].
      destruct r1 as [t1 m1''].
      destruct r2 as [t2 m2''].
      inv Hr. cbn in *.
      inv F. inv H3. rename tm' into tm1'. rename tm'' into tm1''.
      cbn in *. inv Hw. inv H7.
      eapply Genv.match_stbls_incr in H2; eauto.
      2:{ intros. exploit H14; eauto. intros [E F].
      unfold Mem.valid_block in *. split; eauto. }
      eapply Genv.find_symbol_match in H2. 2: eapply FINDM.
      destruct H2 as [b' [C D]].
      edestruct Mem.store_mapped_inject as [tm2' [STORE0' INJ1]]; eauto.
      edestruct Mem.store_mapped_inject as [tm2'' [STORE1' INJ2]]; eauto.
      exists (Returnstate (Int.add ti i) tm2''). split.
      econstructor; eauto.
      econstructor; eauto.
      transitivity (injpw f' m1'' m2'' Hm9).
      constructor; eauto.
      instantiate (1:= INJ2).
      constructor; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- eapply Mem.unchanged_on_trans.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
      -- eapply Mem.unchanged_on_trans. 
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE0.
         destruct STORE0 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE1.
         destruct STORE1 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
      -- red. intros. congruence.
  - intros. inv H0; inv H.
    + (* zero *)
      exists (Returnstate (Int.zero) m2). split. constructor; eauto.
      econstructor; eauto. reflexivity.
    + (* read *)
      exists (Returnstate ti m2).
      inv Hse. eapply Genv.find_symbol_match in H2; eauto.
      destruct H2 as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD0. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      exploit Mem.loadv_inject; eauto.
      intros [v1 [LOAD1' VINJ1]]. inv VINJ1.
      split.
      econstructor; eauto.
      econstructor; eauto. reflexivity.
    + (* call *)
      exists (Interstate i m2).
      inv Hse. eapply Genv.find_symbol_match in H2; eauto.
      destruct H2 as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD0. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      split.
      econstructor; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End SELF_INJP.

Section WT_C.

Theorem self_simulation_wt :
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec Bspec.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [[se1' [se2' sg]] ?]. destruct Hse as [Hse Hse2].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd (snd (fst w)) = int_int_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. inv H. inv H1. cbn in *. inv H. inv H1. exists s1. exists s1.
    split. inv H2. inv H0. simpl. simpl in *.
    inv H. inv H2. inv H5.
    econstructor; eauto. split. reflexivity.
    inv H0. reflexivity.
  - intros. inv H. exists r1.
    split. auto. exists r1. inv H0.
    split; simpl; auto.
    econstructor; simpl. eauto.
    econstructor. constructor.
  - intros. subst.
    exists (se2 , (se2, int_int_sg), tt).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + exists q1. split; inv H0; simpl;  constructor; simpl; eauto.
    + constructor; eauto. simpl. constructor. eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      destruct H as [r3 [A B]].
      inv A. inv B. inv H1. inv H2. econstructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

End WT_C.

Module CL.

Definition int_loc_arguments := loc_arguments int_int_sg.

Definition int_loc_argument := if Archi.ptr64 then (if Archi.win64 then (R CX) else (R DI))
                                          else S Outgoing 0 Tint.
Lemma loc_result_int:
 loc_result int_int_sg = One AX.
Proof.
  intros. unfold int_int_sg, loc_result.
  replace Archi.ptr64 with true by reflexivity.
  reflexivity.
Qed.

Lemma ls_result_int:
  forall ls, Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls = ls (R AX).
Proof.
  intros. rewrite loc_result_int. reflexivity.
Qed.


Definition int_loc_result' : rpair mreg := loc_result int_int_sg.
(* Compute int_loc_result. One AX *)

Definition int_loc_result : loc := R AX.

Definition loc_int_loc (i: int) (l : loc): Locmap.t :=
  fun loc => if Loc.eq loc l  then (Vint i) else Vundef.

Inductive state :=
  | Callstate (ls: Locmap.t) (m:mem)
  | Interstate (ls: Locmap.t) (m:mem)
  | Returnstate (ls: Locmap.t) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

Inductive initial_state : query li_locset -> state -> Prop :=
| initial_state_intro
    v i m b (ls: Locmap.t)
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
    initial_state (lq v int_int_sg ls m) (Callstate ls m).

Inductive at_external: state -> query li_locset -> Prop :=
| at_external_intro
    g_fptr i m ls ls'
    (FINDG: Genv.find_symbol se f_id = Some g_fptr)
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS': ls' = Locmap.set int_loc_argument (Vint (Int.sub i Int.one)) ls):
    at_external (Interstate ls m)
                (lq (Vptr g_fptr Ptrofs.zero) int_int_sg ls' m).

Inductive after_external: state -> reply li_locset -> state -> Prop :=
| after_external_intro
    i m tm ls ls' ls''
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS' : Vint (sum (Int.sub i Int.one)) = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls')
    (LS'' : ls'' = Locmap.set (R AX) (Vint (sum i)) ls'):
    after_external (Interstate ls m) (lr ls' tm) (Returnstate ls'' tm).

Inductive step : state -> trace -> state -> Prop :=
| step_sum
    i m ls ls''
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS'' : Vint (sum i) = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls''):
    step (Callstate ls m) E0 (Returnstate ls'' m)
| step_call
    i m ls
    (NZERO: i.(Int.intval) <> 0%Z)
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
    step (Callstate ls m) E0 (Interstate ls m).

Inductive final_state: state -> reply li_locset  -> Prop :=
  | final_state_intro
      s m ls
      (LS : Vint s = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls):
      final_state (Returnstate ls m) (lr ls m).

Definition valid_query (q : query li_locset): bool := true.

Program Definition lts_BspecL : lts li_locset li_locset state :=
  {|
  Smallstep.step ge := step;
  Smallstep.valid_query := valid_query;
  Smallstep.initial_state := initial_state;
  Smallstep.at_external := at_external;
  Smallstep.after_external := after_external;
  Smallstep.final_state := final_state;
  globalenv := tt;
  |}.

End WITH_SE.

Program Definition BspecL : Smallstep.semantics li_locset li_locset :=
  {|
   Smallstep.skel := skel0;
   Smallstep.state := state;
   Smallstep.activate := lts_BspecL
   |}.

Inductive match_states_c_locset : DemoBspec.state -> state -> Prop :=
  |cl_callstate i ls m
     (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
     match_states_c_locset (DemoBspec.Callstate i m) (Callstate ls m)
  |cl_interstate i ls m
     (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
     match_states_c_locset (DemoBspec.Interstate i m) (Interstate ls m)
  |cl_returnstate i ls m
    (LS' : Vint i = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls):
     match_states_c_locset (DemoBspec.Returnstate i m) (Returnstate ls m).

Theorem c_locset :
  forward_simulation (cc_c_locset) (cc_c_locset) Bspec BspecL.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => (match_states_c_locset s1 s2 /\ w = int_int_sg)).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H0. inv H. exists (Callstate rs m).
    split.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  - intros. inv H. inv H0. inv H1.
    exists (lr ls m). split.
    econstructor; eauto.
    constructor. eauto.
  - intros. inversion H0. inv H. inv H0. inv H3.
    exists int_int_sg, (lq (Vptr g_fptr Ptrofs.zero) int_int_sg
                      (Locmap.set int_loc_argument (Vint (Int.sub i Int.one)) ls) m).
    repeat apply conj; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
      unfold loc_int_loc, int_int_sg, loc_arguments. simpl.
      unfold int_loc_argument. destruct Archi.ptr64.
      -- destruct Archi.win64; reflexivity.
      -- reflexivity.
    + intros. inv H0. inv H.
      exists (Returnstate (Locmap.set (R AX) (Vint (sum i)) rs') tm). split.
      econstructor; eauto. red. split.
      econstructor; eauto. auto.
  - intros. inv H; inv H0; inv H.
    + exists (Returnstate (loc_int_loc (sum i) int_loc_result) m). split; econstructor; eauto.
      constructor. unfold loc_int_loc, int_int_sg, loc_result. simpl.
      unfold int_loc_result. simpl. destruct Archi.ptr64; simpl; reflexivity.
    + exists (Interstate ls m). split; econstructor; eauto.
      constructor; eauto.
  - constructor. intros. inv H.
Qed.

End CL.

Module LM.

Inductive state :=
  |Callstate (sp ra: val) (rs: Mach.regset) (m:mem)
  |Interstate (sp ra: val) (rs: Mach.regset) (m: mem)
  |Returnstate (rs: Mach.regset) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

(* Compute CL.int_loc_argument. *)
Definition int_argument_mreg := if Archi.win64 then CX else DI.

Inductive initial_state_mach : query li_mach -> state -> Prop :=
| initial_state_mach_intro
    v m b i sp ra rs
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (RS : rs int_argument_mreg = Vint i)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
    initial_state_mach (mq v sp ra rs m) (Callstate sp ra rs m).

Inductive at_external_mach: state -> query li_mach -> Prop :=
| at_external_mach_intro
    g_fptr i m sp ra rs rs'
    (FINDG: Genv.find_symbol se f_id = Some g_fptr)
    (RS: rs int_argument_mreg = Vint i)
    (RS': rs' = Regmap.set int_argument_mreg (Vint (Int.sub i (Int.repr 1))) rs):
    at_external_mach (Interstate sp ra rs m)
                (mq (Vptr g_fptr Ptrofs.zero) sp ra rs' m).

Inductive after_external_mach : state -> reply li_mach -> state -> Prop :=
| after_external_mach_intro
    i m  sp ra rs rs' rs'' m'
    (RS: rs int_argument_mreg = Vint i)
    (RS' : rs' AX = Vint (sum (Int.sub i Int.one)))
    (RS'' : rs'' = Regmap.set AX (Vint (sum i)) rs'):
    (forall r, is_callee_save r = true -> rs' r = rs r) ->
    Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m m' ->
    after_external_mach (Interstate sp ra rs m) (mr rs' m') (Returnstate rs'' m').

Inductive step_mach : state -> trace -> state -> Prop :=
| step_sum_mach
    i m rs rs' sp ra
    (RS: rs int_argument_mreg = Vint i)
    (RS' : rs' = Regmap.set AX (Vint (sum i)) rs):
    step_mach (Callstate sp ra rs m) E0 (Returnstate rs' m)
| step_call_mach
    i m rs sp ra
    (NZERO: i.(Int.intval) <> 0%Z)
    (RS: rs int_argument_mreg = Vint i):
    step_mach (Callstate sp ra rs m) E0 (Interstate sp ra rs m).

Inductive final_state_mach: state -> reply li_mach  -> Prop :=
  | final_state_mach_intro
      s m rs
      (RS: rs AX = Vint s):
      final_state_mach (Returnstate rs m) (mr rs m).

(* no actual program context, donot need to check available internal function implementation*)
Definition valid_query_mach (q : query li_mach): bool := true.

Program Definition lts_BspecM : lts li_mach li_mach state :=
  {|
  Smallstep.step ge := step_mach;
  Smallstep.valid_query := valid_query_mach;
  Smallstep.initial_state := initial_state_mach;
  Smallstep.at_external := at_external_mach;
  Smallstep.after_external := after_external_mach;
  Smallstep.final_state := final_state_mach;
  globalenv := tt;
  |}.

End WITH_SE.

Program Definition BspecM : Smallstep.semantics li_mach li_mach :=
  {|
   Smallstep.skel := skel0;
   Smallstep.state := state;
   Smallstep.activate := lts_BspecM
   |}.

Definition make_regset_result (ls: Locmap.t) (sg: signature) (r: mreg) : val :=
  if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls (R r) else Vundef.

Section MS.
Variable rs0: Mach.regset.
Variable sp: val.
Variable m0: mem.

Inductive match_states_locset_mach :  CL.state -> state -> Prop :=
  |LM_callstate ls ra
    (LS_RS : ls = make_locset rs0 m0 sp)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
     match_states_locset_mach (CL.Callstate ls m0) (Callstate sp ra rs0 m0)
  |LM_interstate ls ra
    (LS_RS : ls = make_locset rs0 m0 sp)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
      match_states_locset_mach (CL.Interstate ls m0) (Interstate sp ra rs0 m0)
  |LM_returnstate ls rs m_ m
     (LS_RS : rs AX  = ls (R AX))
     (RS: forall r : mreg, is_callee_save r = true -> rs r = rs0 r)
     (MEM: Mem.unchanged_on (not_init_args (size_arguments int_int_sg) sp) m_ m)
     (SUP: Mem.support m_ = Mem.support m)
(*
     (PERM: forall (b : block) (ofs : Z) (k : perm_kind) (p : permission),
                               loc_init_args (size_arguments int_int_sg) sp b ofs -> ~ Mem.perm m_ b ofs k p)

 *)
     (TMEM: Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m0 m): (*for mr*)
     match_states_locset_mach (CL.Returnstate ls m_) (Returnstate rs m).

End MS.

Lemma argument_int_value:
  forall rs m sp i,
    Vint i :: nil =
    (fun p : rpair loc => Locmap.getpair p (make_locset rs m sp)) ## (loc_arguments int_int_sg) ->
    rs int_argument_mreg = Vint i.
Proof.
  intros.
  unfold make_locset in *.
  unfold int_int_sg, loc_arguments, int_argument_mreg in *.
  replace Archi.ptr64 with true in *. simpl in *. destruct Archi.win64. simpl in *.
  congruence. simpl in *. congruence. reflexivity.
Qed.

Lemma size_int_int_sg_0:
  size_arguments int_int_sg = 0.
Proof.
  unfold size_arguments, int_int_sg, loc_arguments. replace Archi.ptr64 with true by reflexivity.
  destruct Archi.win64; simpl;  reflexivity.
Qed.

Theorem locset_mach:
  forward_simulation (cc_locset_mach) (cc_locset_mach) CL.BspecL BspecM.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst. 
  pose (ms := fun s1 s2 => match_states_locset_mach (lmw_rs w) (lmw_sp w) (lmw_m w) s1 s2 /\ (lmw_sg w) = int_int_sg).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H. inv H0. inv H1.
    exists (Callstate sp ra rs m_). split.
    econstructor; eauto. eapply argument_int_value; eauto.
    red. simpl. split. econstructor; eauto. auto.
    rewrite size_int_int_sg_0 in H4. extlia.
  - intros. inv H. inv H0. inv H1.
    exists (mr rs m0). split.
    econstructor; eauto. rewrite CL.ls_result_int in LS.
    rewrite LS_RS. eauto.
    destruct w. cbn in *. subst lmw_sg.
    econstructor; eauto.
    rewrite CL.loc_result_int. simpl. intros. inv H. auto. inv H0.
    intros. inv H. rewrite size_int_int_sg_0 in H0. extlia.
  - intros. inv H0. inv H. inv H0. destruct w. cbn in *. subst lmw_sg.
    set (rs' := Regmap.set int_argument_mreg (Vint (Int.sub i (Int.repr 1))) lmw_rs).
    exists (lmw int_int_sg rs' lmw_m lmw_sp), (mq (Vptr g_fptr Ptrofs.zero) lmw_sp ra rs' lmw_m).
    repeat apply conj; eauto.
    + econstructor; eauto.
      eapply argument_int_value; eauto.
      eauto.
    + assert (Locmap.set CL.int_loc_argument (Vint (Int.sub i Int.one)) (make_locset lmw_rs lmw_m lmw_sp) = make_locset rs' lmw_m lmw_sp).
      {
        unfold rs'.
        unfold CL.int_loc_argument. unfold int_argument_mreg.
        replace Archi.ptr64 with true by reflexivity.
        apply Axioms.extensionality. intro l.
        destruct (Loc.eq l (if Archi.win64 then R CX else R DI)).
        - subst l. rewrite Locmap.gss.
          unfold make_locset. destruct Archi.win64.
          rewrite Regmap.gss. reflexivity.
          rewrite Regmap.gss. reflexivity.
        - rewrite Locmap.gso. unfold make_locset.
          destruct l. rewrite Regmap.gso. eauto.
          destruct Archi.win64; destruct r; try congruence.
          reflexivity.
          destruct l. destruct Archi.win64; destruct r; try congruence.
          destruct Archi.win64; simpl; eauto.
      }
      rewrite H. simpl.
      econstructor; eauto.
      constructor. red. apply size_int_int_sg_0.
    + intros. inv H0. inv H. cbn in *.
      set (rs'' := Regmap.set AX (Vint (sum i0)) rs'0).
      exists (Returnstate rs'' m' ). split.
      econstructor; eauto.
      -- eapply argument_int_value; eauto.
      -- rewrite CL.loc_result_int in H6.
         cbn in *. rewrite H6. eauto. eauto.
      -- unfold rs''. reflexivity.
      -- intros. rewrite H7; eauto. unfold rs'. rewrite Regmap.gso. reflexivity.
         unfold int_argument_mreg. unfold is_callee_save in H.
         replace Archi.ptr64 with true in H by reflexivity. cbn in *.
         destruct Archi.win64; destruct r; try congruence.
      -- constructor; eauto.
         econstructor; eauto.
         intros. unfold rs''. rewrite Regmap.gso.
         rewrite H7; eauto. unfold rs'. rewrite Regmap.gso. eauto.
         {
           unfold int_argument_mreg. unfold is_callee_save in H.
         replace Archi.ptr64 with true in H by reflexivity. cbn in *.
         destruct Archi.win64; destruct r; try congruence.
         }
         {
          unfold is_callee_save in H. destruct r; try congruence. 
         }
  - intros. inv H0. inv H. inv H1.
    + exists (Returnstate (Regmap.set AX (Vint (sum i)) (lmw_rs w)) (lmw_m w)). split.
      econstructor; eauto.
      eapply argument_int_value; eauto. eauto.
      econstructor; eauto.
      econstructor; eauto with mem.
      -- intros. rewrite Regmap.gso. eauto.
         destruct r; unfold is_callee_save in H; try congruence.
    + inv H1. exists (Interstate (lmw_sp w) ra (lmw_rs w) (lmw_m w)). split; econstructor; eauto.
      eapply argument_int_value; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End LM.

Module MA.

Inductive state :=
  |Callstate (rs: regset) (m:mem)
  |Interstate (rs: regset) (m: mem)
  |Returnstate (rs: regset) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

(* Compute CL.int_loc_argument. *)
Definition int_argument_preg := if Archi.win64 then IR RCX else IR RDI.

(* cc_mach_asm_mr *)

Inductive initial_state : query li_asm -> state -> Prop :=
| initial_state_intro
    v m b i rs
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
    (RANGE: 0 <= i.(Int.intval) < MAX)
    (RS : rs int_argument_preg = Vint i)
    (PC: rs PC <> Vundef)
    (RA: rs RA <> Vundef):
    initial_state (rs,m) (Callstate rs m).

Inductive at_external: state -> query li_asm -> Prop :=
| at_external_intro
    g_fptr i m rs rs'
    (FINDG: Genv.find_symbol se f_id = Some g_fptr)
    (RS: rs int_argument_preg = Vint i)
    (RS': rs' = (rs # int_argument_preg <- (Vint (Int.sub i (Int.repr 1)))) # PC <- (Vptr g_fptr Ptrofs.zero)):
    at_external (Interstate rs m)
                (rs',m).

Inductive after_external : state -> reply li_asm -> state -> Prop :=
| after_external_intro
    i m rs rs' rs'' m'
    (RS: rs int_argument_preg = Vint i)
    (RS' : rs' (IR RAX) = Vint (sum (Int.sub i Int.one)))
    (RS'' : rs'' = Pregmap.set (IR RAX) (Vint (sum i)) rs')
    (SUP : Mem.sup_include (Mem.support m) (Mem.support m')):
    after_external (Interstate rs m) (rs',m') (Returnstate rs'' m').

Inductive step : state -> trace -> state -> Prop :=
| step_sum
    i m rs rs'
    (RS: rs int_argument_preg = Vint i)
    (RS': rs' = (rs # (IR RAX) <- (Vint (sum i))) # PC <- (rs RA)):
    step (Callstate rs m) E0 (Returnstate rs' m)
| step_call
    i m rs
    (NZERO: i.(Int.intval) <> 0%Z)
    (RS: rs int_argument_preg = Vint i):
    step (Callstate rs m) E0 (Interstate rs m).

Inductive final_state: state -> reply li_asm  -> Prop :=
  | final_state_intro
      s m rs
      (RS: rs (IR RAX) = Vint s):
      final_state (Returnstate rs m) (rs, m).

(* no actual program context, donot need to check available internal function implementation*)
Definition valid_query (q : query li_asm): bool := true.

Program Definition lts_BspecA : lts li_asm li_asm state :=
  {|
  Smallstep.step ge := step;
  Smallstep.valid_query := valid_query;
  Smallstep.initial_state := initial_state;
  Smallstep.at_external := at_external;
  Smallstep.after_external := after_external;
  Smallstep.final_state := final_state;
  globalenv := tt;
  |}.

End WITH_SE.

Program Definition BspecA : Smallstep.semantics li_asm li_asm :=
  {|
   Smallstep.skel := skel0;
   Smallstep.state := state;
   Smallstep.activate := lts_BspecA
   |}.

Definition make_regset_result (ls: Locmap.t) (sg: signature) (r: mreg) : val :=
  if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls (R r) else Vundef.

Section MS.
Variable rs0: regset.
Variable s0: sup.

Inductive match_states_mach_asm :  LM.state -> state -> Prop :=
  |LM_callstate mrs m
    (MRS_RS : forall r, mrs r = rs0 (preg_of r))
    (SUP: s0 = Mem.support m):
     match_states_mach_asm (LM.Callstate (rs0 RSP) (rs0 RA) mrs m) (Callstate rs0 m)
  |LM_interstate mrs m
    (MRS_RS : forall r, mrs r = rs0 (preg_of r))
    (SUP: s0 = Mem.support m):
(*    (TSP: Val.has_type (rs RSP) Tptr)
    (TRA: Val.has_type (rs RA) Tptr): *)
      match_states_mach_asm (LM.Interstate (rs0 RSP) (rs0 RA) mrs m) (Interstate rs0 m)
  |LM_returnstate mrs rs m
     (MRS_RS : forall r, mrs r = rs (preg_of r))
     (RSP' : rs RSP = rs0 RSP)
     (PC': rs PC = rs0 RA)
     (SUP: Mem.sup_include s0 (Mem.support m)):
     match_states_mach_asm (LM.Returnstate mrs m) (Returnstate rs m).

End MS.

Lemma int_argument_preg_of:
  int_argument_preg = preg_of LM.int_argument_mreg.
Proof.
  unfold LM.int_argument_mreg, int_argument_preg, preg_of.
  destruct Archi.win64; reflexivity.
Qed.

Lemma int_result_preg_of:
  IR RAX = preg_of AX.
Proof.
  reflexivity.
Qed.

Theorem mach_asm:
  forward_simulation (cc_mach_asm) (cc_mach_asm) LM.BspecM BspecA.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_states_mach_asm (fst w) (snd w) s1 s2
                         /\ (fst w) PC <> Vundef /\ (fst w RA <> Vundef)
                         /\ valid_blockv (snd w) (fst w RSP)).
  eapply forward_simulation_step with (match_states := ms); cbn; destruct w; eauto.
  - intros. inv H. inv H0.
    exists (Callstate r m). split.
    econstructor; eauto. rewrite int_argument_preg_of.
    rewrite <- H4; eauto.
    red. econstructor; eauto.
    econstructor; eauto.
  - intros. inv H0. inv H. inv H0. cbn in *.
    exists (rs0 , m). split.
    econstructor; eauto.
    rewrite MRS_RS in RS. eauto.
    econstructor; eauto.
  - intros. inv H0. inv H. cbn in *. inv H0. destruct H1 as (A & B & C).
    set (s:= Mem.support m).
    set (r' := r # int_argument_preg <- (Vint (Int.sub i (Int.repr 1))) # PC <- (Vptr g_fptr Ptrofs.zero) ).
    exists (r',s), (r',m). repeat apply conj; eauto.
    + econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      unfold r'. reflexivity.
    + assert (VF': Vptr g_fptr Ptrofs.zero = r' PC).
      unfold r'. rewrite Pregmap.gss. eauto.
      assert (SP': r RSP = r' RSP).
      unfold r'. rewrite !Pregmap.gso. eauto.
      unfold int_argument_preg. destruct Archi.win64; congruence. congruence.
      assert (RA': r RA = r' RA).
      unfold r'. rewrite !Pregmap.gso. eauto.
      unfold int_argument_preg. destruct Archi.win64; congruence. congruence.
      rewrite VF',SP',RA'. unfold s.
      econstructor; eauto.
      unfold r'. rewrite Pregmap.gss. congruence.
      rewrite <- SP'. eauto.
      congruence.
      intros r0. destruct (mreg_eq r0 (LM.int_argument_mreg)).
      -- subst. rewrite Regmap.gss. unfold r'. rewrite int_argument_preg_of. rewrite Pregmap.gso.
         rewrite Pregmap.gss. eauto. unfold LM.int_argument_mreg. destruct Archi.win64; simpl; congruence.
      -- rewrite Regmap.gso; eauto. unfold r'.
         rewrite !Pregmap.gso. eauto. unfold LM.int_argument_mreg, int_argument_preg in *.
         destruct Archi.win64; destruct r0; simpl; congruence.
         destruct r0; simpl; congruence.
    + intros. inv H0. rewrite RS in RS0.  inv RS0. inv H. (* why 2 RS? *)
      set (rs'2 := rs'0 # RAX <- (Vint (sum i0))).
      exists (Returnstate rs'2 m').
      split. econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      rewrite H6 in RS'. eauto.
      unfold rs'2. reflexivity.
      constructor; eauto.
      constructor; eauto.
      -- unfold rs'2. intro mreg.
         destruct (mreg_eq mreg AX).
         subst. rewrite Regmap.gss. simpl.
         rewrite Pregmap.gss. eauto.
         rewrite Regmap.gso; eauto.
         rewrite Pregmap.gso; eauto.
         destruct mreg; simpl; try congruence.
      -- unfold rs'2. rewrite Pregmap.gso; try congruence.
         rewrite H2. unfold r'. rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gso. eauto.
         unfold int_argument_preg. destruct Archi.win64; congruence.
      -- unfold rs'2. rewrite Pregmap.gso; try congruence.
         rewrite H3. unfold r'. rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gso. eauto.
         unfold int_argument_preg. destruct Archi.win64; congruence.
  - intros. inv H; inv H0; inv H; destruct H1 as (A & B & C). cbn in *.
    + eexists. split.
      econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
      intros r0. destruct (mreg_eq r0 AX).
      -- subst. rewrite Regmap.gss. simpl. rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gss. reflexivity.
      -- rewrite Regmap.gso; try congruence.
         rewrite !Pregmap.gso; try congruence.
         destruct r0; simpl; congruence.
         destruct r0; simpl; congruence.
      -- subst s. eauto with mem.
    + cbn in *. exists (Interstate r m). split.
      econstructor; eauto. rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End MA.

Section Ainj.

Section WITH_SE.
Variable w: inj_world.

(*Inductive match_states : MA.state -> State -> Prop :=
  | match_states_callstate rs mem
      match_states (MA.Callstate) (State rs mem )



*)
End WITH_SE.

Require Import Extends.

Theorem asm_simulation_ext:
  forward_simulation (cc_asm ext) (cc_asm ext) MA.BspecA (Asm.semantics DemoB.prog).
Proof.
Admitted.


Theorem asm_simulation_inj:
  forward_simulation (cc_asm inj) (cc_asm inj) MA.BspecA (Asm.semantics DemoB.prog).
Proof.
  intros.
  assert (H : ccref (cc_asm ext @ cc_asm inj) (cc_asm inj)).
  rewrite <- cc_asm_compose. rewrite ext_inj. reflexivity.
  rewrite <- H at 1.
  rewrite <- ext_inj at 2. rewrite cc_asm_compose.
  eapply compose_forward_simulations.
  eapply asm_simulation_ext.
  eapply semantics_asm_rel.
Qed.

End Ainj.

Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply self_simulation_C.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  repeat eapply compose_forward_simulations.
  eapply CL.c_locset. eapply LM.locset_mach. eapply MA.mach_asm.
  eapply asm_simulation_inj.
Qed.

