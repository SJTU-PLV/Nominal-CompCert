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
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Callstate i m1) (Callstate i m2)
  |match_Interstate_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
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
    econstructor; eauto. reflexivity.
  - intros. inv H; inv H0.
    exists (cr (Vint i) m2). split; econstructor; eauto.
    split. eauto. constructor. simpl. eauto.
    constructor.
  - intros. inv H; inv H0. inversion Hse. subst. eapply Genv.find_symbol_match in H as H'; eauto.
    destruct H' as [tb [A B]]. inv H1.
    exists (injpw f m1 m2 Hm),(cq (Vptr tb Ptrofs.zero) int_int_sg (Vint (Int.sub i (Int.repr 1)) :: nil) m2).
    apply Mem.unchanged_on_support in H11 as SUP1.
    apply Mem.unchanged_on_support in H12 as SUP2.
    repeat apply conj; eauto.
    + constructor. eauto.
    + constructor. simpl.
    replace (Vptr tb Ptrofs.zero) with (Vptr tb (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))).
    econstructor; eauto. rewrite Ptrofs.add_zero. reflexivity.
    simpl. constructor. constructor. constructor. constructor. congruence.
    + constructor.
      eapply Genv.match_stbls_incr; eauto.
      intros. exploit H14; eauto. intros [C D].
      unfold Mem.valid_block in *. split; eauto.
      eauto. eauto.
    + intros r1 r2 s1' [w'[ Hw Hr]] F.
      destruct w'. inv F. inv Hr. cbn in *. inv H4.
      inv H6.
      exists (Returnstate (sum i) m2'). split.
      constructor. auto.
      econstructor; eauto.
      etransitivity; eauto. constructor; eauto.
  - intros. inv H0; inv H.
    + exists (Returnstate (sum i) m2). split.
      constructor. econstructor; eauto.
    + exists (Interstate i m2). split.
      constructor; auto. econstructor; eauto.
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
      inv A. inv B. inv H1. inv H2. constructor. auto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

End WT_C.

Variable BspecA : Smallstep.semantics li_asm li_asm.


Module CL.

Definition int_loc_arguments := loc_arguments int_int_sg.

Definition int_loc_argument := if Archi.ptr64 then (if Archi.win64 then (R CX) else (R DI))
                                          else S Outgoing 0 Tint.
(* result & *)

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

(*if Archi.ptr64
      then if Archi.win64 then One (R CX) :: nil else One (R DI) :: nil
      else One (S Outgoing 0 Tint) :: nil) *)

Definition loc_int_loc (i: int) (l : loc): Locmap.t :=
  fun loc => if Loc.eq loc l  then (Vint i) else Vundef.

(* Definition valid_loc (ls : Locmap.t) (i: int) : Prop :=
  ls (loc_int) = Vint i.
*)

Inductive state :=
  | Callstate (ls: Locmap.t) (m:mem)
  | Interstate (ls: Locmap.t) (m:mem)
  | Returnstate (ls: Locmap.t) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

(*
LTL_q1       m_ ---------------> m_  r1

args_remove  ms                  ms  unchanged_on
mach_q2      m  ---------------> m   r2

*)
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

(* no actual program context, donot need to check available internal function implementation*)
Definition valid_query (q : query li_locset): bool := true.

(*  match Genv.find_symbol se g_id with
    |Some b =>
       match (cq_vf q) with
         |Vptr b' Ptrofs => eq_block b b'
         |_ => false
       end
    |None => false
  end.*)

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
    exists int_int_sg, (lq (Vptr g_fptr Ptrofs.zero)
                      int_int_sg 
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

Compute CL.int_loc_argument.
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
(*    (RS': rs' int_argument_mreg = Vint (Int.sub i (Int.repr 1)))*)
(*    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr): *)
    at_external_mach (Interstate sp ra rs m)
                (mq (Vptr g_fptr Ptrofs.zero) sp ra rs' m).

Inductive after_external_mach : state -> reply li_mach -> state -> Prop :=
| after_external_mach_intro
    i m  sp ra rs rs' rs'' m'
    (RS: rs int_argument_mreg = Vint i)
    (RS' : rs' AX = Vint (sum (Int.sub i Int.one)))
    (RS'' : rs'' = Regmap.set AX (Vint (sum i)) rs'):
    (* here other values in rs' and rs'' are the same or not ??
       if we need they are the same to preserve match_states and further mr, shoule we 
       algo change the semantics of locset to let Locmap.t only change in R AX also? *)
    (forall r, is_callee_save r = true -> rs' r = rs r) ->
     (* similar, should it be rs'' r = rs'r = rs r?*)
    Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m m' ->
    after_external_mach (Interstate sp ra rs m) (mr rs' m') (Returnstate rs'' m').

Inductive step_mach : state -> trace -> state -> Prop :=
| step_sum_mach
    i m rs rs'' sp ra
    (RS: rs int_argument_mreg = Vint i)
    (RS'' : rs'' AX = Vint (sum i)):
    (* maybe need to identify rs'' here *)
    step_mach (Callstate sp ra rs m) E0 (Returnstate rs'' m)
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
(* cc_locset_mach_mr *)
Inductive match_states_locset_mach :  CL.state -> state -> Prop :=
  |LM_callstate ls ra m_
    (LS_RS : ls = make_locset rs0 m0 sp)
    (MEM: args_removed int_int_sg sp m0 m_)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
     match_states_locset_mach (CL.Callstate ls m_) (Callstate sp ra rs0 m0)
  |LM_interstate ls ra m_
    (LS_RS : ls = make_locset rs0 m0 sp)
    (MEM: args_removed int_int_sg sp m0 m_)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
      match_states_locset_mach (CL.Interstate ls m_) (Interstate sp ra rs0 m0)
  |LM_returnstate ls rs m_ m
     (LS_RS : rs AX  = ls (R AX))
     (RS: forall r : mreg, is_callee_save r = true -> rs r = rs0 r)
     (TMEM: Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m0 m) (*for mr*)
     (MEM: Mem.unchanged_on (not_init_args (size_arguments int_int_sg) sp) m_ m)
     (SUP: Mem.support m_ = Mem.support m)
     (PERM: forall (b : block) (ofs : Z) (k : perm_kind) (p : permission),
                               loc_init_args (size_arguments int_int_sg) sp b ofs -> ~ Mem.perm m_ b ofs k p):
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

Theorem locset_mach:
  forward_simulation (cc_locset_mach) (cc_locset_mach) CL.BspecL BspecM.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst. 
  pose (ms := fun s1 s2 => match_states_locset_mach (lmw_rs w) (lmw_sp w) (lmw_m w) s1 s2 /\ (lmw_sg w) = int_int_sg).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H. inv H0. exists (Callstate sp ra rs m). split.
    econstructor; eauto. eapply argument_int_value; eauto.
    red. simpl. split. econstructor; eauto. auto.
  - intros. inv H. inv H0. inv H1.
    exists (mr rs m0). split.
    econstructor; eauto. rewrite CL.ls_result_int in LS.
    rewrite LS_RS. eauto.
    destruct w. cbn in *. subst lmw_sg.
    econstructor; eauto.
    rewrite CL.loc_result_int. simpl. intros. inv H. auto. inv H0.
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
      -- constructor; eauto. constructor; eauto.
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
      econstructor; eauto.
      -- intros. rewrite Regmap.gso. eauto.
         destruct r; unfold is_callee_save in H; try congruence.
      -- eapply Mem.unchanged_on_refl.
      -- unfold int_int_sg in *. cbn in *. inv MEM.
         eauto with mem.
         constructor.
         ++ erewrite Mem.support_free; eauto.
         ++ intros.
            split.
            eapply Mem.perm_free_3; eauto.
            eapply Mem.perm_free_1; eauto.
            admit.
         ++ 
            admit.
      -- inv MEM. eauto. erewrite Mem.support_free; eauto.
      -- intros. inv MEM.
         clear -H0. inv H0. unfold int_int_sg, size_arguments in H1.
         unfold loc_arguments in H1. replace Archi.ptr64 with true in H1 by reflexivity.
         destruct Archi.win64. simpl in H1. admit.
         simpl in H1.
         admit. (*int_int_sg is not tailcall_possible*)
         Search Mem.free. inv H. rewrite <- H0 in H6. inv H6.
         eapply Mem.perm_free_2; eauto.
    + inv H1. exists (Interstate (lmw_sp w) ra (lmw_rs w) (lmw_m w)). split; econstructor; eauto.
      eapply argument_int_value; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Admitted.

End LM.

Section MA.

Theorem mach_asm :
  forward_simulation (cc_mach_asm) (cc_mach_asm) BspecM BspecA.
Admitted.
End MA.


Section Ainj.

Theorem asm_simulation_inj:
  forward_simulation (cc_asm inj) (cc_asm inj) BspecA (Asm.semantics DemoB.prog).
Admitted.

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
  eapply c_locset. eapply locset_mach. eapply mach_asm.
  eapply asm_simulation_inj.
Qed.

