Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LinkedList.
Require Import Values Globalenvs Memory.
Require Import InitDomain.
Require Import Events.
Require Import Smallstep Rustlightown SmallstepLinkingSafe.

Local Open Scope error_monad_scope.
Import ListNotations.

(* starN inside a function *)
Fixpoint num_frames_cont (k: cont) : nat :=
  match k with
  | Kstop => O
  | Kcall _ _ _ _ k' =>
      S (num_frames_cont k')
  | Kseq _ k
  | Kloop _ k
  | Kdropinsert _ _ k
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k
  | Klet _ _ k => num_frames_cont k
  end.

Definition num_frames (s: state) : nat :=
  match s with
  | State _ _ k _ _ _
  | Callstate _ _ k _
  | Returnstate _ k _
  | Dropinsert _ _ _ k _ _ _
  | Dropplace _ _ _ k _ _ _
  | Dropstate _ _ _ _ k _ => num_frames_cont k
  end.
              


Section CLOSURES.

Context {genv: Type}.
Context {state: Type}.

Variable step: genv -> state -> trace -> state -> Prop.
Variable numf: state -> nat.

Inductive starNf (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starNf_refl: forall s,
      starNf ge O s E0 s
  | starNf_step: forall n s t t1 s' t2 s''
      (STEP: step ge s t1 s')
      (STAR: starNf ge n s' t2 s'')
      (TRACE: t = t1 ** t2)
      (FEQ: numf s = numf s'),
      starNf ge (S n) s t s''.

Remark starNf_star:
  forall ge n s t s', starNf ge n s t s' -> star step ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark starNf_step_right ge: forall n s t t1 s' t2 s'',
    starNf ge n s t1 s' -> step ge s' t2 s'' -> t = t1 ** t2 ->
    numf s' = numf s'' ->
    starNf ge (S n) s t s''.
Admitted.

End CLOSURES.


Definition linked_list_sem := semantics linked_list_mod.

Section SOUNDNESS.

Context (se : Genv.symtbl).

Let ge := globalenv se linked_list_mod.

Hypothesis wf_senv: forall id,
    if in_dec ident_eq id (prog_defs_names linked_list_mod) then
      exists b, Genv.find_symbol se id = Some b
    else True.

Inductive sound_find_cont : cont -> Prop :=
| sound_find_Kstop:
    sound_find_cont Kstop
| sound_find_Kcall: forall k p f e own s,
    sound_find_cont k ->
      (* TODO: specify the statement *)
    sound_find_cont (Kcall p f e own (Kseq s k)).

Definition sound_cont (f: ident) : cont -> Prop :=
  if ident_eq f find then
    sound_find_cont
  else
    fun _ => False.

Definition length_of_args (f: ident) : nat :=
  if ident_eq f find then
    2
  else O.

Inductive call_func (f: ident) : state -> Prop :=
| call_func_intro: forall b vl k m
    (* ensured by valid_query *)
    (SYM: Genv.invert_symbol se b = Some f)
    (** TODO: some property of k *)
    (SCONT: sound_cont f k)
    (ARGS: length vl = length_of_args f),
    call_func f (Callstate (Vptr b Ptrofs.zero) vl k m).

(* continuation of the returnstate in find function *)
Inductive find_cont_ret : cont -> Prop :=
(* (* return the current find function *) *)
(* | find_return1: forall k, *)
(*     sound_find_cont k -> *)
(*     find_cont_ret k *)
(* return from find *)
| find_return1: forall k p f e own s,
    sound_find_cont k ->
    (* TODO: specify the statement *)
    find_cont_ret (Kcall p f e own (Kseq s k))
(* return from process *)
| find_return2: forall k p f e own s,
    sound_find_cont k ->
    (* TODO: specify the statement *)
    find_cont_ret (Kcall p f e own (Kseq s k))
.

(* returnstate in find function *)
Inductive return_find : state -> Prop :=
| return_find_intro: forall k v m,
    find_cont_ret k ->
    return_find (Returnstate v k m).



Inductive sound_state : state -> Prop :=
| find_state_internal1: forall s0 s1 t n
    (CALL: call_func find s0)
    (STAR: starNf step num_frames ge n s0 t s1)
    (RAN: (0 <= n <= 20)%nat),
    sound_state s1
| find_state_internal2: forall s0 s1 t n,
    return_find s0 ->
    starNf step num_frames ge n s0 t s1 ->
    (0 <= n <= 10)%nat ->
    sound_state s1
(* | find_state_call_process: forall , *)
(*     sound_state (Callstate v al  *)
| find_returnstate: forall v k m,
    sound_find_cont k ->
    sound_state (Returnstate v k m).

Lemma find_args_params_norepet:
  list_norepet
    (var_names (fn_params find_func) ++ var_names (fn_vars find_func)).
Proof.
  eapply proj_sumbool_true.
  instantiate (1 := list_norepet_dec ident_eq (var_names (fn_params find_func) ++ var_names (fn_vars find_func))).
  auto.
Qed.


Lemma init_own_env_find_progress:
  exists own, init_own_env (Smallstep.globalenv (linked_list_sem se)) find_func = OK own.        
  unfold init_own_env.
  destruct collect_func eqn: A. cbn [bind].
  set (empty_map := (PTree.map
                       (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                          InitDomain.Paths.empty) t)) in *.
  set (initParams:= (InitDomain.add_place_list t
                       (places_of_locals (fn_params find_func ++ fn_vars find_func))
                       empty_map)) in *.
  set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
  generalize (eq_refl flag).             
  generalize flag at 1 3.
  intros flag0 E. destruct flag0; try congruence.
  eexists; eauto.
  unfold flag in E. unfold initParams, empty_map in *.  
  unfold collect_func in A. 
  replace t with ((collect_stmt (Smallstep.globalenv (linked_list_sem se))
           (fn_body find_func)
           (fold_right
              (InitDomain.collect_place
                 (Smallstep.globalenv (linked_list_sem se)))
              (PTree.empty InitDomain.LPaths.t)
              (map
                 (fun elt : ident * type => Plocal (fst elt) (snd elt))
                 (fn_params find_func ++ fn_vars find_func))))) in *.
  vm_compute in E. congruence.
  congruence.
  unfold collect_func in A. congruence.
Qed.

        
Lemma function_entry_find_progress: forall vl m1,
    length_of_args find = length vl ->
  exists e m2, function_entry ge find_func vl m1 e m2.
Admitted.

(* Compute (variant_field_offset (proj1_sig build_ce_ok) Nil [Member_plain Nil Tunit; Member_plain Cons Node_ty]). *)


Definition val_is_ptr (v: val) : bool :=
  match v with
  | Vptr _ _ => true
  | _ => false
  end.


Definition val_is_int (v: val) : bool :=
  match v with
  | Vint _ => true
  | _ => false
  end.

Lemma sound_cont_no_vars: forall f k,
    sound_cont f k ->
    cont_vars k = nil.
Proof.
  intros. unfold sound_cont in H. destruct ident_eq in H; try contradiction.
  inv H; reflexivity.
Qed.

Lemma split_drop_place_find_retv: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get _retv w) (Plocal _retv List_box) List_box = OK [(Plocal _retv List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_l: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get l w) (Plocal l List_box) List_box = OK [(Pderef (Plocal l List_box) List_ty, true); (Plocal l List_box, false)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_node: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Plocal node Node_ty) Node_ty = OK [(Pfield (Plocal node Node_ty) key type_int32s, true);
    (Pfield (Plocal node Node_ty) LinkedList.val type_int32s, true);
    (Pfield (Plocal node Node_ty) next List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.


Lemma sound_call_cont_find: forall k,
    sound_cont find k ->
    (* Actually ck is the same as k *)
    exists ck, call_cont k = Some ck
          /\ sound_cont find ck.
Admitted.

Lemma call_cont_num_frames_eq: forall k1 k2,
    call_cont k1 = Some k2 ->
    num_frames_cont k1 = num_frames_cont k2.
Proof.
  induction k1; intros k2 CK; simpl in *; inv CK; auto.
Qed.

Lemma step_preservation_progress: forall s,
    sound_state s ->
    (not_stuck (linked_list_sem se) s \/ step_mem_error ge s)
    /\ (forall s' t, step ge s t s' ->
               sound_state s').
Proof.
  intros s INV. inv INV.
  - generalize CALL as CALL1.
    generalize STAR as STAR1. intros.
    (* build s0 *)
    inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal find_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    inv STAR.
    (* take zero step *)
    { split.
      - left. red. right. right.
        edestruct (function_entry_find_progress vl m) as (e & m1 & ENT); eauto.
        destruct init_own_env_find_progress as (own & INITOWN).
        do 2 eexists.
        econstructor; eauto.
      - intros. eapply find_state_internal1 with (n:= 1%nat); eauto.
        econstructor; eauto. econstructor. 
        inv H; simpl; auto. lia. }
    (** take one step *)
    inv STEP; try congruence.
    rewrite FIND in FIND0. inv FIND0.    
    unfold init_own_env in INITOWN.
    (* construct own_env *)
    destruct collect_func eqn: A; cbn [bind] in INITOWN; try congruence.
    set (empty_map := (PTree.map
                         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                            InitDomain.Paths.empty) t)) in *.
    set (initParams:= (InitDomain.add_place_list t
                         (places_of_locals (fn_params find_func ++ fn_vars find_func))
                       empty_map)) in *.
    set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
    generalize INITOWN. clear INITOWN.
    generalize (eq_refl flag).
    generalize flag at 1 3.
    intros flag0 E. destruct flag0; try congruence. intros. inv INITOWN.
    (* construct e *)
    inv ENTRY. inv ALLOC. inv H7. inv H9. inv H10. inv H11.
    inv STAR0.
    (* stop here: evaluate the if statement *)
    { split.
      - left. red.
        (** decide whether there would be memory error  *)
        destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
        + exploit Mem.valid_access_load. eapply v. intros (v1 & LOAD1).
          (* we should show thata v1 must be a pointer *)
          destruct (val_is_ptr v1) eqn: VPTR.
          * destruct v1; simpl in VPTR; try congruence.
            destruct (Mem.valid_access_dec m' Mint32 b4 (Ptrofs.unsigned i) Readable) eqn: VA2.
            -- exploit Mem.valid_access_load. eapply v0. intros (v2 & LOAD2).
               destruct (val_is_int v2) eqn: VINT.
               ++ destruct v2; simpl in VINT; try congruence.
                  right. right.
                  
                  do 2 eexists.
                  (* evaluate if then else *)
                  econstructor. econstructor. econstructor.
                  econstructor.
                  econstructor.
                  reflexivity. 
                  econstructor. reflexivity.
                  eauto. eauto. 1-3: reflexivity. 
                  (** TODO: range check. Make it a memory error state *)
                  simpl. unfold list_length_z. simpl.
                  admit.
                  reflexivity. 
                  simpl.
                  instantiate (1 := Int.eq i0 (Int.repr 0)).
                  destruct (Int.eq i0 (Int.repr 0)) eqn: EQZ; reflexivity.
               (* The tag is not an Int value *)
               ++ admit.
            (* The memory location of tag is not loadable *)
            -- admit.
          (* The value loaded from the place is not a pointer *)
          * admit.
        (* The block of l is not loadable *)
        + admit.
      (* Invariant preservation *)
      - intros. eapply find_state_internal1 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto.
        inv H; simpl; auto. lia. }
    (* destruct the if step *)
    inv STEP.
    2: { destruct H11; unfold find_body in *; try congruence. }
    (* get the bool value *)
    simpl in H15. inv H13. inv H0.
    simpl in PTY. unfold List_ty in PTY. inv PTY.
    vm_compute in CO. inv CO. vm_compute in FTAG. inv FTAG.
    simpl in RANGE. unfold list_length_z in RANGE. simpl in RANGE.
    destruct (Int.eq tag (Int.repr 0)) eqn: EQZ; vm_compute in H15; inv H15.
    (** evaluate the if branch *)
    { inv STAR; cbn [num_frames] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=3%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H11; congruence. }
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sassign to Dassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP. inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_reassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_reassign; auto.
          unfold init_place. cbn [own_universe].
          eapply split_drop_place_find_retv; eauto.
        - intros. eapply find_state_internal1 with (n:=5%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
      erewrite split_drop_place_find_retv in SPLIT; eauto. inv SPLIT.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold is_init, init_place. simpl.
          unfold collect_func in A. vm_compute in A. inv A. 
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=6%nat); eauto.
          eapply starNf_step_right; eauto.
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold is_init, init_place in OWN. simpl in OWN.
           unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { simpl in SCALAR. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=7%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: ealuate step_dropinsert_assign *)
      { split.
        - destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
          (* The argument l is loadable *)
          + exploit Mem.valid_access_load. eapply v. intros (?v & ?LOAD).
            * destruct (sem_cast v0 List_box List_box) eqn: CAST1.
              (* v0 can be casted *)
              -- destruct (Mem.valid_access_dec m' Mptr b2 0 Writable) eqn: VA2.
                 (* The return variable is writable *)
                 ++ edestruct Mem.valid_access_store with (v:= v1) as (?m & ?STORE).
                    eapply v2.
                    left. red. do 2 right.
                    do 2 eexists. econstructor.
                    econstructor; eauto.
                    simpl. unfold List_box. congruence.
                    econstructor. reflexivity.
                    econstructor. econstructor. econstructor.
                    reflexivity. econstructor. reflexivity.
                    eauto. econstructor. reflexivity. eauto.
                 (* The return variable is not writable *)
                 ++ right. econstructor.
                    eapply step_dropinsert_assign_error3.
                    econstructor. reflexivity.
                    econstructor. econstructor. econstructor.
                    reflexivity. econstructor. reflexivity.
                    eauto. eauto.
                    eapply assign_loc_value_mem_error. reflexivity.
                    eauto.
              (* v0 cannot be casted *)
              -- admit.
          (* The argument l is not loadable *)
          + right. econstructor.
            eapply step_dropinsert_assign_error1.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. eapply find_state_internal1 with (n:=8%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Kseq *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=9%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sreturn *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=10%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H11; congruence. }
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropinsert_return_before *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          erewrite sound_cont_no_vars; eauto.          
          eapply step_dropinsert_return_before.
        - intros. eapply find_state_internal1 with (n:=11%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP.
      erewrite sound_cont_no_vars in SDROP; eauto.
      inv SDROP. destruct NOTRETURN; congruence.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_return.
          reflexivity. reflexivity.
          eapply split_drop_place_find_l; eauto.
        - intros. eapply find_state_internal1 with (n:=12%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold List_box in OWNTY0. vm_compute in OWNTY0. congruence. }
      erewrite split_drop_place_find_l in SPLIT; eauto. inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=13%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN. inv STAR0.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=14%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=15%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_skip_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_skip_return.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=16%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      vm_compute in OWNTY1. congruence.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_return_after *)
      { split.
        - destruct (Mem.valid_access_dec m5 Mptr b2 0 Readable) eqn: ?VA.
          + exploit Mem.valid_access_load. eapply v0.
            intros (?v & ?LOAD).
            destruct (sem_cast v2 List_box List_box) eqn: ?CAST.
            * destruct (Mem.free_list m5 [(b3, 0, 16); (b1, 0, 8); (b2, 0, 8); (b0, 0, 4)]) eqn: ?FREELIST.
              -- left. red. do 2 right.
                 exploit sound_call_cont_find; eauto.
                 intros (ck & CK & SCK).
                 do 2 eexists. econstructor.
                 eapply step_dropinsert_return_after.
                 econstructor. econstructor. econstructor. reflexivity.
                 econstructor. reflexivity. eauto.
                 eauto. eauto. 
                 instantiate (1 := [(b3, 0, 16); (b1, 0, 8); (b2, 0, 8); (b0, 0, 4)]).
                 reflexivity. eauto.
              (* free_list memory error *)
              -- right. econstructor.
                 eapply step_dropinsert_return_error2; eauto.
            (* sem_cast fails *)
            * admit.
          + right. econstructor.
            eapply step_dropinsert_return_error1; eauto.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. inv H. inv SDROP.
          exploit sound_call_cont_find; eauto.
          intros (ck1 & CK & SCK). rewrite CONT in CK. inv CK.          
          eapply find_returnstate. eauto. }
      (* show that it cannot take more step using num_frames unchanged
      property *)
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (** show that the returnstate can take a step *)
      { exploit sound_call_cont_find; eauto.
        intros (ck1 & CK & SCK). rewrite CONT in CK. inv CK.
        vm_compute in SCK. inv SCK.
        (* ck1 is Kstop *)
        - split.
          (* final state *)
          + left. red. left.
            eexists. econstructor.
          + intros. inv H.
        (** TODO: ck1 is Kcall. Fill this code after finishing calling
        find *)
        - admit. }
      (* num frames contradiction *)
      inv STEP.
      simpl in FEQ16.
      exfalso. eapply Nat.neq_succ_diag_l; eauto. }
        
    (* evaluate the else branch *)
    { cbn [num_frames num_frames_cont] in *.
      (* show that the tag is one *)
      generalize (Int.unsigned_range tag). intros TAGPOS.
      destruct (zeq (Int.unsigned tag) 0). rewrite <- e in EQZ.
      rewrite Int.repr_unsigned in EQZ. rewrite Int.eq_true in EQZ. congruence.
      assert (EQONE: Int.unsigned tag = 1). lia.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Slet *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=3%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H11; congruence. }
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sassign to Dassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=5%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_reassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_reassign; auto.
          unfold init_place. cbn [own_universe].
          eapply split_drop_place_find_node; eauto.
        - intros. eapply find_state_internal1 with (n:=6%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
      erewrite split_drop_place_find_node in SPLIT; eauto. inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=7%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=8%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=9%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=10%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.      
      (* stop here: evaluate step_dropinsert_assign *)
      { split.
        (* Note that the evaluation of conditional expression provides
        the fact of loading *l *)        
        - destruct (Mem.range_perm_dec m' b5 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) ((Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) + 16) Cur Readable).
          + exploit Mem.range_perm_loadbytes. eapply r. intros (bys & LOADBYTES).
            destruct (Mem.range_perm_dec m' b3 0 (0 + 16) Cur Writable).
            * edestruct Mem.range_perm_storebytes with (bytes:= bys) as (?m & ?STOREBYTES).
              erewrite Mem.loadbytes_length; eauto. eauto.
              left. red. do 2 right.
              do 2 eexists. econstructor.
              econstructor; eauto.
              vm_compute. congruence.
              econstructor. reflexivity.
              econstructor. econstructor. econstructor.
              eauto. reflexivity. reflexivity. eauto.
              rewrite EQONE. reflexivity.
              instantiate (1 := 8). reflexivity.
              eapply deref_loc_copy. eauto.
              simpl. reflexivity.
              (* assign_loc_copy *)
              eapply do_assign_loc_sound.
              unfold do_assign_loc.
              replace (sizeof (Smallstep.globalenv (linked_list_sem se))
               (typeof_place (Plocal node Node_ty))) with 16 by reflexivity.
              rewrite LOADBYTES.
              rewrite Ptrofs.unsigned_zero. rewrite STOREBYTES.
              destruct check_assign_copy.
              -- reflexivity.
              (** TODO: we can treat check_assign_copy failure as a
              kind of memory error which can be ruled out in move
              checking. The approach is that we add a case of memory
              error in step_assign when the type of LHS is
              Tstruct/Tvariant. We also check the RHS must be (Eplace
              p') so that we can prove check_assign_copy success by
              case analysis of (RHS = p') or (RHS <> p'), using the
              fact that different place must have different location
              *)
              -- admit.
            * right. econstructor.
              eapply step_dropinsert_assign_error3.
              econstructor. reflexivity.
              econstructor. econstructor. econstructor.
              eauto. reflexivity. reflexivity. eauto.
              rewrite EQONE. reflexivity.
              instantiate (1 := 8). reflexivity.
              eapply deref_loc_copy. eauto.
              simpl. reflexivity.
              eapply assign_loc_copy_mem_error2; eauto.
          + right. econstructor.
            eapply step_dropinsert_assign_error3.
            econstructor. reflexivity.
            econstructor. econstructor. econstructor.
            eauto. reflexivity. reflexivity. eauto.
            rewrite EQONE. reflexivity.
            instantiate (1 := 8). reflexivity.
            eapply deref_loc_copy. eauto.
            simpl. reflexivity.
            eapply assign_loc_copy_mem_error1; eauto.
        - intros. eapply find_state_internal1 with (n:=11%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate skip_seq *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=12%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=13%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sifthenelse *)
      { split.
        - destruct (Mem.valid_access_dec m5 Mint32 b0 0 Readable).
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v2 type_int32s type_int32s) eqn: ?CAST.
            * destruct (Mem.valid_access_dec m5 Mint32 b3 0 Readable).
              -- exploit Mem.valid_access_load. eauto.
                 intros (?v & ?LOAD).
                 destruct (sem_cast v5 type_int32s type_int32s) eqn: ?CAST.
                 ++ exploit cast_val_is_casted. eapply CAST. intros ?CASTED.
                    exploit cast_val_is_casted. eapply CAST0. intros ?CASTED.
                    inv CASTED. inv CASTED0.
                    exploit sem_cast_id. eapply CAST. intros ?CCAST.
                    exploit sem_cast_id. eapply CAST0. intros ?CCAST.
                    left. red. do 2 right.
                    do 2 eexists. econstructor.
                    (* evaluate the binary equal *)
                    econstructor. econstructor.
                    econstructor. econstructor. reflexivity.
                    econstructor. reflexivity. eauto.
                    econstructor. econstructor. econstructor. reflexivity.
                    reflexivity. reflexivity.
                    reflexivity.
                    econstructor. reflexivity. eauto.
                    reflexivity. reflexivity.
                    simpl. unfold sem_cmp, sem_binarith. simpl.
                    erewrite CCAST. rewrite CCAST0.
                    reflexivity. reflexivity. simpl.
                    instantiate (1 := Int.eq n n1). 
                    destruct (Int.eq n n1) eqn: ?IEQ; reflexivity.
                 (* cast fails *)
                 ++ admit.
              (* load fails *)
              -- right.
                 eapply step_ifthenelse_error.
                 econstructor. econstructor.
                 right. eapply eval_Eplace_error2.
                 econstructor. econstructor. reflexivity. reflexivity.
                 econstructor. reflexivity.
                 econstructor. reflexivity. eauto.
            (* cast fails *)
            *  admit.
          (* load fails *)
          + right.
            eapply step_ifthenelse_error.
            econstructor. econstructor.
            left. eapply eval_Eplace_error2.
            econstructor. econstructor. 
            econstructor. reflexivity.
            eauto.
        - intros. eapply find_state_internal1 with (n:=14%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto. lia. }
      inv STEP.
      destruct b6.
      
      (* evaluate the true branch *)
      { inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Scall to Dcall *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
          - intros. eapply find_state_internal1 with (n:=15%nat); eauto.
            eapply starNf_step_right; eauto. 
            inv H; simpl; auto. lia. }
        inv STEP.
        inv STAR0; cbn [num_frames num_frames_cont] in *.
        (* evaluate step_dropinsert_skip_reassign *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
            eapply step_dropinsert_skip_reassign.
            reflexivity.
          - intros. eapply find_state_internal1 with (n:=16%nat); eauto.
            eapply starNf_step_right; eauto. 
            inv H; inv SDROP; simpl; auto. lia.}
        inv STEP. inv SDROP.
        vm_compute in OWNTY0. congruence. clear OWNTY0.
        inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Dcall *)
        { split.
          - destruct (Mem.valid_access_dec m5 Mint32 b3 4 Readable).
            + exploit Mem.valid_access_load. eauto.
              intros (?v & ?LOAD).
              destruct (sem_cast v3 type_int32s type_int32s) eqn: ?CAST.
              * left. red. do 2 right.
                (* construct the block of process *)
                generalize (wf_senv process). intros FINDPRO.
                simpl in FINDPRO. destruct FINDPRO as (?b & FINDPRO).
                do 2 eexists. econstructor. econstructor.
                reflexivity. reflexivity.
                econstructor. econstructor. eauto.
                eapply deref_loc_reference. reflexivity.
                (* evaluate the arguments *)
                econstructor.
                econstructor. econstructor. econstructor.
                econstructor. reflexivity. reflexivity.
                reflexivity. reflexivity. econstructor. reflexivity.
                eauto. eauto.
                econstructor.
                (* find_funct *)
                simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
                rewrite Genv.find_def_spec.
                erewrite Genv.find_invert_symbol; eauto.
                reflexivity. reflexivity.
                simpl. auto.
              (* sem_cast fails *)
              * admit.
            (* load fails *)
            + right.
              generalize (wf_senv process). intros FINDPRO.
              simpl in FINDPRO. destruct FINDPRO as (?b & FINDPRO).
              econstructor.
              eapply step_dropinsert_call_error2.   
              econstructor. econstructor. eauto.
              eapply deref_loc_reference. reflexivity.
              reflexivity. econstructor. econstructor.
              eapply eval_Eplace_error2. econstructor.
              econstructor. reflexivity. reflexivity. reflexivity.
              reflexivity. econstructor. reflexivity.
              eauto.
          - intros.
            eapply 

            (in_dec ident_eq process (prog_defs_names linked_list_mod)).
            
          simpl.
          eapply do_assign_loc
            econstructor. reflexivity.
          econstructor. reflexivity.
          eauto. reflexivity. reflexivity.
                 
          
      Cop.val_casted
      eval_Ebinop
      destruct (Int.eq_
        length
        
      
            simpl.
            Mem.load_cast val_casted
              val_casted
              Int.eq_
              reflexivity.
            repeat econstructor.
            Lemma starN_step_r: forall genv step
Admitted.

End SOUNDNESS.


        
                
