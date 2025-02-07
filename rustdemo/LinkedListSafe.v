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
Require Import Smallstep Rustlightown SmallstepLinkingSafe.


Local Open Scope error_monad_scope.
Import ListNotations.

Definition linked_list_sem := semantics linked_list_mod.

Section SOUNDNESS.

Context (se : Genv.symtbl).

Let ge := globalenv se linked_list_mod.

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
              

Inductive sound_state : state -> Prop :=
| find_state_internal1: forall s0 s1 t n
    (CALL: call_func find s0)
    (STAR: starN step ge n s0 t s1)
    (RAN: (0 <= n <= 20)%nat)
    (* all execution is inside the current function *)
    (NUMF: num_frames s0 = num_frames s1),
    sound_state s1
| find_state_internal2: forall s0 s1 t n,
    return_find s0 ->
    starN step ge n s0 t s1 ->
    (0 <= n <= 10)%nat ->  
    num_frames s0 = num_frames s1 ->
    sound_state s1
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
  replace (check_own_env_consistency
        (PTree.map
           (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
            InitDomain.Paths.empty)
           (collect_stmt (Smallstep.globalenv (linked_list_sem se))
              (fn_body find_func)
              (fold_right
                 (InitDomain.collect_place
                    (Smallstep.globalenv (linked_list_sem se)))
                 (PTree.empty InitDomain.LPaths.t)
                 (map
                    (fun elt : ident * type =>
                     Plocal (fst elt) (snd elt))
                    (fn_params find_func ++ fn_vars find_func)))))
        (PTree.map
           (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
            InitDomain.Paths.empty)
           (collect_stmt (Smallstep.globalenv (linked_list_sem se))
              (fn_body find_func)
              (fold_right
                 (InitDomain.collect_place
                    (Smallstep.globalenv (linked_list_sem se)))
                 (PTree.empty InitDomain.LPaths.t)
                 (map
                    (fun elt : ident * type =>
                     Plocal (fst elt) (snd elt))
                    (fn_params find_func ++ fn_vars find_func)))))
        (InitDomain.add_place_list
           (collect_stmt (Smallstep.globalenv (linked_list_sem se))
              (fn_body find_func)
              (fold_right
                 (InitDomain.collect_place
                    (Smallstep.globalenv (linked_list_sem se)))
                 (PTree.empty InitDomain.LPaths.t)
                 (map
                    (fun elt : ident * type =>
                     Plocal (fst elt) (snd elt))
                    (fn_params find_func ++ fn_vars find_func))))
           (places_of_locals (fn_params find_func ++ fn_vars find_func))
           (PTree.map
              (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
               InitDomain.Paths.empty)
              (collect_stmt (Smallstep.globalenv (linked_list_sem se))
                 (fn_body find_func)
                 (fold_right
                    (InitDomain.collect_place
                       (Smallstep.globalenv (linked_list_sem se)))
                    (PTree.empty InitDomain.LPaths.t)
                    (map
                       (fun elt : ident * type =>
                        Plocal (fst elt) (snd elt))
                       (fn_params find_func ++ fn_vars find_func))))))
        (collect_stmt (Smallstep.globalenv (linked_list_sem se))
           (fn_body find_func)
           (fold_right
              (InitDomain.collect_place
                 (Smallstep.globalenv (linked_list_sem se)))
              (PTree.empty InitDomain.LPaths.t)
              (map
                 (fun elt : ident * type => Plocal (fst elt) (snd elt))
                 (fn_params find_func ++ fn_vars find_func))))) with true in *. congruence.
  reflexivity.
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
        econstructor; eauto. econstructor. lia.
        inv H; simpl; auto. }
    (** take one step *)
    inv H; try congruence.
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
    inv ENTRY. inv ALLOC. inv H8. inv H10. inv H11. inv H12. inv H13.
    inv H14. inv H15. inv H16. inv H17.
    inv H0.
    (* stop here: evaluate the if statement *)
    { split.
      - left. red.
        (** decide whether there would be memory error  *)
        destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
        + exploit Mem.valid_access_load. eapply v. intros (v1 & LOAD1).
          (* we should show thata v1 must be a pointer *)
          destruct (val_is_ptr v1) eqn: VPTR.
          * destruct v1; simpl in VPTR; try congruence.
            destruct (Mem.valid_access_dec m' Mint32 b9 (Ptrofs.unsigned i) Readable) eqn: VA2.
            -- exploit Mem.valid_access_load. eapply v0. intros (v2 & LOAD2).
               destruct (val_is_int v2) eqn: VINT.
               ++ destruct v2; simpl in VINT; try congruence.
                  right. right.
                  
                  do 2 eexists.
                  (* evaluate if then else *)
                  econstructor. econstructor. econstructor. econstructor.
                  econstructor.
                  do 8 (try rewrite PTree.gso; try (cbv delta; congruence)).
                  rewrite PTree.gss. reflexivity.
                  econstructor. simpl. eauto.
                  eauto. eauto. simpl. unfold List_ty. eauto.
                  simpl. reflexivity. reflexivity.
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
        eapply starN_step_right; eauto. lia.
        inv H; simpl; auto. }
    (* destruct the if step *)
    inv H.
    2: { destruct H18; unfold find_body in *; try congruence. }
    (* get the bool value *)
    simpl in H22. inv H20. inv H0.
    simpl in H5. unfold List_ty in H5. inv H5. simpl in H6.
    rewrite PTree.gss in H6. inv H6. simpl in H17.
    vm_compute in H17. inv H17.
    destruct (Int.eq tag (Int.repr 0)) eqn: EQZ; vm_compute in H22; inv H22.
    (** evaluate the if branch *)
    { inv H1.
      (* stop here: evaluate Slet *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=3%nat); eauto.
          eapply starN_step_right; eauto. lia.
          inv H; simpl; auto. }
      inv H.
      2: { destruct H20; try congruence. }
      inv H0.
      (* stop here: evaluate ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=4%nat); eauto.
          eapply starN_step_right; eauto. lia.
          inv H; simpl; auto. }
      inv H. inv H1.
      (* stop here: evaluate to Dassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=5%nat); eauto.
          eapply starN_step_right; eauto. lia.
          inv H; simpl; auto. }
      inv H. inv H0.
      (* stop here: evaluate step_dropinsert_skip_reassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_skip_reassign; auto.
        - intros. eapply find_state_internal1 with (n:=6%nat); eauto.
          eapply starN_step_right; eauto. lia.
          inv H; inv SDROP; simpl; auto. }
      inv H. inv SDROP; vm_compute in OWNTY; try congruence.
      inv H1.
      (* stop here: ealuate step_dropinsert_assign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_assign; auto.
          simpl. congruence.
          econstructor. reflexivity.
          (* evaluate *l *)
          econstructor. econstructor. econstructor.
          eauto. reflexivity. reflexivity. eauto.
          replace tag with (Int.repr 0). reflexivity.
          generalize (Int.eq_spec tag (Int.repr 0)). rewrite EQZ. auto.
          simpl. instantiate (1 := 8). reflexivity.
          econstructor. simpl. eauto.
          Mem.load_cast
          Int.eq_
          reflexivity.
          repeat econstructor. 
        Lemma starN_step_r: forall genv step 
        
        econstructor.
        Mem.valid_access_load
    
        Lemma init_own_env_find_progress:
          exists own, init_own_env (Smallstep.globalenv (linked_list_sem se)) find_func =
 OK own.
        
        2: { unfold init_own_env.
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
             
             generalize (check_own_env_consistency
       (PTree.map
          (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
           InitDomain.Paths.empty) t)
       (PTree.map
          (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
           InitDomain.Paths.empty) t)
       (InitDomain.add_place_list t
          (places_of_locals (fn_params find_func ++ fn_vars find_func))
          (PTree.map
             (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
              InitDomain.Paths.empty) t))) at 1,3 .

             
             replace (check_own_env_consistency
      (PTree.map
         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
          InitDomain.Paths.empty)
         (collect_func (Smallstep.globalenv (linked_list_sem se))
            find_func))
      (PTree.map
         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
          InitDomain.Paths.empty)
         (collect_func (Smallstep.globalenv (linked_list_sem se))
            find_func))
      (InitDomain.add_place_list
         (collect_func (Smallstep.globalenv (linked_list_sem se))
            find_func)
         (places_of_locals (fn_params find_func ++ fn_vars find_func))
         (PTree.map
            (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
             InitDomain.Paths.empty)
            (collect_func (Smallstep.globalenv (linked_list_sem se))
               find_func)))
      (collect_func (Smallstep.globalenv (linked_list_sem se))
         find_func)) with true.


native_compute (check_own_env_consistency
      (PTree.map
         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
          InitDomain.Paths.empty)
         (collect_func (proj1_sig build_ce_ok) find_func))
      (PTree.map
         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
          InitDomain.Paths.empty)
         (collect_func (proj1_sig build_ce_ok) find_func))
      (InitDomain.add_place_list
         (collect_func (proj1_sig build_ce_ok) find_func)
         (places_of_locals (fn_params find_func ++ fn_vars find_func))
         (PTree.map
            (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
             InitDomain.Paths.empty)
            (collect_func (proj1_sig build_ce_ok) find_func)))
      (collect_func (proj1_sig build_ce_ok) find_func) = true).
{ simpl


    
  rewrite H.
             
               
        econstructor.
        eapply find_args_params_norepet.
        eapply do_alloc_variables_sound. simpl.
        do 9 destruct Mem.alloc eqn: ?ALLOC at 1. f_equal.

        Lemma find_step_internal_progress


        
                
