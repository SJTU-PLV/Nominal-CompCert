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
  | Kcall _ _ _ _ k' =>
      S (num_frames_cont k')
  | _ => O
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
    (RAN: (0 <= n <= 3)%nat)
    (* all execution is inside the current function *)
    (NUMF: num_frames s0 = num_frames s1),
    sound_state s1
| find_state_internal2: forall s0 s1 t n,
    return_find s0 ->
    starN step ge n s0 t s1 ->
    (0 <= n <= 3)%nat ->  
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
  change (check_own_env_consistency
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
  (* reflexivity. *)
  congruence.
  unfold collect_func in A. congruence.
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
        do 2 eexists.
        econstructor; eauto.
        

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


        
                
