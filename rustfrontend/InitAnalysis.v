Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustIR RustIRown.
Require Import InitDomain.


Local Open Scope list_scope.

Definition moved_place (e: expr) : option place :=
  match e with
  | Emoveplace p _ => Some (valid_owner p)
  | _ => None
  end.

Fixpoint moved_place_list (al: list expr) : list place :=
  match al with
  | e :: l =>
      match moved_place e with
      | Some p => p :: moved_place_list l
      | None => moved_place_list l
      end
  | nil => nil
  end.

(* S is the whole set, flag = true indicates that it computes the MaybeInit set *)
Definition transfer (S: PathsMap.t) (flag: bool) (f: function) (cfg: rustcfg) (pc: node) (before: PathsMap.t) : PathsMap.t :=
  (* This condition complicates the proof. Maybe we can prove that
  transfer bot = bot *)
  (* if PathsMap.beq before PathsMap.bot then PathsMap.bot *)
  (* else *)
    match cfg ! pc with
    | None => PathsMap.bot
    | Some (Inop _) => before
    | Some (Icond _ _ _) => before
    | Some Iend => before
    | Some (Isel sel _) =>
        match select_stmt f.(fn_body) sel with
        | None => PathsMap.bot
        | Some s =>
        match s with
        | Sassign p e
        | Sassign_variant p _ _ e
        | Sbox p e =>
            let p' := moved_place e in
            if flag then
              add_place S p (remove_option p' before)
            else
              remove_place p (add_option S p' before)
        | Scall p _ al =>
            let pl := moved_place_list al in
            if flag then
              add_place S p (fold_right remove_place before pl)
            else
              remove_place p (fold_right (add_place S) before pl)
        | Sreturn (Some e) =>
            let p' := moved_place e in
            if flag then
              remove_option p' before
            else
              add_option S p' before
        | Sdrop p =>
            if flag then
              remove_place p before
            else
              add_place S p before
        | _ => before
        end
        end
    end.

Module DS := Dataflow_Solver(PathsMap)(NodeSetForward).

Local Open Scope error_monad_scope.

(* The analyze returns the MaybeInit and MaybeUninit sets along with
the universe set *)
Definition analyze (ce: composite_env) (f: function) : Errors.res (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let maybeInit := fold_right (add_place whole) empty_pathmap pl in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := fold_right (add_place whole) empty_pathmap vl in
  (* generate selector-based CFG for analysis *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry maybeInit in
  let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry maybeUninit in
  match initMap, uninitMap with
  (* we only want the PTree because [None] represent the unreachable node *)
  | Some initMap, Some uninitMap => Errors.OK (initMap, uninitMap, whole)
  | _, _ => Errors.Error (msg "Error in initialize analysis")
  end.
  
(** Definitions of must_owned and may_owned used in Drop elaboration *)

Definition must_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mustinit := Paths.diff init uninit in
  (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mustinit *)
  Paths.for_all (fun p' => Paths.mem p' mustinit)
    (Paths.filter (fun p' => is_prefix p' p) universe).

(* place that needs drop flag *)
Definition may_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mayinit := Paths.inter init uninit in
  (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mayinit *)
  Paths.for_all (fun p' => Paths.mem p' mayinit)
    (Paths.filter (fun p' => is_prefix p' p) universe).

(* Used in static move checking *)
Definition must_movable (initmap uninitmap universemap: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let universe := PathsMap.get id universemap in
  let mustinit := Paths.diff init uninit in
  (* ∀ p' ∈ universe, is_prefix p p' → must_owned p' *)
  Paths.for_all (must_owned initmap uninitmap universemap)
    (Paths.filter (is_prefix p) universe).

(* move it to a new file *)
(** * Relations between the generated CFG and the source statement *)

(* Translation relation of the generate_cfg: [tr_stmt body cfg stmt pc
  out cont break endn] holds if the graph [cfg], starting at node
  [pc], contains instructions that perform the RustIR statement
  [stmt]. These instructions branch to node [out] if the statement
  terminates normally, branch to node [cont] if the statement reaches
  Scontinue, branch to break if the statement reaches Sbreak and
  branch to [endn] if the statement returns *)
Inductive tr_stmt (body: statement) (cfg: rustcfg) : statement -> node -> node -> option node -> option node -> node -> Prop :=
| tr_Sskip: forall pc cont brk endn,
    tr_stmt body cfg Sskip pc pc cont brk endn
| tr_Sassign: forall pc next sel p e cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign p e)),
    tr_stmt body cfg (Sassign p e) pc next cont brk endn
| tr_Sassign_variant: forall pc next sel p e enum_id fid cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign_variant p enum_id fid e)),
    tr_stmt body cfg (Sassign_variant p enum_id fid e) pc next cont brk endn
| tr_Sbox: forall pc next sel p e cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sbox p e)),
    tr_stmt body cfg (Sbox p e) pc next cont brk endn
| tr_Sstoragelive: forall pc next sel id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragelive id)),
    tr_stmt body cfg (Sstoragelive id) pc next cont brk endn
| tr_Sstoragedead: forall pc next sel id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragedead id)),
    tr_stmt body cfg (Sstoragedead id) pc next cont brk endn
| tr_Sdrop: forall pc next sel p cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sdrop p)),
    tr_stmt body cfg (Sdrop p) pc next cont brk endn
| tr_Scall: forall pc next sel p e args cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Scall p e args)),
    tr_stmt body cfg (Scall p e args) pc next cont brk endn
| tr_Ssequence: forall s1 s2 n1 n2 n3 cont brk endn
    (STMT1: tr_stmt body cfg s1 n1 n2 cont brk endn)
    (STMT2: tr_stmt body cfg s2 n2 n3 cont brk endn),
    tr_stmt body cfg (Ssequence s1 s2) n1 n3 cont brk endn
| tr_Sifthenelse: forall s1 s2 e pc n1 n2 endif cont brk endn
    (STMT1: tr_stmt body cfg s1 n1 endif cont brk endn)
    (STMT2: tr_stmt body cfg s2 n2 endif cont brk endn)
    (SEL: cfg ! pc = Some (Icond e n1 n2)),
    tr_stmt body cfg (Sifthenelse e s1 s2) pc endif cont brk endn
| tr_Sloop: forall s next loop_start loop_jump_node cont brk endn
    (STMT: tr_stmt body cfg s loop_start loop_jump_node (Some loop_jump_node) (Some next) endn)
    (SEL: cfg ! loop_jump_node = Some (Inop loop_start)),
    (* next is not specific because loop is impossible to terminate
    normally *)
    tr_stmt body cfg (Sloop s) loop_jump_node next brk cont endn
| tr_Sbreak: forall pc brk cont endn
    (SEL: cfg ! pc = Some (Inop brk)),
    tr_stmt body cfg Sbreak pc brk cont (Some brk) endn
| tr_Scontinue: forall pc brk cont endn
    (SEL: cfg ! pc = Some (Inop cont)),
    tr_stmt body cfg Scontinue pc cont (Some cont) brk endn
| tr_Sreturn: forall pc sel endn e cont brk
    (SEL: cfg ! pc = Some (Isel sel endn))
    (STMT: select_stmt body sel = Some (Sreturn e)),
    tr_stmt body cfg (Sreturn e) pc endn cont brk endn
.


(** * Soundness of Initial Analysis *)

Inductive tr_fun (f: function) (nret: node) : rustcfg -> Prop :=
| tr_fun_intro: forall entry cfg
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (STMT: tr_stmt f.(fn_body) cfg f.(fn_body) entry nret None None nret),
    tr_fun f nret cfg.

Inductive tr_cont : statement -> rustcfg -> cont -> node -> option node -> option node -> node -> Prop :=
| tr_Kseq: forall body cfg s pc next cont brk nret k
    (STMT: tr_stmt body cfg s pc next cont brk nret)
    (CONT: tr_cont body cfg k next cont brk nret),
    tr_cont body cfg (Kseq s k) pc cont brk nret
| tr_Kstop: forall body cfg nret
    (RET: cfg ! nret = Some Iend),
    tr_cont body cfg Kstop nret None None nret
| tr_Kloop: forall body cfg s body_start loop_jump_node exit_loop nret cont brk k
    (STMT: tr_stmt body cfg s body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (SEL: cfg ! loop_jump_node = Some (Inop body_start))
    (CONT: tr_cont body cfg k exit_loop cont brk nret),
    tr_cont body cfg (Kloop s k) loop_jump_node cont brk nret
| tr_Kdropplace: forall body cfg k pc cont brk nret f st l le own
    (CONT: tr_cont body cfg k pc cont brk nret)
    (TRFUN: tr_fun f nret cfg),
    tr_cont body cfg (Kdropplace f st l le own k) pc cont brk nret
| tr_Kdropcall: forall body cfg k pc cont brk nret st membs b ofs id
    (CONT: tr_cont body cfg k pc cont brk nret),
    tr_cont body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret
| tr_Kcall: forall body1 cfg1 body2 cfg2 k pc cont brk nret1 nret2 f le own p
    (RET: cfg1 ! nret1 = Some Iend)
    (* invariant for the caller *)
    (CONT: tr_cont body2 cfg2 k pc cont brk nret2)
    (TRFUN: tr_fun f nret2 cfg2),
    tr_cont body1 cfg1 (Kcall p f le own k) nret1 None None nret1
.


Record sound_own (own: own_env) (init uninit universe: PathsMap.t) : Type :=
  { sound_own_init: PathsMap.ge init own.(own_init);
    
    sound_own_uninit: PathsMap.ge uninit own.(own_uninit);

    sound_own_universe: PathsMap.eq universe own.(own_universe) }.

    
(** ** Semantic invariant *)

(* relation of moveing split places *)
Inductive move_split_places : own_env -> list (place * bool) -> own_env -> Prop :=
| move_split_places_nil: forall own,
    move_split_places own nil own
| move_split_places_cons: forall own1 own2 own3 p full l
    (MOVE: move_place own1 p = own2)
    (MSPLIT: move_split_places own2 l own3),
    move_split_places own1 ((p,full) :: l) own3
.
  

Section SOUNDNESS.

Variable prog: program.
Variable se: Genv.symtbl.

Let ge := RustIR.globalenv se prog.
Let ce := ge.(genv_cenv).

Inductive sound_cont: cont -> Prop :=
| sound_cont_stop: sound_cont Kstop
| sound_cont_seq: forall s k,
    sound_cont k ->
    sound_cont (Kseq s k)
| sound_cont_loop: forall s k,
    sound_cont k ->
    sound_cont (Kloop s k)
| sound_cont_call: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg k own le p cont brk nret
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (OWN: sound_own own mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_cont (Kcall p f le own k)
| sound_cont_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg k own1 own2 le st l cont brk nret
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc =  mayinit)
    (UNINIT: uninitMap !! pc =  mayuninit)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (MOVESPLIT: move_split_places own1 l own2)
    (CONT: sound_cont k),
    sound_cont (Kdropplace f st l le own1 k)
| sound_cont_dropcall: forall id b ofs st membs k,
    sound_cont k ->
    sound_cont (Kdropcall id (Vptr b ofs) st membs k)
.

  
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f initMap uninitMap pc mayinit mayuninit universe cfg s k own le m nret next cont brk
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc next cont brk nret)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (OWN: sound_own own mayinit mayuninit universe),
    sound_state (State f s k le own m)
| sound_callstate: forall vf args k m
    (CONT: sound_cont k),
    sound_state (Callstate vf args k m) 
| sound_returnstate: forall v k m
    (CONT: sound_cont k),
    sound_state (Returnstate v k m)
| sound_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe cfg k own1 own2 le st l m nret next cont brk
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc = mayinit)
    (UNINIT: uninitMap !! pc = mayuninit)
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (* small-step move_place to simulate big-step move_place in
    transfer *)
    (MOVESPLIT: move_split_places own1 l own2)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_state (Dropplace f st l k le own1 m)
| sound_dropstate: forall id b ofs st membs k m
    (CONT: sound_cont k),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
.

(* use fixpoint_soulution to prove that the final abstract env
approximates more than the abstract env computed by transfer
function *)
Lemma analyze_successor: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr pc1 pc2
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2),
    PathsMap.ge (initMap !! pc2) mayinit2
    /\ PathsMap.ge (uninitMap !! pc2) mayuninit2
.
Proof.  (* use fixpoint_solution *)
  unfold analyze; intros. 
  monadInv AN.
  rewrite EQ1 in CFG. inv CFG.
  set (params_init := (fold_right (add_place x)
               (PTree.map
                  (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
               (map
                  (fun elt : ident * type =>
                   Plocal (fst elt) (snd elt)) (fn_params f)))) in *.
  set (vars_uninit := (fold_right (add_place x)
                   (PTree.map
                      (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
                   (map
                      (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_vars f)))) in *.
  destruct (DS.fixpoint cfg successors_instr (transfer x true f cfg) entry
              params_init) eqn: INITMAP; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer x false f cfg) entry
              vars_uninit) eqn: UNINITMAP; try congruence.
  inv EQ2.
  split.
  - eapply DS.fixpoint_solution; eauto.
    (** TODO: transfer bot to bot *)
    admit.
  - eapply DS.fixpoint_solution; eauto.
    admit.
Admitted.
    
         
(* use transfer to act as the bridge to construct the succ abstract
env *)
Lemma analyze_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr own2 pc1 pc2
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2)
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
  exists mayinit3 mayuninit3,
    initMap !! pc2 = mayinit3
    /\ uninitMap !! pc2 = mayuninit3
    /\ sound_own own2 mayinit3 mayuninit3 universe.
  (* show that PathsMap.ge ae1 ae2 and sound_own ae1 implies sound_own
  ae2 *)
Proof.
  intros. exploit analyze_successor; eauto.
  intros (A & B).
  exists (initMap !! pc2), (uninitMap !! pc2).
  split; auto. split; auto.
  destruct OWN.
  constructor.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.eq_trans; eauto.
    apply PathsMap.eq_refl.
Qed.


Lemma sound_state_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr1 own2 pc1 pc2 s k m le nret next cont brk
    (AN: analyze ce f = OK (initMap, uninitMap, universe))
    (INIT: initMap !! pc1 = mayinit1)
    (UNINIT: uninitMap !! pc1 = mayuninit1)
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (SEL1: cfg ! pc1 = Some instr1)
    (PC: In pc2 (successors_instr instr1))
    (TRFUN: tr_fun f nret cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc2 next cont brk nret)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (TFINIT: transfer universe true f cfg pc1 mayinit1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 mayuninit1 = mayuninit2)
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
    sound_state (State f s k le own2 m).
Proof.
  intros. exploit analyze_succ; eauto.
  intros (mayinit3 & mayuninit3 & (A & B & C)).
  econstructor; eauto.
Qed.  


(* Key point: match the small step ownership transfer and the big step
analysis in transfer function of Sdrop *)
Lemma sound_step_droppplace: forall s t s',
    step_dropplace ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  inv MOVESPLIT.
  - econstructor; eauto.
    
    
  - econstructor; eauto.
  - econstructor; eauto.

    
Theorem sound_step: forall s t s',
    step ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  (* step_assign *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc2:= next); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    (* maybe easy *)
    unfold own_check_expr, own_check_assign in *.
    admit.
  (* step_assign_variant *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc2:= next); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    admit.
  (* step_box *)
  - inv TRSTMT. inv TRFUN.
    eapply sound_state_succ with (pc2:= next); eauto.
    simpl. auto.
    econstructor; eauto.
    econstructor.
    (* prove sound_own *)
    inv OWN.
    unfold transfer. rewrite SEL. rewrite STMT.
    admit.
  (* step_to_dropplace *)
  - inv TRSTMT.
    econstructor; eauto.
  (* step_in_dropplace *)
  -
    
Admitted.      
    
End SOUNDNESS.
