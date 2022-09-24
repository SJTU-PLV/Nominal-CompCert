Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Symbtablegen SymbtablegenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics.
Require Import RelocProgSemanticsArchi.
Require Import LocalLib AsmInject.
Require Import SymbtablegenproofArchi RelocProgGlobalenvs MemoryAgree.
Import ListNotations.
Require AsmFacts.

Open Scope Z_scope.


Ltac monadInvX1 H :=
  let monadInvX H :=  
      monadInvX1 H ||
                 match type of H with
                 | (?F _ _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 end
  in

  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X eqn:?; [try (monadInvX1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [discriminate | try (monadInvX1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInvX1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  | (match ?X with Some _ => _ | None => _ end = _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  | (match ?X with pair _ _ => _ end = OK _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  end.

Ltac monadInvX H :=
  monadInvX1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  end.  

Lemma alignw_le : forall x, x <= align x alignw.
Proof.
  intros x. apply align_le. unfold alignw. lia.
Qed.


Lemma divides_align : forall y x,
    y > 0 -> (y | x) -> align x y = x.
Proof.
  intros y x GT DV.
  unfold align. red in DV. destruct DV as [z DV].
  subst. replace (z * y + y - 1) with (z * y + (y - 1)) by lia.
  erewrite Zbits.Zdiv_shift; eauto.
  erewrite Z_div_mult; eauto. rewrite Z_mod_mult.
  rewrite zeq_true. rewrite Z.add_0_r. auto.
Qed.

Lemma align_idempotent : forall v x,
    x > 0 -> align (align v x) x = align v x.
Proof.
  intros v x H. eapply divides_align; eauto.
  apply align_divides. auto.
Qed.

Lemma alignw_divides:
  forall z,
    (alignw | align z alignw).
Proof.
  intros. apply align_divides. unfold alignw; lia.
Qed.

Lemma transf_prog_pres_senv: forall instr_size p tp,
  transf_program instr_size p = OK tp -> 
  Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p) = Genv.genv_senv (globalenv instr_size tp).
Proof.
  intros instr_size p tp TF.
  unfold transf_program in TF.
  destr_in TF. destr_in TF. destr_in TF. (* destr_in TF. *)
  (* destruct p. simpl. *)
  (* destr_in TF. *)
  (* inv TF. cbn. *)
  (* rewrite add_external_globals_pres_senv. *)
  cbn. auto.
Qed.

(** * Main Preservaiton Proofs *)
Section PRESERVATION.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Definition match_prog (p: Asm.program) (tp: program) :=
  transf_program instr_size p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program instr_size p = OK tp -> match_prog p tp.
Proof.
  auto.
Qed.


Lemma create_sec_table_correct_aux: forall n l id,
    length l = n ->
    ~In id fst##l ->
    (fold_left acc_gen_section l (PTree.empty section)) ! id = None.
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl. eapply PTree.gempty.
  exploit length_S_inv;eauto.
  intros (l'& a & A1 & A2). destruct a. subst. clear H.
  rewrite fold_left_app. simpl.
  rewrite map_app in H0.
  rewrite in_app in H0.
  eapply Decidable.not_or in H0.
  destruct H0. simpl in H0. eapply Decidable.not_or in H0.
  destruct H0. clear H1.
  destruct g.
  - destruct f.
    + rewrite PTree.gso;eauto.
    + eauto.
  - destr;eauto.
    destruct l.
    + destr;eauto;
      destr;rewrite PTree.gso;eauto.
    + destr;eauto;
        destr;rewrite PTree.gso;eauto.
Qed.

(* auxilary lemma for match_def_sec *)
Lemma create_sec_table_correct: forall n id def defs,
    length defs = n ->
    list_norepet fst ## defs ->
    In (id,def) defs ->
    (fold_left acc_gen_section defs (PTree.empty section)) ! id =
    (match def with
     | Gfun (Internal f) => Some (sec_text (fn_code f))
     | Gvar v =>
       match gvar_init v with
       | [] => None
       | [Init_space _ ] => None
       | _ =>
         if v.(gvar_readonly) then Some (sec_rodata v.(gvar_init))
         else Some (sec_rwdata v.(gvar_init))
       end
     | _ => None
     end).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  inv H1.
  exploit length_S_inv;eauto.
  intros (l'& a & A1 & A2). destruct a.
  subst. clear H.
  apply in_app in H1.
  rewrite map_app in H0.
  apply list_norepet_app in H0. destruct H0 as (A1 & A2 & A3).
  rewrite fold_left_app. simpl.
  unfold list_disjoint in A3.  
  destruct g.
  - destruct f.
    + destruct H1.
      -- rewrite PTree.gso.
         eapply IHn;eauto. eapply A3;simpl;auto.
         eapply in_map in H.
         replace id with (fst (id,def)) by auto.
         eauto.
      -- inv H. inv H0.
         rewrite PTree.gss. auto.
         inv H0.
    + destruct H1.
      -- eapply IHn;eauto. 
      -- inv H. inv H0.
         clear - A3.
         assert (~In id fst##l').
         unfold not. intros. eapply A3.
         eauto. simpl. left. eauto. eauto.
         eapply create_sec_table_correct_aux;eauto.
         inv H0.
  - destruct H1.
    + assert (id <> p).
      eapply A3. replace id with (fst (id,def)). 
      eapply in_map. auto. auto.
      simpl. auto.
      destruct (gvar_init v).
      -- eapply IHn;eauto.
      --        
        destruct l.
        destruct i;eauto;destruct gvar_readonly;
          rewrite PTree.gso;auto.                
        destruct i;
          destruct gvar_readonly;
          rewrite PTree.gso;auto. 
    + inv H. inv H0.
      destruct (gvar_init v).
      -- assert (~In id fst##l').
         unfold not. intros. eapply A3.
         eauto. simpl. left. eauto. eauto.
         eapply create_sec_table_correct_aux;eauto.         
      -- destruct l.
         destruct i;
           try (destruct gvar_readonly;
                rewrite PTree.gss;auto).
         assert (~In id fst##l').
         unfold not. intros. eapply A3.
         eauto. simpl. left. eauto. eauto.
         eapply create_sec_table_correct_aux;eauto.

         destruct i;
           try (destruct gvar_readonly;
                rewrite PTree.gss;auto).
      -- inv H0.    
Qed.

Lemma advance_next_exists: forall F V n b (defs: list (ident * globdef F V)),
    length defs = n ->
    Mem.sup_In b (Genv.advance_next defs Mem.sup_empty) ->
    exists id gd, b = Global id /\ In (id,gd) defs.
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in H0. exploit Mem.empty_in;eauto.
  intros. exfalso. auto.
  exploit length_S_inv;eauto.
  intros (l'& a & A1 & A2). destruct a.
  subst. clear H.  unfold Genv.advance_next in H0.
  rewrite fold_left_app in H0.
  simpl in H0. apply Mem.sup_incr_glob_in in H0.
  destruct H0.
  subst. exists i,g.
  split;auto. rewrite in_app.
  right. constructor;auto.
  exploit IHn;eauto.
  intros (id & gd & P1 & P2).
  subst.
  exists id,gd. split;auto.
  rewrite in_app.
  left. auto.
Qed.


Lemma gen_symb_table_in_defs: forall n id gd defs,
    length defs = n ->
    list_norepet fst##defs ->
    In (id,gd) defs ->
    (fold_left (acc_symb instr_size) defs (PTree.empty symbentry)) ! id = Some (get_symbentry instr_size id gd).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  inv H1.
  exploit length_S_inv;eauto.
  intros (l'& a & A1 & A2). destruct a.
  subst. clear H.
  rewrite fold_left_app. simpl.
  rewrite map_app in H0.
  apply list_norepet_app in H0.
  destruct H0 as (A1 & A2 & A3).
  apply in_app in H1. destruct H1.
  - simpl in *.
    unfold list_disjoint in A3.
    exploit IHn;eauto.
    intros. rewrite PTree.gso. auto.
    apply A3. eapply in_map with (f:=fst) in H.
    simpl in H. auto. constructor;auto.
  - inv H;inv H0.
    rewrite PTree.gss. auto.
Qed.

    
(** Transformation *)
Variable prog: Asm.program.
Variable tprog: program.

Let ge := Genv.globalenv prog.
Let tge := globalenv instr_size tprog.

Hypothesis TRANSF: match_prog prog tprog.

(* some properties *)
Lemma match_prog_well_formed_symbtbl:
  well_formed_symbtbl (prog_sectable tprog) (prog_symbtable tprog).
Proof.
  unfold match_prog in TRANSF.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  simpl. unfold well_formed_symbtbl.
  unfold gen_symb_table,create_sec_table.
  intros.
  inv w. 
  rename wf_prog_norepet_defs into NOREP.
  clear l.
  set (l := (AST.prog_defs prog)) in *.
  clear tge.
  assert (LEN: exists n, length l = n).
  { clear.
    induction l. exists O. auto.
    destruct IHl.
    eexists. simpl. auto. }
  destruct LEN. revert H H0.
  generalize x,l. clear.
  induction x;intros.
  rewrite length_zero_iff_nil in H0. subst.
  simpl in H. rewrite PTree.gempty in H. inv H.
  apply LocalLib.length_S_inv in H0.
  destruct H0 as (l' & a & A1 & A2). subst.
  rewrite fold_left_app in H. simpl in H.
  unfold acc_symb in H at 1.
  destruct a.
  destruct (Pos.eq_dec i id).
  - subst.
    rewrite fold_left_app. simpl.
    rewrite PTree.gss in H. inv H.
    destruct g.    
    + destruct f;simpl.     
      rewrite PTree.gss.
      eexists. eauto.
      congruence.
    + simpl;destruct (gvar_init v);simpl.
      congruence.
      destruct i;
        try (destruct gvar_readonly;
      simpl;rewrite PTree.gss;
      eexists;eauto;
      simpl;rewrite PTree.gss;
      eexists;eauto).
      destruct l;simpl;auto.
      try (destruct gvar_readonly;
      simpl;rewrite PTree.gss;
      eexists;eauto;
      simpl;rewrite PTree.gss;
      eexists;eauto).
  - rewrite fold_left_app.
    rewrite PTree.gsspec in *.
    destr_in H.    
    destruct (symbentry_secindex e).
    + simpl.
      destruct g.
      destruct f.
      rewrite PTree.gsspec. destr.
      eauto. eapply IHx;eauto.
      eapply IHx;eauto.
      destruct (gvar_init v).
      eapply IHx;eauto.
      destruct i0;
      try (destruct gvar_readonly;rewrite PTree.gsspec;destr;
           eauto;eapply IHx;eauto).
      destruct l.
      eapply IHx;eauto.
      try (destruct gvar_readonly;rewrite PTree.gsspec;destr;
           eauto;eapply IHx;eauto).
    + eapply IHx;eauto.
    + eapply IHx;eauto.
Qed.

(** ** Definitions of Matching States *)

Definition glob_block_valid (m:mem) := 
  forall b g, Globalenvs.Genv.find_def ge b = Some g -> Mem.valid_block m b.

(** Properties about the memory injection from RealAsm to Relocatable Programs *)   Record match_inj (j: meminj) : Type :=
  {
    (** Preservation of finding of instruction *)
    agree_inj_instrs:
      forall b b' f ofs ofs' i,
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
        Asm.find_instr instr_size (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
        j b = Some (b', ofs') ->
        Genv.find_instr tge (Vptr b' (Ptrofs.add ofs (Ptrofs.repr ofs'))) = Some i;

    (** Preservation of finding of global symbols *)
    agree_inj_globs:
      forall id b,
        Globalenvs.Genv.find_symbol ge id = Some b ->
        exists b' ofs', Genv.find_symbol tge id = Some (b', ofs') /\
                   j b = Some (b', Ptrofs.unsigned ofs');

    (** Preservation of finding of external functions *)
    agree_inj_ext_funct:
      forall b f ofs b',
        Globalenvs.Genv.find_funct_ptr ge b = Some (External f) ->
        j b = Some (b', ofs) ->
        Genv.find_ext_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some f;

    (** Preservation of finding of internal functions *)
    agree_inj_int_funct:
      forall b f ofs b' ofs',
        Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
        j b = Some (b', ofs) ->
        Genv.find_ext_funct tge (Vptr b' ofs') = None;
  }.



Inductive match_states: state -> state -> Prop :=
| match_states_intro: forall (rs: regset) (m: mem) (rs': regset) (m':mem) (j:meminj)
                        (STRUCTJ: j = Mem.flat_inj (Mem.support m))
                        (MATCHINJ: match_inj j)
                        (MINJ: magree j  m m')
                        (RSINJ: regset_inject j rs rs')
                        (GBVALID: glob_block_valid m),
    match_states (State rs m) (State rs' m').



(** ** Matching of the Initial States *)
  
Lemma symbol_address_inject : forall j id ofs
                                (MATCHINJ: match_inj j),
    Val.inject j (Senv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Senv.symbol_address.
  inv MATCHINJ.
  unfold Senv.find_symbol. simpl.
  destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
  exploit agree_inj_globs0; eauto.
  intros (b' & ofs' & FINDSYM' & JB).
  erewrite Genv.symbol_address_offset; eauto. 
  eapply Val.inject_ptr; eauto.
  rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_commut.
  unfold Genv.symbol_address. rewrite FINDSYM'. 
  rewrite Ptrofs.add_zero_l. auto.
Qed.

Lemma genv_pres_instr_aux3: (forall secs id ofs nmap,
   ~ In id fst ## secs ->
   fold_left
     (fun (a : NMap.t (ptrofs -> option instruction))
        (p : positive * section) =>
        acc_code_map instr_size a (fst p) (snd p)) secs
     nmap
     (Global id) ofs = nmap (Global id) ofs).
Proof.
  induction secs.
  simpl. auto.
  intros. destruct a;simpl.
  simpl in H. eapply Decidable.not_or in H.
  destruct H.
  erewrite IHsecs;auto.
  unfold acc_code_map. destruct s;simpl;auto.
  erewrite NMap.gso. auto.
  unfold not. intros. inv H1. congruence.
Qed.

Lemma ptrofs_repr_eq: forall ofs1 ofs2,
    0 <= ofs1 <= Ptrofs.max_unsigned ->
    0 <= ofs2 <= Ptrofs.max_unsigned ->
    Ptrofs.repr ofs1 = Ptrofs.repr ofs2 ->
    ofs1 = ofs2.
Proof.
  intros.
  generalize (Ptrofs.eq_spec (Ptrofs.repr ofs1) (Ptrofs.repr ofs2)).
  unfold Ptrofs.eq. rewrite Ptrofs.unsigned_repr;auto.
  rewrite Ptrofs.unsigned_repr;auto.
  destruct zeq. intros. auto.
  intros. congruence.
Qed.

Lemma acc_instr_map_fst_code_size: forall n imap c,
    length c = n ->
    code_size instr_size c <= Ptrofs.max_unsigned ->
    fst (fold_left (acc_instr_map instr_size) c (Ptrofs.zero, imap)) = Ptrofs.repr (code_size instr_size c). 
    induction n.
    intros. apply length_zero_iff_nil in H. subst. simpl. auto.
    intros. exploit length_S_inv;eauto.  intros (c' & a & ? & ?).
    subst. rewrite fold_left_app.
    simpl. unfold acc_instr_map at 1.
    destruct (fold_left (acc_instr_map instr_size) c' (Ptrofs.zero, imap)) eqn:FOLD.
    simpl. replace i with (Ptrofs.repr (code_size instr_size c')).
    rewrite code_size_app. simpl. rewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr;auto. rewrite Ptrofs.unsigned_repr.
    auto.
    generalize (instr_size_bound a). lia.
    rewrite code_size_app in H0. simpl in H0.
    generalize (instr_size_bound a). intros.
    split.
    clear -instr_size_bound.
    induction c'. simpl. lia. simpl.
    generalize (instr_size_bound a). intros. lia.
    lia.

    erewrite <- IHn. rewrite FOLD. auto. auto.
    rewrite code_size_app in H0. simpl in H0.
    generalize (instr_size_bound a). intros.
    lia.
Qed.



(** instruction map is equiv to find_instr *)
Lemma gen_instr_map_pres: forall n c ofs i,
    (code_size instr_size c) <= Ptrofs.max_unsigned ->
    Datatypes.length c = n ->
    find_instr instr_size ofs c = Some i ->
    gen_instr_map instr_size c (Ptrofs.repr ofs) = Some i.
Proof.
  induction n.
  simpl. intros. apply length_zero_iff_nil in H0. subst.
  simpl in H1. congruence.
  intros.
  exploit length_S_inv. apply H0. intros (c' & a & ? & ?).
  rewrite H2. unfold gen_instr_map.
  erewrite fold_left_app. simpl.
  unfold gen_instr_map in IHn.
  destruct ((fold_left (acc_instr_map instr_size) c'
                       (Ptrofs.zero, fun _ : ptrofs => None))) eqn:FOLD.
  simpl.
  destruct (Ptrofs.eq_dec i0 (Ptrofs.repr ofs)).
  assert (C':code_size instr_size c' <= Ptrofs.max_unsigned).
  rewrite H2 in H. rewrite code_size_app in H. simpl in H.
  generalize  (instr_size_bound a). intros.
  lia.
  
    
  generalize (acc_instr_map_fst_code_size (length c') (fun _ : ptrofs => None) c'). unfold fst.
  rewrite FOLD. intros. rewrite e in H4.
  exploit (ptrofs_repr_eq ofs (code_size instr_size c'));auto.
  generalize (find_instr_ofs_pos instr_size instr_size_bound _ _ _ H1).
  generalize (find_instr_bound instr_size instr_size_bound _ _ _ H1).
  intros. constructor. lia.
  generalize (instr_size_bound i). intros. lia.
  rewrite H2 in H. rewrite code_size_app in H. simpl in H.
  generalize (instr_size_bound a). intros.
  split. apply code_size_non_neg. apply instr_size_bound.
  lia.

  intros.
  rewrite H5 in H1. rewrite H2 in H1.
  rewrite find_instr_app' in H1.
  rewrite Z.sub_diag in H1. simpl in H1. auto.
  eapply instr_size_bound. lia.
  
  assert (o = (let
         '(_, map) :=
          fold_left (acc_instr_map instr_size) c'
                    (Ptrofs.zero, fun _ : ptrofs => None) in map)).
  rewrite FOLD. auto.
  subst. erewrite IHn;auto.
  rewrite code_size_app in H. simpl in H.
  generalize (instr_size_bound a). intros. lia.
  
  (* i0 = Ptrofs.repr code_size c' *)
  (* code_size c' < ofs or ofs < code_size c' *)
  generalize (acc_instr_map_fst_code_size (length c') (fun _ : ptrofs => None) c').
  rewrite FOLD. simpl. intros.
  rewrite H2 in n0.
  assert (code_size instr_size c' <> ofs).
  unfold not. intros. apply n0. rewrite H3. auto.
  clear - H1 H3.
  generalize ofs H3 H1. clear ofs H1 H3.
  induction c'. intros. simpl in H1. destr_in H1. subst. simpl in H3.
  congruence.
  intros.
  simpl in *. destr. eapply IHc'.
  lia. auto.
  auto.

  rewrite code_size_app in H. simpl in H.
  generalize (instr_size_bound a). intros. lia.
Qed.

Lemma genv_pres_instr_aux2:  forall defs (b : block) (f : function) (ofs : Z) (i : instruction) ge sectbl
    (* (OFS: 0 <= ofs <= Ptrofs.max_unsigned) *)
    (FSIZE: code_size instr_size (fn_code f) <= Ptrofs.max_unsigned)
    (MATCH: forall id f, Genv.genv_defs ge (Global id) = Some (Gfun (Internal f)) ->
                    sectbl ! id = Some (sec_text (fn_code f))),
    Genv.genv_defs
    (fold_left (Genv.add_global (V:=unit)) defs
       ge) b =
  Some (Gfun (Internal f)) ->
  find_instr instr_size ofs (fn_code f) = Some i ->
  fold_left
    (fun (a : NMap.t (ptrofs -> option instruction))
       (p : positive * section) =>
     acc_code_map instr_size a (fst p) (snd p))
    (PTree.elements
       (fold_left acc_gen_section defs
          sectbl))
    (NMap.init (ptrofs -> option instruction)
       (fun _ : ptrofs => None)) b (Ptrofs.repr ofs) = 
  Some i.
Proof.
  induction defs.
  simpl. intros.
  exploit (Genv.genv_defs_range). unfold NMap.get. eauto. intros.
  exploit (Genv.genv_sup_glob). eauto. intros (id & ?). subst.
  apply MATCH in H.
  exploit PTree.elements_correct. apply H. intros.
  generalize (PTree.elements_keys_norepet  sectbl). intros.
  (* no_repeat can destruct in l1++a::l2 *)
  exploit (in_norepet_unique_r);eauto. intros (gl1 & gl2 & SEC & NOTIN).
  rewrite SEC. erewrite fold_left_app.
  simpl. erewrite genv_pres_instr_aux3;eauto.
  erewrite NMap.gss.
  eapply gen_instr_map_pres;eauto.
  
  simpl. intros.
  eapply IHdefs;eauto. intros.
  destruct a.
  unfold acc_gen_section. simpl in H1.
  generalize (NMap.gsspec). unfold NMap.get. intro.
  erewrite H2 in H1. destr_in H1.
  inv e. inv H1. eapply PTree.gss.
  apply MATCH in H1. destruct g;auto.
  destruct f1;auto. erewrite PTree.gso;auto.
  unfold not. intros;subst. congruence.
  assert (id<>i0). unfold not. intros;subst. congruence.    
  destruct gvar_readonly.
  - destr.    
    destruct i1;try erewrite PTree.gso;auto.    
    destruct l;auto. destruct i0;try erewrite PTree.gso;auto.
  - destr.    
    destruct i1;try erewrite PTree.gso;auto.    
    destruct l;auto. destruct i0;try erewrite PTree.gso;auto.
Qed.

Lemma genv_pres_instr_aux1:  forall defs (b : block) (f : function) (ofs : Z) (i : instruction)
  (FSIZE: code_size instr_size (fn_code f) <= Ptrofs.max_unsigned),
    Genv.genv_defs
    (fold_left (Genv.add_global (V:=unit)) defs
       (Genv.empty_genv fundef unit (AST.prog_public prog))) b =
  Some (Gfun (Internal f)) ->
  find_instr instr_size ofs (fn_code f) = Some i ->
  fold_left
    (fun (a : NMap.t (ptrofs -> option instruction))
       (p : positive * section) =>
     acc_code_map instr_size a (fst p) (snd p))
    (PTree.elements
       (fold_left acc_gen_section defs
          (PTree.empty section)))
    (NMap.init (ptrofs -> option instruction)
       (fun _ : ptrofs => None)) b (Ptrofs.repr ofs) = 
  Some i.
Proof.
  induction defs.
  simpl. intros. unfold NMap.init in H. inv H.
  simpl. intros.
  erewrite genv_pres_instr_aux2;eauto.
  destruct a. simpl. intros.
  generalize (NMap.gsspec). unfold NMap.get. intros. erewrite H2 in H1.
  destr_in H1. inv e. inv H1.
  erewrite PTree.gss;auto. unfold NMap.init in H1. congruence.
Qed.
  

Lemma genv_pres_instr : forall b f ofs i
    (FSIZE: code_size instr_size (fn_code f) <= Ptrofs.max_unsigned),
    Globalenvs.Genv.genv_defs ge b = Some (Gfun (Internal f)) ->
    find_instr instr_size ofs (fn_code f) = Some i ->
    Genv.genv_instrs tge b (Ptrofs.repr ofs) = Some i.
Proof.
  generalize (genv_pres_instr_aux1).
  unfold ge. unfold tge. unfold match_prog in TRANSF.
  unfold transf_program in TRANSF.
  destr_in TRANSF. destr_in TRANSF.

  unfold Genv.globalenv. unfold globalenv.
  cbn [Genv.genv_instrs].
  inv TRANSF. cbn [prog_sectable].

  unfold Genv.add_globals. unfold gen_code_map.
  unfold create_sec_table.
  erewrite PTree.fold_spec.
  intros. erewrite H;eauto.
Qed.

(** transform program correct implies def size less than max unsigned *)

Lemma def_size_range: forall id def,
    In (id,def) (AST.prog_defs prog) ->
    def_size instr_size def <= Ptrofs.max_unsigned.
Proof.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  destr_in TRANSF. destr_in TRANSF.
  intros.
  clear - l H instr_size_bound.
  unfold defs_size in l.
  set (defs:=(AST.prog_defs prog)) in *.
  generalize def H l. generalize defs.
  clear - instr_size_bound.
  induction defs. simpl. intros. exfalso. auto.
  simpl. intros. destruct a. destruct H.
  - inv H. simpl in l.    
    generalize (defs_size_pos _ instr_size_bound snd##defs).
    intros. unfold defs_size in H. lia.
  - eapply IHdefs;eauto.
    simpl in l. generalize (def_size_pos _ instr_size_bound g).
    intros. lia.
Qed.

Lemma genv_defs_match: forall l id (ge1 ge2:Globalenvs.Genv.t fundef unit),
    Genv.genv_defs ge1 (Global id) = Genv.genv_defs ge2 (Global id) -> 
    Genv.genv_defs (Genv.add_globals ge1 l) (Global id) =
    Genv.genv_defs (Genv.add_globals ge2 l) (Global id).
Proof.
  induction l;simpl;intros.
  auto. eapply IHl. destruct a.
  simpl. unfold NMap.set. destr.
Qed.

Theorem init_meminj_match_sminj : forall m,
  Genv.init_mem prog = Some m ->
  match_inj (Mem.flat_inj (Mem.support m)).
Proof.
  intros m INIT.
  constructor.

  (* agree_inj_instrs *)
  intros b b' f ofs ofs' i FPTR FINST INITINJ.
  unfold Mem.flat_inj in INITINJ.
  destruct (Mem.sup_dec b (Mem.support m));try congruence.
  inv INITINJ. 
  exploit Genv.find_funct_ptr_inversion. apply FPTR.
  intros (id & DEFSIN).
  unfold Genv.find_instr.
  eapply genv_pres_instr;eauto.
  2: eapply Genv.find_funct_ptr_iff;eauto.
  (* code size <= max_unsigned *)
  eapply def_size_range in DEFSIN. auto.
  rewrite Ptrofs.unsigned_repr. erewrite Z.add_0_r. auto.
  constructor. lia.
  eapply Z.ge_le. eapply  Ptrofs.max_signed_pos.
  
  (* agree_inj_globs *)
  intros. exists b,Ptrofs.zero.
  unfold Globalenvs.Genv.find_symbol in H.
  generalize (Genv.genv_vars_eq _ _ H). intros. subst.
  generalize (Genv.genv_symb_range _ _ H). intros.
  unfold Mem.flat_inj.
  rewrite Ptrofs.unsigned_zero.
  generalize (Genv.init_mem_genv_sup _ INIT). intros.
  unfold ge in *. rewrite H1 in H0. unfold sup_In in H0.
  unfold Mem.sup_dec. destruct (Sup.sup_dec (Global id) (Mem.support m)).
  split;auto.
  (* find_symbol match genv_symb *)
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF. unfold tge. unfold Genv.find_symbol.
  simpl.
  unfold gen_symb_map.
  erewrite PTree.gmap.
  unfold gen_symb_table. unfold option_map.
  exploit Genv.find_symbol_inversion. apply H. intros. 
  inv w. unfold prog_defs_names in H2. erewrite in_map_iff in H2.
  destruct H2 as (g & EQg & INDEFS). destruct g. simpl in EQg. subst.
  exploit in_norepet_unique_r. eapply INDEFS. auto.
  intros (gl1 & gl2 & SPILT & NOTIN). rewrite SPILT.
  rewrite fold_left_app. simpl.
  set (P:= fun (m:PTree.t symbentry) => m ! id = Some (get_symbentry instr_size id g)).
  assert (forall ls m, ~ In id fst ## ls ->
                 P m ->
                 P (fold_left (acc_symb instr_size) ls m)).
  { induction ls;simpl;intros.
    auto.
    apply Decidable.not_or in H2. destruct H2. destruct a.
    eapply IHls. auto. simpl. unfold P.
    simpl in H2. erewrite PTree.gso;auto. }
  setoid_rewrite H2;auto. f_equal.

  (* lots of destruction for variable and global function here *)
  { unfold gen_global. destr. generalize Heqs0. clear Heqs0.
  destruct g. destruct f.
  simpl. intros SECEQ. inv SECEQ. auto.
  simpl. intros SECEQ. inv SECEQ.
  destruct v;simpl;destruct gvar_init;simpl.
  congruence.
  destruct i;destruct gvar_readonly;simpl;try congruence;intros SECEQ;inv SECEQ;auto.
  destruct gvar_init;simpl in *;try congruence. inv H4. auto.
  destruct gvar_init;simpl in *;try congruence. inv H4. auto. }

  unfold P. rewrite PTree.gss. auto.  
  unfold sup_In in n. congruence.
  
  (* agree_inj_ext_funct *)
  unfold Genv.find_funct_ptr. unfold Genv.find_ext_funct.
  intros. repeat destr_in H.
  unfold Mem.flat_inj in H0. repeat destr_in H0.
  unfold Ptrofs.zero. rewrite Ptrofs.eq_true.
  simpl.
  exploit Genv.init_mem_genv_sup;eauto. intros.
  exploit Genv.genv_sup_glob;eauto. rewrite <- H in s. eauto.
  intros (id & BLO). subst.
  unfold Genv.find_def in Heqo. unfold NMap.get in *.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF. inv w.
  simpl. unfold ge in Heqo.
  unfold Genv.globalenv in Heqo.
  set (init_ge := (Genv.empty_genv fundef unit (AST.prog_public prog))).
  set (P:= fun (ge:Globalenvs.Genv.t fundef unit) m  =>
             Genv.genv_defs ge (Global id) = Some (Gfun (External f)) ->
             m (Global id)= Some f).
  assert (REC: forall defs m ge
                 (UNIQUE: list_norepet fst ## defs),
             P ge m ->
         P (Genv.add_globals ge defs) (fold_right acc_extfuns m defs)).
  { induction defs;intros;simpl.
    - auto.
    - destruct a;destruct g;simpl.
      destruct f0;simpl.
      + eapply IHdefs.
        inv UNIQUE. auto.
        unfold P in *. simpl. unfold NMap.set.
        destruct (eq_block (Global id) (Global i)).
        intros. inv H1.
        auto.
      + unfold NMap.set. unfold P.
        destruct (eq_block (Global id) (Global i)).
        (* id = i *)
        inv e0. inv UNIQUE.
        set (Q := fun (ge:Globalenvs.Genv.t fundef unit) => Genv.genv_defs ge (Global i) = Some (Gfun (External e))).
        assert (Q (Genv.add_globals (Genv.add_global ge0 (i, Gfun (External e)))  defs)).
        eapply Genv.add_globals_unique_preserves with (id:= i);eauto.
        unfold Q. unfold Genv.add_global. simpl.
        unfold NMap.set. intros. destr.
        unfold Q. unfold Genv.add_global. simpl. 
        unfold NMap.set. intros. destr.
        setoid_rewrite H1. intros. inv H2. auto.
        (* id <> i *)
        intros.
        setoid_rewrite IHdefs;eauto.
        inv UNIQUE;auto.
        unfold Genv.add_globals in *.
        
        set (Q:= fun (ge1 ge2:Globalenvs.Genv.t fundef unit) l =>
                   Genv.genv_defs ge1 (Global id) = Genv.genv_defs ge2 (Global id) -> 
                   Genv.genv_defs (fold_left
                                     (Genv.add_global (V:=unit)) l
                                     ge1) (Global id) =
                   Genv.genv_defs (fold_left (Genv.add_global (V:=unit)) l
                                             ge2) (Global id)).
        assert (forall ls g1 g2, Q g1 g2 ls).
        { induction ls;simpl;intros.
        unfold Q. simpl. auto.
        unfold Q. simpl. unfold Q in IHls. intros.
        eapply IHls. destruct a.
        simpl. unfold NMap.set. destr. }           
        setoid_rewrite <- H2;eauto.
        simpl. unfold NMap.set. destr.
      + eapply IHdefs. inv UNIQUE;auto.
        unfold P. simpl. unfold NMap.set. destr.
        intros.
        setoid_rewrite H0; auto. }
  setoid_rewrite REC;eauto.
  unfold P. simpl. unfold NMap.init. congruence.
  
  (* agree_inj_int_funct *)
  simpl.
  unfold Mem.flat_inj. intros. destr_in H0. inv H0.
  destr. clear Heqb.
  rewrite  Genv.find_funct_ptr_iff in H.
  exploit Genv.init_mem_genv_sup;eauto. intros. rewrite <- H0 in s.
  exploit Genv.genv_sup_glob;eauto. intros (id & GLO). subst.
  clear s H0.
  unfold Genv.find_def in H. unfold NMap.get in *.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF. inv w.
  simpl. unfold ge in H.
  unfold Genv.globalenv in H.
  unfold gen_extfuns.
  set (P:= fun (ge:Globalenvs.Genv.t fundef unit) (m:NMap.t (option external_function))  =>
             (Genv.genv_defs ge (Global id) = Some (Gfun (Internal f)) \/             Genv.genv_defs ge (Global id) = None) ->
             m (Global id)= None).
  assert (REC: forall defs m ge
                 (UNIQUE: list_norepet fst ## defs),
             (In id fst##defs -> Genv.genv_defs ge (Global id) = None) ->
             P ge m ->
         P (Genv.add_globals ge defs) (fold_right acc_extfuns m defs)).
  { induction defs;simpl;intros.
    auto.
    destruct a;destruct g.
    destruct f0;simpl. 
    + eapply IHdefs. inv UNIQUE;auto. intros.
      inv UNIQUE. simpl. unfold NMap.set. destr.
      unfold P. simpl. unfold NMap.set. intros. destr_in H2.
      intros. unfold P in H1. eapply H1.
      inv e. simpl in H0. right. auto.
      unfold P in H1. eapply H1. auto.
    + unfold P. unfold NMap.set. destr.
      * inv e0.
      simpl in H0. assert (Genv.genv_defs ge0 (Global i) = None) by auto.
      inv UNIQUE.
      set (Q:= fun (ge:Globalenvs.Genv.t fundef unit) =>  Genv.genv_defs ge (Global i) = Some (Gfun (External e))).
      assert (Q (Genv.add_globals (Genv.add_global ge0 (i, Gfun (External e)))
       defs)).
      { eapply Genv.add_globals_unique_preserves with (id:=i);auto.
      intros. unfold Q. unfold Genv.add_global. simpl.
      unfold NMap.set. destr.
      unfold Q. simpl. unfold NMap.set. destr. }
      setoid_rewrite H3. intros. destruct H4;inv H4.
      * intros. unfold P in IHdefs. eapply IHdefs.
        inv UNIQUE. auto. intros. apply H0. right;auto.
        intros.
        setoid_rewrite H1. auto. auto.
        destruct H2.
        ++ 
        inv UNIQUE. left.
        exploit (genv_defs_match defs id (Genv.add_global ge0 (i, Gfun (External e))) ge0).
        simpl. unfold NMap.set. destr. intros.
        rewrite <- H3. auto.
        ++ right. exploit (genv_defs_match defs id (Genv.add_global ge0 (i, Gfun (External e))) ge0).
           simpl. unfold NMap.set. destr. intros.
           rewrite <- H3. auto.
    + eapply IHdefs. inv UNIQUE;auto.
      unfold P. simpl. unfold NMap.set. destr.
      intros. inv e. inv UNIQUE. congruence.
      unfold P.
      unfold Genv.add_global. simpl. unfold NMap.set. destr.
      intros. setoid_rewrite H1. auto. auto. }
  setoid_rewrite REC;eauto. intros.
  simpl. unfold NMap.init. auto.
  unfold P. simpl. auto.
Qed.


Inductive match_sec_def (id: ident) (prog: program) (gd: globdef fundef unit): Prop :=
| match_text_int: forall f code,
    gd = Gfun (Internal f) ->
    (prog_sectable prog) ! id = Some (sec_text code) ->
    (fn_code f) = code ->
    match_sec_def id prog gd
| match_rodata_var: forall v data,
    gd = Gvar v ->
    (prog_sectable prog) ! id = Some (sec_rodata data) ->
    v.(gvar_readonly) = true  ->
    v.(gvar_init) = data ->
    match_sec_def id prog gd
| match_rwdata_var: forall v data,
    gd = Gvar v ->
    (prog_sectable prog) ! id = Some (sec_rwdata data) ->
    v.(gvar_readonly) = false  ->
    v.(gvar_init) = data ->
    match_sec_def id prog gd
| match_ext_fun: forall f e,
    gd = Gfun (External f) ->
    (prog_symbtable prog) ! id = Some e ->
    (prog_sectable prog) ! id = None ->
    e.(symbentry_type) = symb_func ->
    e.(symbentry_secindex) = secindex_undef ->
    match_sec_def id prog gd
| match_ext_var: forall v e,
    gd = Gvar v ->
    v.(gvar_init) = [] ->
    (prog_symbtable prog) ! id = Some e ->
    (prog_sectable prog) ! id = None ->
    e.(symbentry_type) = symb_data ->
    e.(symbentry_secindex) = secindex_undef ->
    match_sec_def id prog gd
| match_comm: forall v e sz,
    gd = Gvar v ->
    (prog_symbtable prog) ! id = Some e ->
    (prog_sectable prog) ! id = None ->
    v.(gvar_init) = [Init_space sz] ->
    e.(symbentry_type) = symb_data ->
    e.(symbentry_secindex) = secindex_comm ->
    e.(symbentry_size) = Z.max sz 0 ->
    match_sec_def id prog gd.
              
          
Lemma init_meminj_invert_strong :forall m b b' delta ,
    Genv.init_mem prog = Some m ->
    Mem.flat_inj (Mem.support m) b = Some (b',delta) ->
    delta = 0 /\
    exists id gd,
      b = Global id
      /\ Globalenvs.Genv.find_symbol ge id = Some b
      /\ Genv.find_symbol tge id = Some (b, Ptrofs.zero)
      /\ Genv.find_def ge b = Some gd
      /\ match_sec_def id tprog gd.
Proof.
  unfold Genv.init_mem.
  intros m b b' del ALLOC INJ.  
  eapply Genv.alloc_globals_support in ALLOC.
  rewrite ALLOC in INJ. clear ALLOC.
  unfold Mem.flat_inj in INJ.
  destr_in INJ. inv INJ.
  split;auto.  
  unfold ge,tge.
  unfold match_prog in TRANSF.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  unfold globalenv. simpl. unfold Genv.find_symbol.
  simpl.

  rewrite Mem.support_empty in s.
  exploit advance_next_exists;eauto.
  intros (id & gd & P1 & P2). subst.

  exists id,gd. split;auto.
  split.

  (* ge find_symbol *)
  apply Genv.find_symbol_exists in P2.
  destruct P2. rewrite H.  eapply Genv.genv_vars_eq in H.
  subst. auto.

  split.
  (* tge find_symbol *)
  unfold gen_symb_map.
  unfold gen_symb_table.
  rewrite PTree.gmap. unfold option_map.

  inv w.
  erewrite gen_symb_table_in_defs;eauto.
  f_equal. unfold gen_global. destruct gd;simpl.
  destruct f;simpl;auto.
  destruct (gvar_init v);simpl;auto.
  destruct i;auto;destruct (gvar_readonly v);auto;
  destruct l0;auto.


  split.
  (* find_def *)
  exploit prog_defmap_norepet;eauto.
  unfold prog_defs_names. inv w.
  auto. intros P3.
  eapply Genv.find_def_symbol in P3.
  destruct P3 as (b & B1 & B2).
  eapply Genv.genv_vars_eq in B1.
  subst. auto.

  (* transf_program_match_def : proved here*)
  clear s l.
  
  destruct gd.
  - destruct f.
    + econstructor;eauto.
      simpl. unfold create_sec_table.
      inv w.
      exploit create_sec_table_correct;eauto.
    + eapply match_ext_fun;eauto;simpl.
      inv w.
      unfold gen_symb_table.
      erewrite gen_symb_table_in_defs;eauto.
      unfold create_sec_table.
      erewrite create_sec_table_correct;eauto. simpl.
      auto. inv w. auto.
      simpl. auto.
      simpl. auto.
  - destruct v.
    destruct gvar_init.
    + eapply match_ext_var;eauto.
      simpl. unfold gen_symb_table.
      erewrite gen_symb_table_in_defs;eauto.
      inv w;auto.
      simpl. unfold create_sec_table.
      erewrite create_sec_table_correct;eauto. simpl.
      auto. inv w. auto.
      simpl. auto.
      simpl. auto.
    + destruct (gvar_init).
      * assert ({exists sz, i=Init_space sz} + {not (exists sz, i=Init_space sz)}).
        { destruct i.
          1-6: (right;unfold not;intros;destruct H;inv H).
          left. exists z. auto.
          right;unfold not;intros;destruct H;inv H. }
        destruct H.
        -- destruct e. subst.
           eapply match_comm;eauto.
           simpl. unfold gen_symb_table.
           erewrite gen_symb_table_in_defs;eauto.
           inv w;auto.
           simpl. unfold create_sec_table.
           erewrite create_sec_table_correct;eauto. simpl.
           auto. inv w. auto.
           simpl. eauto.
           simpl. auto.
           simpl. auto.
           simpl. auto.
        -- destruct gvar_readonly.
           ++ eapply match_rodata_var;eauto.
              simpl. unfold create_sec_table.
              erewrite create_sec_table_correct;eauto. simpl.
              destruct i;auto.
              exfalso. apply n. eauto.
              inv w. auto.
           ++ eapply match_rwdata_var;eauto.
              simpl. unfold create_sec_table.
              erewrite create_sec_table_correct;eauto. simpl.
              destruct i;auto.
              exfalso. apply n. eauto.
              inv w. auto.
      * destruct gvar_readonly.
        -- eapply match_rodata_var;eauto.
           simpl. unfold create_sec_table.
           erewrite create_sec_table_correct;eauto. simpl.
           destruct i;auto.         
           inv w. auto.
        -- eapply match_rwdata_var;eauto.
           simpl. unfold create_sec_table.
           erewrite create_sec_table_correct;eauto. simpl.
           destruct i;auto.         
           inv w. auto.           
Qed.



Section INIT_MEM.

Variables m tm: mem.
Hypothesis IM: Genv.init_mem prog = Some m.
Hypothesis TIM: init_mem instr_size tprog = Some tm.

  
Lemma bytes_of_init_inject:
  forall il,
  list_forall2 (memval_inject (Mem.flat_inj (Mem.support m))) (Genv.bytes_of_init_data_list ge il) (bytes_of_init_data_list tge il).
Proof.
  induction il.
  - simpl. constructor.
  - simpl. eapply list_forall2_app;eauto.
    destruct a;simpl.
    generalize (Int.unsigned i). intros.
    generalize (encode_int_length 1 z). 
    generalize  (encode_int 1 z). intros.
    do 2 (destruct l as [|? l];simpl in H;try congruence).
    constructor. constructor. constructor.
    generalize (Int.unsigned i). intros.
    generalize (encode_int_length 2 z). 
    generalize  (encode_int 2 z). intros.
    do 3 (destruct l as [|? l];simpl in H;try congruence).
    repeat constructor.
    generalize (Int.unsigned i). intros.
    generalize (encode_int_length 4 z). 
    generalize  (encode_int 4 z). intros.
    do 5 (destruct l as [|? l];simpl in H;try congruence).
    repeat constructor. 
    generalize (Int64.unsigned i). intros.
    generalize (encode_int_length 8 z). 
    generalize  (encode_int 8 z). intros.
    do 9 (destruct l as [|? l];simpl in H;try congruence).
    repeat constructor. 
    generalize (Int.unsigned (Float32.to_bits f)). intros.
    generalize (encode_int_length 4 z). 
    generalize  (encode_int 4 z). intros.
    do 5 (destruct l as [|? l];simpl in H;try congruence).
    repeat constructor.
    generalize (Int64.unsigned (Float.to_bits f)). intros.
    generalize (encode_int_length 8 z). 
    generalize  (encode_int 8 z). intros.
    do 9 (destruct l as [|? l];simpl in H;try congruence).
    repeat constructor. 

    generalize (Z.to_nat z). clear.
    induction n. simpl. constructor.
    simpl. constructor. constructor.
    eauto.
    
    destruct Archi.ptr64.
    destr. exploit init_meminj_match_sminj;eauto.
    intros. exploit agree_inj_globs;eauto.
    intros (b' & ofs' & A & B).
    unfold Mem.flat_inj in B. destr_in B. inv B. rewrite A.
    eapply inj_value_inject.
    econstructor. unfold Mem.flat_inj. destr.
    rewrite H2.
    rewrite Ptrofs.repr_unsigned. auto.
    destr. destruct p.
    simpl.
    unfold inj_value. simpl.
    repeat constructor.
    simpl. repeat constructor.

    destr. exploit init_meminj_match_sminj;eauto.
    intros. exploit agree_inj_globs;eauto.
    intros (b' & ofs' & A & B).
    unfold Mem.flat_inj in B. destr_in B. inv B. rewrite A.
    eapply inj_value_inject.
    econstructor. unfold Mem.flat_inj. destr.
    rewrite H2.
    rewrite Ptrofs.repr_unsigned. auto.
    destr. destruct p.
    simpl.
    unfold inj_value. simpl.
    repeat constructor.
    simpl. repeat constructor.
Qed.

    
(** copy from Unusedglobproof *)
Lemma Mem_getN_forall2:
  forall (P: memval -> memval -> Prop) c1 c2 i n p,
  list_forall2 P (Mem.getN n p c1) (Mem.getN n p c2) ->
  p <= i -> i < p + Z.of_nat n ->
  P (ZMap.get i c1) (ZMap.get i c2).
Proof.
  induction n; simpl Mem.getN; intros.
- simpl in H1. extlia.
- inv H. rewrite Nat2Z.inj_succ in H1. destruct (zeq i p).
+ congruence.
+ apply IHn with (p + 1); auto. lia. lia.
Qed.


Lemma init_mem_inj_1:
  Mem.mem_inj (Mem.flat_inj (Mem.support m)) m tm.
Proof.  
  constructor;intros.
  - exploit init_meminj_invert_strong;eauto.
    intros (DEL & id & gd & GDEQ & FINDSYM1 & FINDSYM2 & FINDEF & MATCH). subst delta.
    rewrite Z.add_0_r.
    exploit (Genv.init_mem_characterization_gen);eauto. intro INIT1.
    exploit (init_mem_characterization_gen). apply TIM. apply GDEQ.
    intro INIT2.
    inv MATCH.
    + rewrite H2 in *.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      simpl in OFSRANGE.
      apply OFSRANGE1 in H0. destruct H0. subst.
      eapply Mem.perm_cur. auto.
    + rewrite H2 in *.  simpl in INIT2.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      apply OFSRANGE1 in H0. destruct H0.
      apply PERM in H.
      unfold Genv.perm_globvar in H0.
      rewrite H3 in H0.
            eapply Mem.perm_cur.
      destr_in H0. inv H0.
      eapply Mem.perm_implies. eauto.
      constructor.
      eapply Mem.perm_implies. eauto.
      constructor.
      eapply Mem.perm_implies. eauto.
      auto.
    + rewrite H2 in *.  simpl in INIT2.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      apply OFSRANGE1 in H0. destruct H0.
      apply PERM in H.
      unfold Genv.perm_globvar in H0.
      rewrite H3 in H0.
            eapply Mem.perm_cur.
      destr_in H0. inv H0.
      eapply Mem.perm_implies. eauto.
      constructor.
      eapply Mem.perm_implies. eauto.
      constructor.
      eapply Mem.perm_implies. eauto.
      auto.
    + rewrite H3 in *. rewrite H2 in *.
      rewrite H4 in *. rewrite H5 in *.
      simpl in INIT2.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      simpl in OFSRANGE.
      apply OFSRANGE1 in H0. destruct H0. subst.
      eapply Mem.perm_cur. auto.
    + rewrite H4 in *. rewrite H3 in *.
      rewrite H5 in *. rewrite H6 in *.
      simpl in INIT2.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      simpl in OFSRANGE.
      apply OFSRANGE1 in H0. destruct H0.
      rewrite H2 in H. simpl in H. lia.
    + rewrite H3 in *. rewrite H2 in *.
      rewrite H5 in *. rewrite H6 in *.
      simpl in INIT2.
      unfold Mem.flat_inj in H. destr_in H. inv H.
      destruct INIT2 as (PERM & OFSRANGE).
      destruct INIT1 as (PERM1 & OFSRANGE1).
      rewrite H7 in *. rewrite H4 in *.
      apply OFSRANGE1 in H0. destruct H0.
      simpl in H. rewrite Z.add_0_r in H.
      apply PERM in H.
      apply Mem.perm_cur.
      eapply Mem.perm_implies. eauto.
      unfold Genv.perm_globvar in H0.
      destr_in H0. inv H0;constructor.
      destr_in H0. inv H0;constructor.
      
      
  - exploit init_meminj_invert_strong;eauto.
    intros (DEL & id & gd & GDEQ & FINDSYM1 & FINDSYM2 & FINDEF & MATCH). subst delta.
    apply Z.divide_0_r.
  - exploit init_meminj_invert_strong;eauto.
    intros (DEL & id & gd & GDEQ & FINDSYM1 & FINDSYM2 & FINDEF & MATCH). subst delta.
    rewrite Z.add_0_r.
    unfold Mem.flat_inj in H. destr_in H. inv H.
    exploit (Genv.init_mem_characterization_gen);eauto. intro INIT1.
    exploit (init_mem_characterization_gen). apply TIM. eapply (eq_refl (Global id)).
    intro INIT2.
    inv MATCH.
    + rewrite H1 in *.
      destruct INIT1. apply H2 in H0.
      destruct H0. discriminate.
    + rewrite H1 in *.
      simpl in INIT2.
      destruct INIT1 as (RPERM1 & OFSRANGE1  & LOADSTORE1 & BYTES1).
      apply OFSRANGE1 in H0. destruct H0.      
      unfold Genv.perm_globvar in *.
      rewrite H2 in *. destruct (gvar_volatile v).
      inv H0.
      destruct INIT2 as (RPERM & OFSRANGE & LOADSTORE & BYTES).
      Local Transparent Mem.loadbytes.
      unfold Mem.loadbytes in BYTES.
      destr_in BYTES.
      generalize (BYTES1 (eq_refl false)).
      unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
      inv BYTES.
      (* H4 and H5 *)
      eapply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
      rewrite H4,H5. apply bytes_of_init_inject. lia. lia.
    + rewrite H1 in *.
      simpl in INIT2.
      destruct INIT1 as (RPERM1 & OFSRANGE1  & LOADSTORE1 & BYTES1).
      apply OFSRANGE1 in H0. destruct H0.      
      unfold Genv.perm_globvar in *.
      rewrite H2 in *. destruct (gvar_volatile v).
      inv H0.
      destruct INIT2 as (RPERM & OFSRANGE & LOADSTORE & BYTES).
      Local Transparent Mem.loadbytes.
      unfold Mem.loadbytes in BYTES.
      destr_in BYTES.
      generalize (BYTES1 (eq_refl false)).
      unfold Mem.loadbytes. destruct Mem.range_perm_dec; intros E1; inv E1.
      inv BYTES.
      (* H4 and H5 *)
      eapply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (init_data_list_size (gvar_init v))).
      rewrite H4,H5. apply bytes_of_init_inject. lia. lia.
      
    + rewrite H2,H1,H3,H4 in *.
      destruct INIT1. apply H5 in H0.
      destruct H0. discriminate.
      
    + rewrite H2,H1,H3,H4,H5 in *.
      simpl in INIT1.
      destruct INIT1. apply H6 in H0.
      destruct H0. lia.
    + rewrite H2,H1,H3,H4,H5,H6 in *.
      simpl in *.
      destruct INIT1 as (RPERM1 & OFSRANGE1  & LOADSTORE1 & BYTES1).
      apply OFSRANGE1 in H0. destruct H0.      
      unfold Genv.perm_globvar in *.
      destruct (gvar_volatile v).
      inv H0.
      destruct INIT2 as (RPERM & OFSRANGE & LOADSTORE & BYTES).

      eapply Mem_getN_forall2 with (p := 0) (n := Z.to_nat (Z.max sz 0)).
      Local Transparent Mem.loadbytes.
      unfold Mem.loadbytes in *.
      destr_in BYTES. inv BYTES.
      generalize (BYTES1 (eq_refl false)).
      intros. destr_in H7. rewrite Z.add_0_r in H7.
      rewrite app_nil_r in H7.
      inv H7. rewrite H8,H10.
      rewrite app_nil_r.
      assert ((Z.to_nat sz) = (Z.to_nat (Z.max sz 0))).
      destruct sz;simpl;lia.
      rewrite <- H7.
      set (n:= Z.to_nat sz).
      clear H7. induction n.
      simpl. constructor.
      simpl. constructor. apply memval_inject_byte.
      auto.
      lia. lia.
Qed.


Lemma init_mem_inj_2:
  magree (Mem.flat_inj (Mem.support m)) m tm.
Proof.
  constructor;intros.
  - apply init_mem_inj_1.
  - unfold Mem.flat_inj. destr.
  - exploit init_meminj_invert_strong;eauto.
    intros (DEL & id & gd & GDEQ & FINDSYM1 & FINDSYM2 & FINDEF & MATCH). subst delta.
    unfold Mem.flat_inj in H. destr_in H. inv H.
    unfold Mem.valid_block. 
    (* need Genv.find_symbol_not_fresh for tge*)
    eapply find_symbol_not_fresh;eauto.
    eapply match_prog_well_formed_symbtbl.
      
  - red;intros.
    unfold Mem.flat_inj in *.
    destr_in H0. destr_in H1.
  - unfold Mem.flat_inj in *.
    destr_in H. inv H.
    split. lia. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
Qed.

Lemma alloc_stack_pres_inject:
  forall lo hi stk stk' j m' tm',
    Mem.alloc m lo hi = (m', stk) ->
    Mem.alloc tm lo hi = (tm', stk') ->
    j = (Mem.flat_inj (Mem.support m')) ->
    magree j m' tm' /\ stk = stk' /\ match_inj j.
Proof.
  intros.
  exploit (Genv.init_mem_stack);eauto.
  exploit (init_mem_stack);eauto.
  exploit (Mem.alloc_result m);eauto.
  exploit (Mem.alloc_result tm);eauto.
  intros. subst. unfold Mem.nextblock. unfold Mem.fresh_block.
  rewrite H4. rewrite H5. simpl.
  generalize  init_mem_inj_2. intro INJ.
  exploit (alloc_parallel_inject);eauto.
  apply Z.le_refl. apply Z.le_refl.
  (* unfold Mem.nextblock. unfold Mem.fresh_block. repeat rewrite H5. *)
  (* simpl. *)
  intros (f' & m2' & b2 & A & B & C & D & E).
  rewrite H0 in A. inv A.
  assert (f' = Mem.flat_inj (Mem.support m')).
  { apply Axioms.functional_extensionality.
    intros.
    destruct (eq_block x (Mem.nextblock m)).
    subst. rewrite D. unfold Mem.flat_inj.
    exploit (Mem.valid_new_block). apply H.
    unfold Mem.valid_block.
    intros. destr. f_equal. f_equal.
    eapply Mem.stackeq_nextblock. rewrite H4,H5.
    auto.
    erewrite E;auto. unfold Mem.flat_inj.
    destruct (Mem.sup_dec x (Mem.support m)).
    exploit Mem.sup_include_alloc. apply H. apply s.
    intro;destr.
    destr.
    exploit Mem.support_alloc. apply H. intro.
    rewrite H1 in *. apply Mem.sup_incr_in in s.
    destruct s. unfold Mem.nextblock in n. congruence.
    congruence. }
  rewrite <- H1. split;auto.
  split;auto.
  exploit init_meminj_match_sminj;eauto. intro MATCHINJ.
  subst.
  constructor.
  - intros. eapply agree_inj_instrs;eauto.
    unfold Mem.flat_inj in H3. destr_in H3. inv H3.
    unfold Mem.flat_inj.
    exploit Genv.find_funct_ptr_not_fresh;eauto.
    unfold Mem.valid_block.
    unfold Mem.sup_dec. intro. destr.
  - intros. exploit agree_inj_globs;eauto.
    intros (b' & ofs' & P & Q).
    exists b',ofs'. split;auto.
  - intros. eapply agree_inj_ext_funct;eauto.
    unfold Mem.flat_inj in H2. destr_in H2. inv H2.
    unfold Mem.flat_inj.
    exploit Genv.find_funct_ptr_not_fresh;eauto.
    unfold Mem.valid_block.
    unfold Mem.sup_dec. intro. destr.
  - intros. eapply agree_inj_int_funct;eauto.
    unfold Mem.flat_inj in H2. destr_in H2. inv H2.
    unfold Mem.flat_inj.
    exploit Genv.find_funct_ptr_not_fresh;eauto.
    unfold Mem.valid_block.
    unfold Mem.sup_dec. intro. destr.
Qed.


End INIT_MEM.

(* Need preserve match_inj lemma after store*)
Lemma storev_pres_match_inj:
  forall chunk m m' addr v,
    Mem.storev chunk m addr v = Some m' ->
    match_inj (Mem.flat_inj (Mem.support m)) ->
    match_inj (Mem.flat_inj (Mem.support m')).
Proof.
  intros.
  exploit Mem.support_storev;eauto. intros.
  rewrite <- H1.
  auto.
Qed.

Lemma storev_pres_inject:
  forall chunk j m1 m1' m2 a a' v v',
    Mem.storev chunk m1 a v = Some m2 ->
    magree j m1 m1' ->
    Val.inject j v v' ->
    Val.inject j a a' ->
    j = (Mem.flat_inj (Mem.support m1)) ->
    exists m2',  Mem.storev chunk m1' a' v' = Some m2' /\ magree (Mem.flat_inj (Mem.support m2)) m2 m2'.
Proof.
  intros.
  exploit Mem.support_storev;eauto. intros.
  exploit storev_mapped_inject;eauto.
  intros (n2 & A & B).
  exists n2. rewrite <- H4. subst. split;auto.
Qed.


Definition init_data_list_aligned (sec:section) :=
  match sec with
  | sec_text _ => True
  | sec_rodata l | sec_rwdata l => Genv.init_data_list_aligned 0 l
  end.

Lemma alloc_sections_exists: forall n ge secs m0,
    length secs = n ->
    (forall sec, In sec snd ## secs -> init_data_list_aligned sec) ->
    exists m', fold_left
            (fun (a : option mem) (p : positive * section) => alloc_section instr_size ge a (fst p) (snd p))
            secs (Some m0) = Some m'.
Proof.
  induction n;intros.
  - eapply length_zero_iff_nil in H. subst.
    simpl.
    eexists. split;eauto.  
  - eapply length_S_inv in H.
    destruct H as (l' & a & P1 & P2). subst.
    exploit IHn;eauto.
    intros. eapply H0. rewrite map_app. eapply in_app.
    auto.
    intros (m' & Q1).
    rewrite fold_left_app. simpl.
    rewrite Q1. 
    assert (exists m'', alloc_section instr_size ge0 (Some m') (fst a) (snd a) = Some m'').
    { unfold alloc_section.
      destruct a;simpl.
      exploit (H0 s). rewrite map_app.
      apply in_app. right. simpl. auto.
      intros ALIGN.
      destruct s.
    + destruct (Mem.alloc_glob p m' 0 (sec_size instr_size (sec_text code))) eqn:FOLD.
      simpl. simpl in FOLD.
      unfold Mem.drop_perm. destr.
      eexists. eauto.
      unfold Mem.range_perm in n. exfalso.
      eapply n. intros. eapply Mem.perm_alloc_glob_2;eauto.
    + simpl. destruct (Mem.alloc_glob p m' 0 (init_data_list_size init)) eqn:FOLD.
      exploit Genv.store_zeros_exists.
      unfold Mem.range_perm. intros. eapply Mem.perm_alloc_glob_2 with (lo:=0);eauto.
      rewrite <- (Z.add_0_l (init_data_list_size init)). eauto.
      intros (m0' & STORE). rewrite STORE.
      exploit store_init_data_list_exists.
      eapply store_zeros_pres_range_perm with (lo:=0).
      rewrite Z.add_0_l. eauto.
      rewrite Z.add_0_l. unfold Mem.range_perm. intros. eapply Mem.perm_alloc_glob_2;eauto.
      simpl in ALIGN. auto.
      intros (m'' & A). rewrite A.
      unfold Mem.drop_perm.
      destr. eexists. eauto.
      unfold Mem.range_perm in n. exfalso.
      eapply n. intros. eapply store_init_data_list_perm in A;eauto.
      eapply A. eapply Genv.store_zeros_perm in STORE;eauto.
      eapply STORE. eapply Mem.perm_alloc_glob_2;eauto.
    + simpl. destruct (Mem.alloc_glob p m' 0 (init_data_list_size init)) eqn:FOLD.
      exploit Genv.store_zeros_exists.
      unfold Mem.range_perm. intros. eapply Mem.perm_alloc_glob_2 with (lo:=0);eauto.
      rewrite <- (Z.add_0_l (init_data_list_size init)). eauto.
      intros (m0' & STORE). rewrite STORE.
      exploit store_init_data_list_exists.
      eapply store_zeros_pres_range_perm with (lo:=0).
      rewrite Z.add_0_l. eauto.
      rewrite Z.add_0_l. unfold Mem.range_perm. intros. eapply Mem.perm_alloc_glob_2;eauto.
      simpl in ALIGN. auto.
      intros (m'' & A). rewrite A.
      unfold Mem.drop_perm.
      destr. eexists. eauto.
      unfold Mem.range_perm in n. exfalso.
      eapply n. intros. eapply store_init_data_list_perm in A;eauto.
      eapply A. eapply Genv.store_zeros_perm in STORE;eauto.
      eapply STORE. eapply Mem.perm_alloc_glob_2;eauto. }

    destruct H. rewrite H. exists x. split;auto.
Qed.      

Lemma alloc_globals_app1: forall F V (l1 l2: list (ident*globdef F V)) m0 m ge,
    Genv.alloc_globals ge m0 (l1++l2) = Some m ->
    exists m', (Genv.alloc_globals ge m0 l1 = Some m' /\
          Genv.alloc_globals ge m' l2 = Some m).
Proof.
  induction l1;simpl;eauto.
  intros. destr_in H.
  eapply IHl1 in H.
  destruct H as (m' & A & B).
  rewrite A. eexists m'.
  split;eauto.
Qed.

Lemma allocs_globals_init_data_list_aligned: forall n defs id sec m m' ge,
    length defs = n ->
    Genv.alloc_globals ge m defs = Some m' ->
    In (id,sec) (PTree.elements (create_sec_table defs)) ->
    init_data_list_aligned sec.
Proof.
  induction n;intros.
  eapply length_zero_iff_nil in H. subst.    
  simpl in H0.  exfalso;auto.

  eapply length_S_inv in H.
  destruct H as (l' & a & P1 & P2). subst.  

  eapply alloc_globals_app1 in H0.
  destruct H0 as (m'' & A & B).
  simpl in B. destr_in B.
  inv B. eapply PTree.elements_complete in H1.
  unfold create_sec_table in H1.
  rewrite fold_left_app in H1. simpl in H1.
  unfold acc_gen_section at 1 in H1.
  destruct a. destruct g.
  - destruct f.  
    + rewrite PTree.gsspec in H1.
      destr_in H1.
      * inv H1. simpl. auto.
      * eapply IHn;eauto.
        eapply PTree.elements_correct. unfold create_sec_table.
        eauto.
    + eapply IHn;eauto.
      eapply PTree.elements_correct. unfold create_sec_table.      
      eauto.
  - destr_in H1.
    + eapply IHn;eauto.
      eapply PTree.elements_correct. unfold create_sec_table.      
      eauto.
    + destruct l.
      * destruct (gvar_readonly v).
        -- destruct i0;
           try 
           (rewrite PTree.gsspec in H1;
           destr_in H1;
           [inv H1;simpl; split; [apply Z.divide_0_r| auto]|
            eapply IHn;eauto;
            eapply PTree.elements_correct;unfold create_sec_table;
            eauto]).
           eapply IHn;eauto;
           eapply PTree.elements_correct;unfold create_sec_table;
             eauto.
        -- destruct i0;
           try 
           (rewrite PTree.gsspec in H1;
           destr_in H1;
           [inv H1;simpl; split; [apply Z.divide_0_r| auto]|
            eapply IHn;eauto;
            eapply PTree.elements_correct;unfold create_sec_table;
            eauto]).
           eapply IHn;eauto;
           eapply PTree.elements_correct;unfold create_sec_table;
             eauto.
      * unfold Genv.alloc_global in Heqo.
        destruct (Mem.alloc_glob i m'' 0 (init_data_list_size (gvar_init v))).
        destr_in Heqo. destr_in Heqo.
        eapply Genv.store_init_data_list_aligned in Heqo1.
        rewrite Heql in *. 
        destruct (gvar_readonly v).
        -- destruct i0;
           try (rewrite PTree.gsspec in H1;
           destr_in H1;
           [inv H1;unfold init_data_list_aligned;auto|
            destruct sec;eauto;eapply IHn;eauto;
            eapply PTree.elements_correct;unfold create_sec_table;
            eauto]).
        -- destruct i0;
           try (rewrite PTree.gsspec in H1;
           destr_in H1;
           [inv H1;unfold init_data_list_aligned;auto|
            destruct sec;eauto;eapply IHn;eauto;
            eapply PTree.elements_correct;unfold create_sec_table;
            eauto]).
Qed.
           
(** hard: auxilary lemma for init_mem_exists *)
Lemma alloc_globals_alloc_sections_exists: forall defs ge1 ge2 m1 m1' m2,
    Genv.alloc_globals ge1 m1 defs = Some m1' ->
    exists m2', fold_left 
       (fun (a : option mem) (p : positive * section) =>
            alloc_section instr_size ge2 a (fst p) (snd p))
       (PTree.elements (create_sec_table defs)) (Some m2) = Some m2'.
Proof.
  intros.
  set (l:= (PTree.elements (create_sec_table defs))).
  eapply alloc_sections_exists;eauto.
  intros.
  eapply in_map_iff in H0.
  destruct H0 as (x & A & B). destruct x.
  simpl in A. subst.
  eapply allocs_globals_init_data_list_aligned in H;eauto.
Qed.

Lemma alloc_globals_alloc_external_exists: forall defs ge m1 m1' m2,
    Genv.alloc_globals ge m1 defs = Some m1' ->
    exists m2', alloc_external_symbols m2 (gen_symb_table instr_size defs) = Some m2'.
Admitted.


Lemma init_mem_exists:
  forall m, Genv.init_mem prog = Some m ->
  exists tm, init_mem instr_size tprog = Some tm.
Proof.
  unfold init_mem,Genv.init_mem.
  intros m M1.
  (* exploit (alloc_globals_alloc_sections_exists (AST.prog_defs prog) (Genv.globalenv prog) ((globalenv instr_size tprog)) (Mem.empty) m (Mem.empty));eauto. *)
  (* intros (m2' & A). *)
  destr.
  generalize (alloc_globals_alloc_external_exists _ _ _ _ m0 M1).
  intros (m1 & E). exists m1.
  assert ((gen_symb_table instr_size (AST.prog_defs prog)) = (prog_symbtable tprog)).
  { unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF. simpl. auto. }
  rewrite <- H. auto.
  assert (exists m', alloc_sections instr_size (globalenv instr_size tprog) (prog_sectable tprog) Mem.empty = Some m').
  {
    generalize TRANSF. intros TRANSF'.
    unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
    destr_in TRANSF'.  destr_in TRANSF'. inversion TRANSF'.
    simpl.
    unfold alloc_sections. simpl.
    rewrite PTree.fold_spec.
    eapply alloc_globals_alloc_sections_exists;eauto. }
   destruct H. congruence.
Qed.


Lemma init_mem_pres_inject :
  forall m
    (INITMEM: Genv.init_mem prog = Some m),
  exists m', init_mem instr_size tprog = Some m' /\ magree (Mem.flat_inj (Mem.support m)) m m'.
Proof.
  intros.
  exploit init_mem_exists;eauto.
  intros (tm & INIT1). exists tm.
  exploit (init_mem_inj_2);eauto.
Qed.


Lemma val_inject_set:
  forall j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    v v' (VINJ: Val.inject j v v') r1 r,
    Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
Proof.
  intros.
  destruct (PregEq.eq r1 r); subst; auto.
  rewrite ! Pregmap.gss; auto.
  rewrite ! Pregmap.gso by auto. auto.
Qed.

Lemma transf_initial_states : forall rs st1,
    RealAsm.initial_state prog st1 ->
    exists st2, initial_state instr_size tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs st1 INIT.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF. 2: congruence. destr_in TRANSF'. 
  inv INIT.
  exploit (init_mem_pres_inject m0);eauto.
  intros (m0' & INITM' & MINJ).
  (* exploit (Mem.alloc_parallel_inject (Mem.flat_inj (Mem.support m0)) *)
  (*              m0 m0' 0 (max_stacksize + align (size_chunk Mptr) 8) *)
  (*              m1 stk 0 (max_stacksize + align (size_chunk Mptr) 8));eauto;try lia. *)
  exploit (Mem.valid_new_block m0);eauto. unfold Mem.valid_block. intros VALIDSTK.
  caseEq (Mem.alloc m0' 0 (max_stacksize + align (size_chunk Mptr) 8)).
  intros m1'  stk'  H0'.
  exploit (alloc_stack_pres_inject m0 m0');eauto.
  intros (MINJ1 &  STK &  MATINJ1). subst.  
  exploit (storev_pres_match_inj Mptr m1 m2);eauto.
  intros MATINJ2.
  edestruct storev_pres_inject as (m2' & ST & SMINJ). apply H1. apply MINJ1. econstructor. econstructor.
  (* stk' is valid *)
  unfold Mem.flat_inj. destruct (Mem.sup_dec stk' (Mem.support m1)).
  eauto. congruence.
  eapply eq_refl. constructor.
  (* regset *)
  set (rs0' := rs # PC <- (Genv.symbol_address tge tprog.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk' (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.

  (* instantiate the initial state*)
  exists (State rs0' m2').
  split. 
  (* initial_state *)
  - econstructor;eauto.
    econstructor;eauto.
  - econstructor;eauto.
    unfold regset_inject. intros.
    
    unfold rs0',rs0.
    apply val_inject_set.
    apply val_inject_set.
    apply val_inject_set.
    auto.
      (* main function *)
      destr_in TRANSF'. simpl.
     exploit (agree_inj_globs (Mem.flat_inj (Mem.support m2)) MATINJ2 ((AST.prog_main prog)) bmain). auto.
     intros (bmain' & ofs' & MAIN' & MAININJ).
     (* proof bmain is valid in m2 support *)
     exploit (Genv.find_symbol_not_fresh). apply H. apply H2. intros VALIDMAIN0.
     exploit (Mem.valid_block_alloc). apply H0. apply VALIDMAIN0. intros VALIDMAIN1.
     exploit (Mem.support_store). apply H1. intros SUPEQ.
     unfold Mem.valid_block in VALIDMAIN1.
     rewrite <- SUPEQ in VALIDMAIN1. unfold Mem.flat_inj in MAININJ.
     destruct (Mem.sup_dec bmain (Mem.support m2));try congruence.
     destr_in MAININJ.
     unfold Genv.symbol_address.
     rewrite MAIN'. econstructor.
     unfold Mem.flat_inj. destruct (Mem.sup_dec bmain' (Mem.support m2));try congruence. eauto.
     rewrite Ptrofs.add_unsigned. rewrite Ptrofs.add_zero.
     rewrite <- H6. rewrite Z.add_0_r. rewrite Ptrofs.unsigned_zero. auto.
     constructor.
     cbn [Val.offset_ptr].
     rewrite Ptrofs.sub_add_opp.
     econstructor.
     (* prove SSAsm.stkblock = stk' = stk *)
     exploit (Genv.init_mem_stack). eapply H. intros.
     exploit (init_mem_stack). eapply INITM'. intros.
     assert (stk' = SSAsm.stkblock).
     exploit Mem.alloc_result. eapply H0.
     unfold Mem.nextblock. unfold Mem.fresh_block. rewrite H3.
     simpl. intros. rewrite H5. unfold SSAsm.stkblock. auto.
     (* prove stk' in support m2 *)
     rewrite <- H5.
     exploit Mem.support_storev. apply H1. intros.
     rewrite <- H6. unfold Mem.flat_inj.
     destruct Mem.sup_dec. eauto.
     congruence.
     rewrite Ptrofs.add_zero. auto.
     (* glob block valid *)
     
     unfold glob_block_valid. intros.
     exploit (Genv.find_def_not_fresh). apply H. apply H3.
     unfold Mem.valid_block. intros.
     exploit Mem.support_alloc. apply H0. 
     exploit Mem.support_storev. apply H1.
     intros. rewrite <- H5. rewrite H6.
     exploit Mem.sup_include_incr. apply H4. auto.
Qed.


(** ** Simulation of Single Step Execution *)

Lemma eval_builtin_arg_inject : forall j m m' rs rs' sp sp' arg varg
    (MATCHINJ: match_inj j)                              
    (MINJ: magree j m m')
    (RSINJ: regset_inject j rs rs')
    (VINJ: Val.inject j sp sp')
    (EVALBI: Events.eval_builtin_arg ge rs sp m arg varg),
    exists varg', eval_builtin_arg _ tge rs' sp' m' arg varg' /\
             Val.inject j varg varg'.
Proof.
  unfold regset_inject.
  induction arg; intros; inv EVALBI.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - eexists; split; auto. constructor.
  - exploit loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & ML & VJ); auto.
    eexists; split. constructor. apply ML. auto.
  - eexists; split. constructor.
    apply Val.offset_ptr_inject; eauto.
  - exploit loadv_inject; eauto.
    apply symbol_address_inject; eauto.
    intros (v2 & ML & VJ); auto.
    eexists; split. constructor. apply ML. auto.
  - eexists; split. constructor.
    apply symbol_address_inject; eauto.
  - exploit IHarg1; eauto.
    intros (varg1 & EVALBI1 & JB1).
    exploit IHarg2; eauto.
    intros (varg2 & EVALBI2 & JB2).
    eexists; split. constructor; eauto.
    apply Val.longofwords_inject; auto.
  - exploit IHarg1; eauto.
    intros (varg1 & EVALBI1 & JB1).
    exploit IHarg2; eauto.
    intros (varg2 & EVALBI2 & JB2).
    destruct Archi.ptr64 eqn: PTR.
    eexists; split. econstructor;eauto.
    rewrite PTR. eapply Val.addl_inject;auto.
    eexists; split. econstructor;eauto.
    rewrite PTR. eapply Val.add_inject;auto.
Qed.


Lemma eval_builtin_args_inject : forall j m m' rs rs' sp sp' args vargs
    (MATCHINJ: match_inj j)
    (MINJ: magree j m m')
    (RSINJ: regset_inject j rs rs')
    (VINJ: Val.inject j sp sp')
    (EVALBI: Events.eval_builtin_args ge rs sp m args vargs),
    exists vargs', eval_builtin_args _ tge rs' sp' m' args vargs' /\
             Val.inject_list j vargs vargs'.
Proof.
  induction args; intros; simpl; inv EVALBI.
  - eexists. split. constructor. auto.
  - exploit eval_builtin_arg_inject; eauto.
    intros (varg' & EVARG & JB).
    exploit IHargs; eauto.
    intros (vargs' & EVARGS & JBS).
    exists (varg' :: vargs'). split; auto.
    unfold eval_builtin_args.
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arg_inject : forall rs1 rs2 m1 m2 l arg1 j,
    extcall_arg rs1 m1 l arg1 ->
    magree j m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg rs2 m2 l arg2.
Proof.
  intros. inv H.
  - unfold regset_inject in *.
    specialize (H1 (Asm.preg_of r)). eexists; split; eauto.
    constructor.
  - exploit loadv_inject; eauto.
    apply Val.offset_ptr_inject. apply H1.
    intros (arg2 & MLOADV & ARGINJ).
    exists arg2. split; auto.
    eapply extcall_arg_stack; eauto.
Qed.

    
Lemma extcall_arg_pair_inject : forall rs1 rs2 m1 m2 lp arg1 j,
    extcall_arg_pair rs1 m1 lp arg1 ->
    magree j m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg_pair rs2 m2 lp arg2.
Proof.
  intros. inv H.
  - exploit extcall_arg_inject; eauto.
    intros (arg2 & VINJ & EXTCALL).
    exists arg2. split; auto. constructor. auto.
  - exploit (extcall_arg_inject rs1 rs2 m1 m2 hi vhi); eauto.
    intros (arghi & VINJHI & EXTCALLHI).
    exploit (extcall_arg_inject rs1 rs2 m1 m2 lo vlo); eauto.
    intros (arglo & VINJLO & EXTCALLLO).
    exists (Val.longofwords arghi arglo). split.
    + apply Val.longofwords_inject; auto.
    + constructor; auto.
Qed.

Lemma extcall_arguments_inject_aux : forall rs1 rs2 m1 m2 locs args1 j,
   list_forall2 (extcall_arg_pair rs1 m1) locs args1 ->
    magree j m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      list_forall2 (extcall_arg_pair rs2 m2) locs args2.
Proof.
  induction locs; simpl; intros; inv H.
  - exists nil. split.
    + apply Val.inject_list_nil.
    + unfold Asm.extcall_arguments. apply list_forall2_nil.
  - exploit extcall_arg_pair_inject; eauto.
    intros (arg2 & VINJARG2 & EXTCALLARG2).
    exploit IHlocs; eauto.
    intros (args2 & VINJARGS2 & EXTCALLARGS2).
    exists (arg2 :: args2). split; auto.
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arguments_inject : forall rs1 rs2 m1 m2 ef args1 j,
    Asm.extcall_arguments rs1 m1 (ef_sig ef) args1 ->
    magree j m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      Asm.extcall_arguments rs2 m2 (ef_sig ef) args2.
Proof.
  unfold Asm.extcall_arguments. intros.
  eapply extcall_arguments_inject_aux; eauto.
Qed.

(* copy from LocalLib *)
Lemma inject_decr : forall b j j' m1 m2 b' ofs,
  Mem.valid_block m1 b -> inject_incr j j' -> inject_separated j j' m1 m2 ->
  j' b = Some (b', ofs) -> j b = Some (b', ofs).
Proof.
  intros. destruct (j b) eqn:JB.
  - unfold inject_incr in *. destruct p. exploit H0; eauto.
    intros. congruence.
  - unfold inject_separated in *. exploit H1; eauto.
    intros (NVALID1 & NVALID2). congruence.
Qed.
(* End of copy *)

Lemma inject_pres_match_sminj :
  forall j j' m1 m2 (ms: match_inj j),
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 ->
    match_inj j'.
Proof.
  unfold glob_block_valid.
  intros. inversion ms. constructor; intros.
  -
    eapply (agree_inj_instrs0 b b'); eauto.
    unfold Globalenvs.Genv.find_funct_ptr in H2. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
  -
    exploit agree_inj_globs0; eauto.
    intros (b' & ofs' & GLBL & JB).
    eexists; eexists; eexists; eauto.
  -
    eapply (agree_inj_ext_funct0 b); eauto.
    unfold Globalenvs.Genv.find_funct_ptr in H2. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
  -
    eapply (agree_inj_int_funct0 b); eauto.
    unfold Globalenvs.Genv.find_funct_ptr in H2. destruct (Globalenvs.Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
Qed.


Lemma inject_symbol_address : forall j id ofs,
    match_inj j ->
    Val.inject j (Globalenvs.Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  unfold Globalenvs.Genv.symbol_address.
  intros.
  destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
  inv H. exploit agree_inj_globs0; eauto.
  intros (b' & ofs' & SBOFS & JB).
  erewrite Genv.symbol_address_offset; eauto. 
  eapply Val.inject_ptr; eauto.
  rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_commut.
  unfold Genv.symbol_address. rewrite SBOFS.
  rewrite Ptrofs.add_zero_l. auto.
Qed.


Ltac simpl_goal :=
  repeat match goal with
         | [ |- context [ Int.add Int.zero _ ] ] =>
           rewrite Int.add_zero_l
         | [ |- context [ Int64.add Int64.zero _ ] ] =>
           rewrite Int64.add_zero_l
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int Int.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int64 Int64.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add Ptrofs.zero _] ] =>
           rewrite Ptrofs.add_zero_l
         | [ |- context [Ptrofs.repr (Ptrofs.unsigned _)] ] =>
           rewrite Ptrofs.repr_unsigned
         end.

Ltac destr_pair_if :=
  repeat match goal with
         | [ |- context [match ?a with pair _ _ => _ end] ] =>
           destruct a eqn:?
         | [ |- context [if ?h then _ else _] ] =>
           destruct h eqn:?
         end.

Ltac inject_match :=
  match goal with
  | [ |- Val.inject ?j (match ?a with _ => _ end) (match ?b with _ => _ end) ] =>
    assert (Val.inject j a b)
  end.

Ltac inv_valinj :=
  match goal with
         | [ H : Val.inject _ (Vint _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vlong _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vptr _ _) _ |- _ ] =>
           inversion H; subst
         end.

Ltac destr_valinj_right H :=
  match type of H with
  | Val.inject _ _ ?a =>
    destruct a eqn:?
  end.

Ltac destr_valinj_left H :=
  match type of H with
  | Val.inject _ ?a ?b =>
    destruct a eqn:?
  end.

Remark mul_inject:
  forall f v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mul v1 v2) (Val.mul v1' v2').
Proof.
  intros.
  unfold Val.mul. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.


Lemma eval_addrmode32_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode32 ge a rs1) (eval_addrmode32 tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode32, eval_addrmode32.
  destruct a. 
  destruct base, ofs, const; simpl in *. 
  - destruct p. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
  - destruct p,p0. repeat apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. apply Val.add_inject; auto. 
    inject_match. apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.
    (* 32bit need the following proof *)
    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if. auto. *)
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.

    destr_valinj_left H1; inv H1; auto.
    (* destr_pair_if. auto. *)
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - destruct p,p0.
    inject_match.
    apply Val.add_inject; auto.
    destr_pair_if; auto.
    apply mul_inject; auto.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    destr_valinj_left H1; inv H1; auto.

    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.
  - repeat apply Val.add_inject; auto.
  - destruct p. 
    inject_match. inject_match.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.    
    destr_valinj_left H1;inv H1; auto.

    destr_valinj_left H1;inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.

    destruct Archi.ptr64 eqn:PTR.    
    destr_valinj_left H1; inv H1; auto.
    destr_valinj_left H1; inv H1; auto.
    destr_pair_if. auto.
    eapply Val.inject_ptr; eauto.
    repeat unfold Ptrofs.of_int.
    repeat rewrite Int.unsigned_zero.
    repeat rewrite Ptrofs.add_zero. auto.   

        
Qed.

    (* destr_pair_if. auto. *)
    (* eapply Val.inject_ptr; eauto. *)
    (* repeat unfold Ptrofs.of_int.  *)
    (* repeat rewrite Int.unsigned_zero.  *)
    (* repeat rewrite Ptrofs.add_zero. auto. *)
    (* destr_valinj_left H1; inv H1; auto. *)
    (* destr_pair_if. auto. *)
    (* eapply Val.inject_ptr; eauto. *)
    (* repeat unfold Ptrofs.of_int.  *)
    (* repeat rewrite Int.unsigned_zero.  *)
    (* repeat rewrite Ptrofs.add_zero. auto. *)   

Lemma eval_addrmode64_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode64 ge a rs1) (eval_addrmode64 tge a rs2).
Proof.
  intros. 
  destruct a. 
  destruct base, ofs, const; simpl in *.
  - destruct p. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.

    apply Val.mull_inject; auto.
  - destruct p,p0. repeat apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    apply inject_symbol_address. auto.
  - repeat apply Val.addl_inject; auto.
  - destruct p. apply Val.addl_inject; auto.
    inject_match.
    (* dependent in ptr64 !! try to fix it !!!*)
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - destruct p.
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - destruct p,p0.
    inject_match.
    apply Val.addl_inject; auto.
    destr_pair_if; auto.
    apply Val.mull_inject; auto.
    apply inject_symbol_address; auto.
    destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
  - repeat apply Val.addl_inject; auto.
  - destruct p. inject_match. inject_match.
    apply inject_symbol_address; auto.
    * destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
    *  destruct Archi.ptr64 eqn:PTR.
    (* 64 *)
    + destr_valinj_left H1; inv H1;eauto.
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 Int64.zero)). auto.
    + destr_valinj_left H1; inv H1;eauto.
Qed.

Lemma eval_addrmode_inject: forall j a rs1 rs2,
    match_inj j ->
    regset_inject j rs1 rs2 ->
    Val.inject j (Asm.eval_addrmode ge a rs1) (eval_addrmode tge a rs2).
Proof.
  intros. unfold Asm.eval_addrmode, eval_addrmode. destruct Archi.ptr64.
  + eapply eval_addrmode64_inject; eauto.
  + eapply eval_addrmode32_inject; eauto.
Qed.


Lemma exec_load_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk rd a
                          (INJ: j = Mem.flat_inj (Mem.support m1))
                          (MINJ: magree j  m1 m2)
                          (MATCHINJ: match_inj j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1), 
    Asm.exec_load ge sz chunk m1 a rs1 rd = Next rs1' m1' ->
    exists rs2' m2',
      exec_load sz tge chunk m2 a rs2 rd = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.loadv chunk m1 (Asm.eval_addrmode ge a rs1)) eqn:MLOAD; try congruence.
  exploit loadv_inject; eauto. intros (v2 & MLOADV & VINJ).
  eexists. eexists. split.
  - unfold exec_load. rewrite MLOADV. auto.
  - inv H. eapply match_states_intro; eauto.
    apply nextinstr_pres_inject.
    apply undef_regs_pres_inject.
    apply regset_inject_expand; eauto.
Qed.


Lemma store_pres_glob_block_valid : forall m1 chunk b v ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma storev_pres_glob_block_valid : forall m1 chunk ptr v m2,
  Mem.storev chunk m1 ptr v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold Mem.storev. intros. destruct ptr; try congruence.
  eapply store_pres_glob_block_valid; eauto.
Qed.

Lemma exec_store_step: forall j rs1 rs2 m1 m2 rs1' m1' sz chunk r a dregs
                         (INJ: j = Mem.flat_inj (Mem.support m1))
                         (MINJ: magree j m1 m2)
                         (MATCHINJ: match_inj j)
                         (RSINJ: regset_inject j rs1 rs2)
                         (GBVALID: glob_block_valid m1),
    Asm.exec_store ge sz chunk m1 a rs1 r dregs = Next rs1' m1' ->
    exists rs2' m2',
      exec_store sz tge chunk m2 a rs2 r dregs = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.
  exploit eval_addrmode_inject; eauto. intro EMODINJ.
  destruct (Mem.storev chunk m1 (Asm.eval_addrmode ge a rs1) (rs1 r)) eqn:MSTORE; try congruence.
  exploit storev_mapped_inject; eauto. intros (m2' & MSTOREV & MINJ').
  exploit (Mem.support_storev). apply MSTORE. intros SUP.
  eexists. eexists. split.
  - unfold exec_store. rewrite MSTOREV. auto.
  - inv H. eapply match_states_intro; eauto.
    rewrite <- SUP. auto.
    rewrite <- SUP. auto.
    (* erewrite <- storev_pres_def_frame_inj; eauto. *)
    apply nextinstr_pres_inject. repeat apply undef_regs_pres_inject.
    rewrite <- SUP. auto.
    eapply storev_pres_glob_block_valid; eauto.
Qed.

Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    Val.opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.



Hint Resolve nextinstr_nf_pres_inject nextinstr_pres_inject regset_inject_expand
  regset_inject_expand_vundef_left undef_regs_pres_inject
  Val.zero_ext_inject Val.sign_ext_inject Val.longofintu_inject Val.longofint_inject
  Val.singleoffloat_inject Val.loword_inject Val.floatofsingle_inject Val.intoffloat_inject Val.maketotal_inject
  Val.intoffloat_inject Val.floatofint_inject Val.intofsingle_inject Val.singleofint_inject
  Val.longoffloat_inject Val.floatoflong_inject Val.longofsingle_inject Val.singleoflong_inject
  eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject
  Val.neg_inject Val.negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject Val.mul_inject Val.mull_inject Val.mulhs_inject Val.mulhu_inject
  Val.mullhs_inject Val.mullhu_inject Val.shr_inject Val.shrl_inject Val.or_inject Val.orl_inject
  Val.xor_inject Val.xorl_inject Val.and_inject Val.andl_inject Val.notl_inject
  Val.shl_inject Val.shll_inject Val.vzero_inject Val.notint_inject
  Val.shru_inject Val.shrlu_inject Val.ror_inject Val.rorl_inject
  compare_ints_inject compare_longs_inject compare_floats_inject compare_floats32_inject
  Val.addf_inject Val.subf_inject Val.mulf_inject Val.divf_inject Val.negf_inject Val.absf_inject
  Val.addfs_inject Val.subfs_inject Val.mulfs_inject Val.divfs_inject Val.negfs_inject Val.absfs_inject
  val_of_optbool_lessdef eval_testcond_inject Val.offset_ptr_inject: inject_db.

Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
    reflexivity
  | [ |- context [eval_testcond _ _] ]=>
    unfold eval_testcond; solve_exec_instr
  | [ H: Asm.eval_testcond ?c ?r = _ |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite H; solve_exec_instr
  | [ H: _ = Asm.eval_testcond ?c ?r |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite <- H; solve_exec_instr
  end.

Ltac solve_match_states :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ |- exists _, _ ] => eexists; solve_match_states
  | [ |- Next _ _ = Next _ _ /\ match_states _ _ ] =>
    split; [reflexivity | econstructor; eauto; solve_match_states]
  | [ |- (exec_instr _ _ _ _ = Next _ _) /\ match_states _ _ ] =>
    split; [simpl; solve_exec_instr | econstructor; eauto; solve_match_states]
  | [ |- regset_inject _ _ _ ] =>
    eauto 10 with inject_db
  end.

Ltac destr_eval_testcond :=
  match goal with
  | [ H : match Asm.eval_testcond ?c ?rs with | _ => _ end = Next _ _ |- _ ] =>
    let ETEQ := fresh "ETEQ" in (
      destruct (Asm.eval_testcond c rs) eqn:ETEQ); destr_eval_testcond
  | [ H : Some ?b = Asm.eval_testcond _ _ |- _ ] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.eval_testcond _ _ = Some ?b |- _] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.Next _ _ = Next _ _ |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some true) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: Val.opt_lessdef (Some false) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | _ => idtac
  end.

Ltac destr_match_outcome :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ H: Asm.Next _ _ = Next _ _ |- _ ] => inv H; destr_match_outcome
  | [ H: match ?a with _ => _ end = Next _ _ |- _] =>
    let EQ := fresh "EQ" in (destruct a eqn:EQ; destr_match_outcome)
  | _ => idtac
  end.


Lemma goto_ofs_pres_mem : forall f l rs1 m1 rs1' m1',
    Asm.goto_ofs ge f l rs1 m1 = Next rs1' m1' -> m1 = m1'.
Proof.
  unfold Asm.goto_label. intros.
  unfold Asm.goto_ofs in H. 
  repeat destr_in H.
Qed.

Lemma goto_ofs_inject : forall rs1 rs2 f l j m1 m2 rs1' m1'
                            (RINJ: regset_inject j rs1 rs2),
    Asm.goto_ofs ge f l rs1 m1 = Next rs1' m1' ->
    exists rs2', goto_ofs f l rs2 m2 = Next rs2' m2 /\
            regset_inject j rs1' rs2'.
Proof.
  intros. unfold Asm.goto_ofs in H.
  destr_in H. destr_in H. inv H.
  unfold goto_ofs.
  generalize (RINJ PC). rewrite Heqv.
  intros NJ. inv NJ.
  eexists; split; eauto.
  apply regset_inject_expand; auto.
  eapply Val.inject_ptr; eauto.
  repeat rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut.
  repeat rewrite Ptrofs.add_assoc.
  auto.
Qed.

Lemma goto_ofs_inject' : forall l f j rs1 rs2 m1 m2 rs1' m1'
                                (RINJ: regset_inject j rs1 rs2),
    Asm.goto_ofs ge f l ((rs1 # RAX <- Vundef) # RDX <- Vundef) m1 = Next rs1' m1' ->
    exists rs2',
      goto_ofs f l ((rs2 # RAX <- Vundef) # RDX <- Vundef) m2 = Next rs2' m2 /\
      regset_inject j rs1' rs2'.
Proof.
  intros. 
  eapply goto_ofs_inject; eauto.
  repeat apply regset_inject_expand; auto.
Qed.

Lemma extcall_pres_glob_block_valid : forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply external_call_valid_block; eauto.
Qed.

(* TODO: it is architechture specific, we should move it to architechture directory *)
(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' i ofs f b
                        (INJ : j = Mem.flat_inj (Mem.support m1))
                        (MINJ: magree j m1 m2)
                        (MATCHSMINJ: match_inj j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1),
    rs1 PC = Vptr b ofs ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr instr_size (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RealAsm.exec_instr instr_size ge f i rs1 m1 = Next rs1' m1' ->
    exists rs2' m2',
      exec_instr instr_size tge i rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.

  intros.
  destruct i; inv H2; simpl in *;
    try first [solve_store_load |
               solve_match_states].

  - (* Pmov_rs *)
    apply nextinstr_nf_pres_inject.
    apply regset_inject_expand; auto.
    inv MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address.
    destruct (Globalenvs.Genv.find_symbol ge id) eqn:FINDSYM; auto.
    exploit agree_inj_globs0; eauto.
    intros (b1 & ofs1 & GLBL & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  (* Divisions *)
  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - destr_match_outcome.
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.
     
  - (* Pcmov *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1')) c rs1 rs2); eauto.
    intros. inv H2.
    destr_eval_testcond; try solve_match_states.
    (* destruct (Asm.eval_testcond c rs2) eqn:EQ'. destruct b0; solve_match_states. *)
    (* solve_match_states. *)
    destruct v;solve_match_states.
    
    
  - (* Pjmp_l *)
    assert (instr_valid (Pjmp_l l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pjmp_s *)
    repeat destr_in H4.    
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ.
    unfold Globalenvs.Genv.symbol_address. destr_match; auto.
    exploit (agree_inj_globs0 symb b0); eauto.
    intros (b1 & ofs1 & LBLOFS & JB).
    erewrite Genv.find_sym_to_addr with (ofs:=ofs1); eauto.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  - (* Pjmp_r *)
    repeat destr_in H4.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
      
  - (* Pjcc *)
    assert (instr_valid (Pjcc c l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
    
  - (* Pjcc2 *)
    assert (instr_valid (Pjcc2 c1 c2 l)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pjmptbl *)
    assert (instr_valid (Pjmptbl r tbl)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pcall_s *)
    repeat destr_in H4.
    generalize (RSINJ PC).
    (* support after storev *)
    exploit (Mem.support_storev). eapply Heqo. intros SUPEQ.
    rewrite SUPEQ in *.
    edestruct storev_mapped_inject as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    (* destruct ros; simpl; repeat apply regset_inject_expand; auto. *)
    exploit (inject_symbol_address). eapply MATCHSMINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.
    
  - (* Pcall_r *)
    repeat destr_in H4.
    generalize (RSINJ PC).
    (* support after storev *)
    exploit (Mem.support_storev). eapply Heqo. intros SUPEQ.
    rewrite SUPEQ in *.
    edestruct storev_mapped_inject as (m2' & ST & MINJ'). apply MINJ. eauto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    do 2 eexists; split; eauto. simpl.
    rewrite ST. eauto.
    econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    apply Val.offset_ptr_inject. eauto.
    apply Val.offset_ptr_inject. eauto.
    eapply storev_pres_glob_block_valid; eauto.
    
  - (* Pret *)
    repeat destr_in H4. simpl.
    unfold loadvv in *. destr_in Heqo. 
    exploit loadv_inject;eauto. intros (v2 & LD & VI). rewrite LD.
    destr_in Heqo;inv Heqo;inv VI;
    eexists _, _; split; eauto;
    econstructor; eauto;
    repeat apply regset_inject_expand; auto;
    try apply Val.offset_ptr_inject; eauto.
    
  - (* Pallocframe *)
    assert (instr_valid (Pallocframe sz ofs_ra ofs_link)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.

  - (* Pfreeframe *)
    assert (instr_valid (Pfreeframe sz ofs_ra ofs_link)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
    
  - (* Pjmp_l_rel *)
    unfold Asm.goto_ofs in H4.
    destruct (rs1 Asm.PC) eqn:PC1; inv H4.
    destruct (Globalenvs.Genv.find_funct_ptr ge b0); inv H3.
    generalize (RSINJ PC). rewrite PC1.
    intros INJ. inv INJ. eauto.
    eexists; eexists. split.
    unfold goto_ofs.
    rewrite <- H4. eauto.
    eapply match_states_intro; eauto.
    apply regset_inject_expand; auto.
    rewrite H in *. inv PC1. inv H.
    eapply Val.inject_ptr; eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    match goal with
    | [ |- _ = Ptrofs.add _ (Ptrofs.add ?b ?c) ] =>
      rewrite (Ptrofs.add_commut b c)
    end.
    match goal with
    | [ |- _ = Ptrofs.add ?a ?b ] =>
      rewrite (Ptrofs.add_commut a b)
    end.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    
  - (* Pjcc_rel *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_ofs_pres_mem; eauto. intros. subst.
    generalize (goto_ofs_inject _ _ _ _ _ m1' m2 _ _ RSINJ H4).
    intros (rs2' & GOTO & RINJ').
    exists rs2', m2. split; auto.
    eapply match_states_intro; eauto.

  - (* Pjcc2_rel *)
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c1 rs1 rs2); eauto.
    exploit (eval_testcond_inject (Mem.flat_inj (Mem.support m1)) c2 rs1 rs2); eauto.
    intros ELF1 ELF2.
    destr_eval_testcond; try solve_match_states.
    exploit goto_ofs_pres_mem; eauto. intros. subst.
    generalize (goto_ofs_inject _ _ _ _ _ m1' m2 _ _ RSINJ H4).
    intros (rs2' & GOTO & RINJ').
    exists rs2', m2. split; auto.
    eapply match_states_intro; eauto.

  - (* Pjmptbl_rel *)
    assert (instr_valid (Pjmptbl_rel r tbl)) as NJ.
    { eapply instr_is_valid; eauto. }
    red in NJ. cbn in NJ. contradiction.
(***** Remove Proofs By Chris Start ******)
(*       *)
(*     destruct (rs1 r) eqn:REQ; inv H4. *)
(*     destruct (list_nth_z tbl (Int.unsigned i)) eqn:LEQ; inv H3. *)
(*     assert (rs2 r = Vint i) by *)
(*         (generalize (RSINJ r); rewrite REQ; inversion 1; auto). *)
(*     exploit goto_ofs_pres_mem; eauto. intros. subst. *)
(*     generalize (goto_ofs_inject' _ _ _ _ _ m1' m2 _ _ RSINJ H4). *)
(*     intros (rs2' & GLBL & RSINJ'). *)
(*     exists rs2', m2. rewrite H2. rewrite LEQ. *)
(*     split; auto. *)
(*     eapply match_states_intro; eauto. *)
(* *)
(***** Remove Proofs By Chris End ******)
Qed.

(* copy from SSAsmproof.v *)
Lemma val_inject_undef_caller_save_regs:
  forall j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    r,
    Val.inject j (undef_caller_save_regs rs1 r) (undef_caller_save_regs rs2 r).
Proof.
  intros; eauto.
  unfold undef_caller_save_regs.
  destruct (preg_eq r SP); destruct (in_dec preg_eq r (map preg_of (filter Conventions1.is_callee_save Machregs.all_mregs))); simpl; try (apply RINJ).
  eauto.
Qed.


Theorem step_simulation:
  forall S1 t S2,
    RealAsm.step instr_size ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      step instr_size tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_inj_instrs (Mem.flat_inj (Mem.support m)) MATCHINJ b b2 f ofs delta i); eauto.
    intros FIND.
    exploit (exec_instr_step (Mem.flat_inj (Mem.support m)) rs rs'0 m m'0 rs' m' i); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply exec_step_internal; eauto.
    eapply (agree_inj_int_funct (Mem.flat_inj (Mem.support m)) MATCHINJ); eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_inj_instrs (Mem.flat_inj (Mem.support m)) MATCHINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros FIND.
    exploit (eval_builtin_args_inject (Mem.flat_inj (Mem.support m)) m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    exploit (external_call_inject ge (Mem.flat_inj (Mem.support m)) vargs vargs' m m'0 m' vres t ef);eauto.
    rewrite SENVEQ.
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP & INJ).
    set (rs' := nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                             (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0))).
    exploit (fun b ofs => exec_step_builtin instr_size tge b ofs
                                         ef args res rs'0  m'0 vargs' t vres2 rs' m2'); eauto. 
    eapply (agree_inj_int_funct (Mem.flat_inj (Mem.support m)) MATCHINJ); eauto.
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj (Mem.flat_inj (Mem.support m))); eauto.
    + subst rs'. intros. 
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (fun h => set_res_pres_inject res j' 
                  rs1 rs2 h vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      eapply nextinstr_nf_pres_inject. auto.
      (* eauto with inject_db. *)
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    exploit loadv_inject. apply MINJ. apply LOADRA. eauto. intros (v2 & LRA & VI).
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    apply regset_inject_expand. eauto.
    apply Val.offset_ptr_inject. eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { eapply transf_prog_pres_senv; eauto. }
    exploit (external_call_inject ge (Mem.flat_inj (Mem.support m)) args args2 ); eauto.
    rewrite SENVEQ.
    
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP & INJ).
    exploit (fun ofs => exec_step_external instr_size tge b2 ofs ef args2 res'); eauto.
    eapply agree_inj_ext_funct; eauto.
    + intro; subst. inv VI. congruence.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj (Mem.flat_inj (Mem.support m))); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        (* set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *. *)
        (* generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros. *)
        (* set (rs1 := (Asm.undef_regs dregs rs)) in *. *)
        (* set (rs2 := (Asm.undef_regs dregs rs'0)) in *. *)
        (* set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *. *)
        (* generalize (undef_regs_pres_inject j' rs1 rs2 cdregs). intros. *)
        (* set (rs3 := (Asm.undef_regs cdregs rs1)) in *. *)
        (* set (rs4 := (Asm.undef_regs cdregs rs2)) in *. *)
        (* generalize (set_pair_pres_inject j' rs3 rs4 res res'  *)
        (*                                  (Asm.loc_external_result (ef_sig ef))). *)
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
        eapply set_pair_pres_inject.
        unfold regset_inject.
        eapply val_inject_undef_caller_save_regs.
        auto. auto.
        eapply val_inject_incr; eauto.
        apply Val.offset_ptr_inject; eauto.
      * eapply extcall_pres_glob_block_valid; eauto.
Qed.


(** ** Matching of the Final States*)
Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.

(** ** The Main Correctness Theorem *)
Lemma transf_program_correct:
  forward_simulation (RealAsm.semantics instr_size prog) 
                     (semantics instr_size tprog (Pregmap.init Vundef)).
Proof.
  intros. apply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF. cbn.
    auto.
    (* rewrite add_external_globals_pres_senv. cbn. auto. *)
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    (* intros. *)
    (* rewrite Pregmap.gi. auto. *)
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.

Instance symbtablegen_transflink (instr_size: instruction -> Z):
  TransfLink (match_prog instr_size).
Admitted.
