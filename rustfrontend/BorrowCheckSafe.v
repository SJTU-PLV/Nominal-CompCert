Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface Invariant.
Require Import Rusttypes RustlightBase.
Require Import RustIR BorrowCheckDomain BorrowCheckPolonius.

(* move to rustlight  *)
Definition is_owned (p: place) (own: own_env) : bool :=
  match own ! (local_of_place p) with
  | Some l =>
      (** FIXME: consider partial ownership! *)
      in_dec place_eq p l             
  | None => false
  end.

Definition scalar_type (ty: type) : bool :=
  match ty with
  | Tunit
  | Tint _ _
  | Tlong _
  | Tfloat _
  | Tfunction _ _ _ _ _
  | Tarray _ _ => true
  | _ => false
  end.

(* relation between the selector and the (stmt, cont) pair *)
Inductive match_instr_stmt (body: statement) : instruction -> statement -> cont -> Prop :=
| sel_stmt_base: forall sel n s k,
    select_stmt body sel = Some s ->
    match_instr_stmt body (Isel sel n) s k
| sel_stmt_seq: forall sel n s1 s2 k,
    match_instr_stmt body (Isel sel n) s1 (Kseq s2 k) ->
    match_instr_stmt body (Isel sel n) (Ssequence s1 s2) k
| sel_stmt_kseq: forall sel n s k,
    match_instr_stmt body (Isel sel n) s k ->
    match_instr_stmt body (Isel sel n) Sskip (Kseq s k)
| sel_stmt_ifthenelse: forall e n1 n2 s1 s2 k,
    match_instr_stmt body (Icond e n1 n2) (Sifthenelse e s1 s2) k
| sel_stmt_loop: forall n s k,    
    match_instr_stmt body (Inop n) (Sloop s) k
| sel_stmt_break: forall n k,    
    match_instr_stmt body (Inop n) Sbreak k
| sel_stmt_continue: forall n k,
    match_instr_stmt body (Inop n) Scontinue k
.

(** Definition of abstracter which maps a memory location to place
(i.e. the owner of this location) *)

Definition mem_abstracter : Type := block -> Z -> option (place * Z).

Section MATCH.

Variable ce: composite_env.
Variable abs: mem_abstracter.


(* The value stored in m[b, ofs] is consistent with the type of p *)
Inductive bmatch (m: mem) (b: block) (ofs: Z) (p: place) (own: own_env) : type -> Prop :=
| bm_box: forall ty b1 ofs1
    (* valid resource. If the loaded value is not a pointer, it is a
    type error instead of a memory error *)
    (VRES: Mem.load Mptr m b ofs = Some (Vptr b1 ofs1) ->
           (abs b1 (Ptrofs.unsigned ofs1) = Some (Pderef p ty, 0) <-> is_owned p own = true)),
    bmatch m b ofs p own (Tbox ty)
| bm_struct: forall orgs id
    (* all fields in the struct satisfy bmatch *)
    (FMATCH: forall co fid fty fofs bf,
        ce ! id = Some co ->
        In (Member_plain fid fty) co.(co_members) ->       
        field_offset ce fid co.(co_members) = OK (fofs, bf) ->
        bmatch m b (ofs + fofs) (Pfield p fid fty) own fty),
    bmatch m b ofs p own (Tstruct orgs id)
| bm_enum: forall orgs id
    (FMATCH: forall co fid fty fofs bf tag,
        ce ! id = Some co ->
        (* load tag *)
        Mem.load Mint32 m b ofs = Some (Vint tag) ->
        list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
        variant_field_offset ce fid (co_members co) = OK (fofs, bf) ->        
        bmatch m b (ofs + fofs) (Pdowncast p fid fty) own fty),
    bmatch m b ofs p own (Tvariant orgs id)
| bm_scalar: forall ty,
    scalar_type ty = true ->
    bmatch m b ofs p own ty
(** TODO: bm_reference  *)
.
  

Definition mmatch (m: mem) (own: own_env) : Prop :=
  forall b ofs p pofs,
    abs b ofs = Some (p, pofs) ->
    (** TODO: how to represent the align_chunk property in
    valid_access ? I think the permission depends on the type of p *)
    (** p may be an enum whose body has been moved, but its tag is
    still owned by p? *)
    (Mem.range_perm m b (ofs - pofs) (ofs - pofs + (sizeof ce (typeof_place p))) Cur Freeable
    /\ bmatch m b (ofs - pofs) p own (typeof_place p)).


End MATCH.



Section BORCHK.

Variable p: program.
Variable w: inv_world wt_c.
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program p) se.
Hypothesis INV: symtbl_inv wt_c w se.
Let L := semantics p se.
Let ge := globalenv se p.

(* composite environment *)
Let ce := ge.(genv_cenv).


Inductive sound_state: state -> Prop :=
| sound_regular_state: forall
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (INSTR: cfg ! pc = Some instr)
    (MSTMT: match_instr_stmt f.(fn_body) instr s k)
    (CHK: borrow_check ce f = OK ae)
    (AS: ae ! pc = Some (AE.State Σ Γ Δ))
    
    sound_state (State f s k e m)
  

  

Lemma sound_state_no_mem_error: forall s,
    step_mem_error ge s -> sound_state s -> False .
Admitted.

Lemma initial_state_sound: forall q s,
    Smallstep.initial_state L q s ->
    sound_state s.
Admitted.

Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    Step L s1 t s2 ->
    (* how to prove sound_state in dropstate? *)
    sound_state s2.
Admitted.


Lemma reachable_state_sound: forall s,
    (* What about after external? *)
    reachable L s -> sound_state s.
Admitted.


(** Specific definition of partial safe *)
Definition partial_safe (s: state) : Prop :=
  safe L s \/ step_mem_error ge s.

Lemma borrow_check_lts_safe:
    borrow_check_program p = OK tt ->
    lts_safe se (semantics p se) wt_c wt_c (fun _ => partial_safe) w ->
    lts_safe se (semantics p se) wt_c wt_c safe w.
Proof.
  intros BORCHK PSAFE. inv PSAFE.  
  constructor.
  - intros s t s' REACH STEP.
    generalize (step_safe _ _ _ REACH STEP). intros PSAFE.
    destruct PSAFE as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply reachable_state_sound. eapply step_reachable; eauto.
  (* initial_progress *)
  - eauto.
  (* initial_safe *)
  - intros q s INIT.
    generalize (initial_safe _ _ INIT). intros PSAFE.
    destruct PSAFE as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply initial_state_sound; eauto.
  (* external_safe *)
  - intros s q REACH EXT.
    generalize (external_safe _ _ REACH EXT).
    intros (wA & SYMBINV & VQ & AFTEREXT).
    exists wA. split; auto. split; auto.
    intros r VR. generalize (AFTEREXT _ VR).
    intros ((s' & AFTER) & PSAFE).
    split. exists s'. eauto.
    intros s'' AFTER1.
    generalize (PSAFE s'' AFTER1). intros PSAFE1.
    destruct PSAFE1 as [|MEMERROR]. auto.
    exfalso. eapply sound_state_no_mem_error. eauto.
    eapply reachable_state_sound. eapply external_reach; eauto.
    eapply star_refl.
  - eauto.
Qed.    
    
End BORCHK.



(* Lemma borrow_check_safe: forall p, *)
(*     borrow_check_program p = OK tt -> *)
(*     module_safe (semantics p) wt_c wt_c partial_safe -> *)
(*     module_safe (semantics p) wt_c wt_c safe. *)
(* Proof. *)
(*   intros p BORCHK MSAFE. *)
(*   red. intros w se VALIDSE SYMBINV. *)
(* Admitted. *)
    
