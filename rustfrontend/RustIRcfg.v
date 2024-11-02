Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight Rustlight Rustlightown.
Require Import InitDomain RustIR.
Require Import Sorting.Permutation.


Import ListNotations.

(** ** Definition of selector. It is the program pointer in AST-like 
program.  *)

Inductive select_kind : Type :=
| Selseqleft: select_kind
| Selseqright: select_kind
| Selifthen: select_kind
| Selifelse: select_kind
| Selloop: select_kind.

Definition selector := list select_kind.

Inductive selector_disjoint : selector -> selector -> Prop :=
| sel_disjoint_neq: forall s1 s2 l1 l2,
    s1 <> s2 ->
    selector_disjoint (s1::l1) (s2::l2)
| sel_disjoint_cons: forall s l1 l2,
    selector_disjoint l1 l2 ->
    selector_disjoint (s::l1) (s::l2).

(* list_sel_norepet: selector version of list_norepet except that we
strength the neq to selector_disjoint *)
Inductive list_sel_norepet : list selector -> Prop :=
  | list_sel_norepet_nil:
      list_sel_norepet nil
  | list_norepet_cons: forall hd tl
      (DIS: forall sel, In sel tl -> selector_disjoint hd sel)
      (NOREP: list_sel_norepet tl),
      list_sel_norepet (hd :: tl).

(* list_sel_disjoint: selector version of list_disjoint except that we
strength the neq to selector_disjoint *)
Definition list_sel_disjoint (l1 l2: list selector) : Prop :=
  forall (x y: selector), In x l1 -> In y l2 -> selector_disjoint x y.

Lemma list_sel_norepet_app:
  forall (l1 l2: list selector),
  list_sel_norepet (l1 ++ l2) <->
  list_sel_norepet l1 /\ list_sel_norepet l2 /\ list_sel_disjoint l1 l2.
Admitted.


(* Definition select_stmt_aux (sel: select_kind) (stmt: option statement)  *)
(* : option statement := *)
(*   match sel, stmt with *)
(*   | Selseqleft, Some (Ssequence s1 s2) => Some s1 *)
(*   | Selseqright, Some (Ssequence s1 s2) => Some s2 *)
(*   | Selifthen, Some (Sifthenelse _ s1 s2) => Some s1 *)
(*   | Selifelse, Some (Sifthenelse _ s1 s2) => Some s2 *)
(*   | Selloop, Some (Sloop s) => Some s *)
(*   | _, _ => None *)
(*   end. *)

(* Definition select_stmt (stmt: statement) (sel: selector) : option statement := *)
(*   fold_right select_stmt_aux (Some stmt) sel. *)

(** Maybe we can use fold_right to implement select_stmt and reverse *)
(* the selectors to simplify the proof *)
Fixpoint select_stmt (stmt: statement) (sel: selector) : option statement :=
  match sel, stmt with
  | nil, _ => Some stmt
  | Selseqleft :: sel', Ssequence s1 s2 => select_stmt s1 sel'
  | Selseqright :: sel', Ssequence s1 s2 => select_stmt s2 sel'
  | Selifthen :: sel', Sifthenelse _ s1 s2 => select_stmt s1 sel'
  | Selifelse :: sel', Sifthenelse _ s1 s2 => select_stmt s2 sel'
  | Selloop :: sel', Sloop s => select_stmt s sel'
  | _, _ => None
  end.

(* Change in place the statement resided in this selector to an another
statement. And return the modified statement *)
(** TODO: we do not want to use [rev] *)

(* Fixpoint update_stmt_aux (root: statement) (sel: selector) (stmt: statement): option statement := *)
(*   match sel, root with *)
(*   | nil, _ => Some stmt *)
(*   | Selseqleft :: sel', Ssequence s1 s2 => select_stmt s1 sel' *)
(*   | Selseqright :: sel', Ssequence s1 s2 => select_stmt s2 sel' *)
(*   | Selifthen :: sel', Sifthenelse _ s1 s2 => select_stmt s1 sel' *)
(*   | Selifelse :: sel', Sifthenelse _ s1 s2 => select_stmt s2 sel' *)
(*   | Selloop :: sel', Sloop s => select_stmt s sel' *)
(*   end.   *)
  (* match sel, root with *)
  (* | nil, _ => Some stmt *)
  (* | Selseqleft :: sel', Ssequence s1 s2 => *)
  (*     match (update_stmt_aux s1 sel' stmt) with *)
  (*     | Some s1' => Some (Ssequence s1' s2) *)
  (*     | None => None *)
  (*     end *)
  (* | Selseqright :: sel', Ssequence s1 s2 =>       *)
  (*     match (update_stmt_aux s2 sel' stmt) with *)
  (*     | Some s2' => Some (Ssequence s1 s2') *)
  (*     | None => None *)
  (*     end *)
  (* | Selifthen :: sel', Sifthenelse e s1 s2 => *)
  (*     match (update_stmt_aux s1 sel' stmt) with *)
  (*     | Some s1' => Some (Sifthenelse e s1' s2) *)
  (*     | None => None *)
  (*     end *)
  (* | Selifelse :: sel', Sifthenelse e s1 s2 => *)
  (*     match (update_stmt_aux s2 sel' stmt) with *)
  (*     | Some s2' => Some (Sifthenelse e s1 s2') *)
  (*     | None => None *)
  (*     end *)
  (* | Selloop :: sel', Sloop s => *)
  (*     match (update_stmt_aux s sel' stmt) with *)
  (*     | Some s' => Some (Sloop s') *)
  (*     | None => None *)
  (*     end *)
  (* | _, _ => None *)
  (* end. *)

Fixpoint update_stmt (root: statement) (sel: selector) (stmt: statement): option statement :=
  match sel, root with
  | nil, _ => Some stmt
  | Selseqleft :: sel', Ssequence s1 s2 =>
      match (update_stmt s1 sel' stmt) with
      | Some s1' => Some (Ssequence s1' s2)
      | None => None
      end
  | Selseqright :: sel', Ssequence s1 s2 =>      
      match (update_stmt s2 sel' stmt) with
      | Some s2' => Some (Ssequence s1 s2')
      | None => None
      end
  | Selifthen :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt s1 sel' stmt) with
      | Some s1' => Some (Sifthenelse e s1' s2)
      | None => None
      end
  | Selifelse :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt s2 sel' stmt) with
      | Some s2' => Some (Sifthenelse e s1 s2')
      | None => None
      end
  | Selloop :: sel', Sloop s =>
      match (update_stmt s sel' stmt) with
      | Some s' => Some (Sloop s')
      | None => None
      end
  | _, _ => None
  end.

(** ** Control flow graph based on selector *)

Definition node := positive.

(* An instruction  is either a selector or a control command (e.g., if-then-else) *)
Inductive instruction : Type :=
  | Inop: node -> instruction
  | Isel: selector -> node -> instruction
  | Icond: expr -> node -> node -> instruction
  | Iend: instruction.

Definition rustcfg := PTree.t instruction.

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop n => n :: nil
  | Isel _ n => n :: nil
  | Icond _ n1 n2 => n1 :: n2 :: nil
  | Iend => nil
  end.

Definition get_stmt (stmt: statement) (cfg: rustcfg) (pc: node) : option statement :=
  match cfg!pc with
  | Some instr =>
      match instr with
      | Isel sel _ =>
          select_stmt stmt sel
      | _ => None
      end
  | None => None
  end.


(** ** Generate CFG from a statement *)

(** * Translation state *)

Record generator: Type := mkstate {
  st_nextnode: node;
  st_code: rustcfg;
  st_wf: forall (pc: node), Plt pc st_nextnode \/ st_code!pc = None
}.


Inductive state_incr: generator -> generator -> Prop :=
  state_incr_intro:
    forall (s1 s2: generator)
    (PLE: Ple s1.(st_nextnode) s2.(st_nextnode))
    (INCL: forall pc, s1.(st_code)!pc = None
                 \/ s2.(st_code)!pc = s1.(st_code)!pc)
    (* there is an append strategy of the elements of s1 and s2 under
    the permutation *)
    (PERMU: exists l, Permutation (PTree.elements (st_code s2)) (PTree.elements (st_code s1) ++ l)),
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl.
  intros. auto.
  (* permutation *)
  exists nil. erewrite app_nil_r.
  reflexivity.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption.
  intros. generalize (INCL pc) (INCL0 pc). intuition congruence.
  destruct PERMU0. destruct PERMU.
  exists (x0++x). etransitivity. eauto.
  erewrite app_assoc.
  eapply Permutation_app. auto.
  reflexivity.
Qed.


(** ** The generator and error monad *)

(* just copy from RTLgen *)

Inductive res (A: Type) (s: generator): Type :=
  | Err: Errors.errmsg -> res A s
  | Res: A -> forall (s': generator), state_incr s s' -> res A s.

Arguments Res [A s].
Arguments Err [A s].

Definition mon (A: Type) : Type := forall (s: generator), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: generator) => Res x s (state_incr_refl s).


Definition error {A: Type} (msg: Errors.errmsg) : mon A := 
  fun (s: generator) => Err msg.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: generator) =>
    match f s with
    | Err msg => Err msg
    | Res a s' i =>
        match g a s' with
        | Err msg => Err msg
        | Res b s'' i' => Res b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Declare Scope cfg_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200): cfg_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200): cfg_monad_scope.

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s: generator) =>
    match f s with
    | Res a s' i => Res a s' i
    | Err _ => g s
    end.

(** monadInv for this error monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: generator) (i: state_incr s1 s3),
  bind f g s1 = Res y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = Res x s2 i1 /\ g x s2 = Res y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: generator) (i: state_incr s1 s3),
  bind2 f g s1 = Res z s3 i ->
  exists x, exists y, exists s2, exists i1, exists i2,
  f s1 = Res (x, y) s2 i1 /\ g x y s2 = Res z s3 i2.
Proof.
  unfold bind2; intros.
  exploit bind_inversion; eauto.
  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x; exists y; exists s2; exists i1; exists i2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (Err _ = Res _ _ _) =>
      discriminate
  | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = Res ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (@ret _ _ _ = Res _ _ _) => monadInv1 H
  | (@error _ _ _ = Res _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = Res ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = Res ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.


(** ** Operations on generator *)

(** The initial generator (empty CFG). *)

Remark init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty instruction)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : generator :=
  mkstate 1%positive (PTree.empty instruction) init_state_wf.


Remark add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros. case (peq pc n); intro.
  subst pc; left; apply Plt_succ.
  rewrite PTree.gso; auto.
  elim (st_wf s pc); intro.
  left. apply Plt_trans_succ. exact H.
  right; assumption.
Qed.

Remark add_instr_incr:
  forall s i,
  let n := s.(st_nextnode) in                                
  state_incr s (mkstate (Pos.succ n)
                  (PTree.set n i s.(st_code))
                  (add_instr_wf s i)).
Proof.
intros.
  constructor; simpl.
  apply Ple_succ.
  intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto.
  (* permutation *)
  exists [(n,i)].  
  exploit (@PTree.elements_remove instruction n i (PTree.set n i (st_code s))).
  eapply PTree.gss.
  intros (l1 & l2 & A1 & A2).
  rewrite A1.
  assert (A3: PTree.elements (st_code s) = l1 ++ l2).
  { erewrite <- A2.
    eapply PTree.elements_extensional.
    intros. rewrite PTree.grspec.
    destruct s. simpl in *.
    destruct (st_wf0 i0).
    - destruct PTree.elt_eq. subst. extlia.
      erewrite PTree.gso; auto.
    - destruct PTree.elt_eq. subst. auto.
      erewrite PTree.gso; auto. }
  rewrite A3.
  rewrite <- app_assoc. eapply Permutation_app.
  reflexivity. eapply Permutation_cons_app. rewrite app_nil_r. reflexivity.  
Qed.

Definition add_instr (i: instruction) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    Res n
       (mkstate (Pos.succ n) (PTree.set n i s.(st_code))
                (add_instr_wf s i))
       (add_instr_incr s i).

(** [add_instr] can be decomposed in two steps: reserving a fresh
  CFG node, and filling it later with an instruction.  This is needed
  to compile loops. *)

Remark reserve_instr_wf:
  forall s pc,
  Plt pc (Pos.succ s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof.
  intros. elim (st_wf s pc); intro.
  left; apply Plt_trans_succ; auto.
  right; auto.
Qed.

Remark reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode) in
  state_incr s (mkstate (Pos.succ n)
                  s.(st_code)
                      (reserve_instr_wf s)).
Proof.
  intros; constructor; simpl.
  apply Ple_succ.
  auto.
  (* permutation *)
  exists nil. rewrite app_nil_r. reflexivity.
Qed.

Definition reserve_instr: mon node :=
  fun (s: generator) =>
  let n := s.(st_nextnode) in
  Res n
     (mkstate (Pos.succ n) s.(st_code) (reserve_instr_wf s))
     (reserve_instr_incr s).

Remark update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode) ->
  forall pc,
  Plt pc s.(st_nextnode) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros.
  case (peq pc n); intro.
  subst pc; left; assumption.
  rewrite PTree.gso; auto. exact (st_wf s pc).
Qed.

Remark update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode)),
  s.(st_code)!n = None ->
  state_incr s
             (mkstate s.(st_nextnode) (PTree.set n i s.(st_code))
                     (update_instr_wf s n i LT)).
Proof.
  intros.
  constructor; simpl; intros.
  apply Ple_refl.
  rewrite PTree.gsspec. destruct (peq pc n). left; congruence. right; auto.
  (* permutation *)
  (* permutation *)
  exists [(n,i)].
  exploit (@PTree.elements_remove instruction n i (PTree.set n i (st_code s))).
  eapply PTree.gss.
  intros (l1 & l2 & A1 & A2).
  rewrite A1.
  assert (A3: PTree.elements (st_code s) = l1 ++ l2).
  { erewrite <- A2.
    eapply PTree.elements_extensional.
    intros. rewrite PTree.grspec.
    destruct PTree.elt_eq. subst. auto.
      erewrite PTree.gso; auto. }
  rewrite A3.
  rewrite <- app_assoc. eapply Permutation_app.
  reflexivity. eapply Permutation_cons_app. rewrite app_nil_r. reflexivity.  
Qed.

Definition check_empty_node:
  forall (s: generator) (n: node), { s.(st_code)!n = None } + { True }.
Proof.
  intros. case (s.(st_code)!n); intros. right; auto. left; auto.
Defined.

Definition update_instr (n: node) (i: instruction) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode), check_empty_node s n with
    | left LT, left EMPTY =>
        Res tt
           (mkstate s.(st_nextnode) (PTree.set n i s.(st_code))
                    (update_instr_wf s n i LT))
           (update_instr_incr s n i LT EMPTY)
    | _, _ =>
        Err (Errors.msg "RTLgen.update_instr")
    end. 


Local Open Scope cfg_monad_scope.

(** Translation of statement *)

Section COMPOSITE_ENV.

Variable (ce: composite_env).

Import ListNotations.

Fixpoint transl_stmt (end_node: node) (stmt: statement) (sel: selector) 
(succ: node) (cont: option node) (brk: option node) {struct stmt} 
: mon node :=
  let transl_stmt := transl_stmt end_node in
  match stmt with
  | Sskip =>
      ret succ
  | Sassign p e =>
      add_instr (Isel sel succ)
  | Sassign_variant p enum_id fid e =>
      add_instr (Isel sel succ)
  | Sbox p e =>
      add_instr (Isel sel succ)
  | Ssequence stmt1 stmt2 =>
      do succ2 <- transl_stmt stmt2 (sel ++ [Selseqright]) succ cont brk;
      do succ1 <- transl_stmt stmt1 (sel ++ [Selseqleft]) succ2 cont brk;
      ret succ1
  | Sifthenelse e stmt1 stmt2 =>
      do n1 <- transl_stmt stmt1 (sel ++ [Selifthen]) succ cont brk;
      do n2 <- transl_stmt stmt2 (sel ++ [Selifthen]) succ cont brk;
      do n3 <- add_instr (Icond e n1 n2);
      ret n3
  | Sloop stmt =>
      do loop_jump_node <- reserve_instr;
      (* The succ in function body is loop_start *)
      do body_start <- transl_stmt stmt (sel ++ [Selloop]) loop_jump_node (Some loop_jump_node) (Some succ);
      do _ <- update_instr loop_jump_node (Inop body_start);
      (* return loop_jump_node and return body_start are equivalent *)
      ret loop_jump_node
  | Sbreak =>
      match brk with
      | None =>
          error (Errors.msg "No loop outside the break: transl_stmt")
      | Some brk =>
          add_instr (Inop brk)
      end
  | Scontinue =>
      match cont with
      | None =>
          error (Errors.msg "No loop outside the continue")
      | Some cont =>
          add_instr (Inop cont)
      end
  | Sstoragelive id =>
      add_instr (Isel sel succ)
  | Sstoragedead id =>
      add_instr (Isel sel succ)
  | Sdrop p =>
      add_instr (Isel sel succ)
  | Scall p a al =>
      add_instr (Isel sel succ)
  | Sreturn e =>
      add_instr (Isel sel end_node)
    end.

Definition generate_cfg' (stmt: statement): mon node :=
  (* return node *)
  do return_node <- add_instr Iend;
  transl_stmt return_node stmt nil return_node None None.

Definition generate_cfg (stmt: statement): Errors.res (node * rustcfg) :=  
  match generate_cfg' stmt init_state with
  | Res start st _ =>
      Errors.OK (start, st.(st_code))
  | Err msg =>
      Errors.Error msg
  end.
  

End COMPOSITE_ENV.


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
(* backward traversal of CFG. [next] node is used in tr_cont, so it
should matches the AST *)
| tr_Sbreak: forall brk cont endn next,
    tr_stmt body cfg Sbreak brk next cont (Some brk) endn
| tr_Scontinue: forall brk cont endn next,
    tr_stmt body cfg Scontinue cont next (Some cont) brk endn
| tr_Sreturn: forall pc sel succ endn e cont brk
    (SEL: cfg ! pc = Some (Isel sel endn))
    (STMT: select_stmt body sel = Some (Sreturn e)),
    tr_stmt body cfg (Sreturn e) pc succ cont brk endn
.

Inductive tr_fun (f: function) (nret: node) : node -> rustcfg -> Prop :=
| tr_fun_intro: forall entry cfg
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (STMT: tr_stmt f.(fn_body) cfg f.(fn_body) entry nret None None nret)
    (RET: cfg ! nret = Some Iend),
    tr_fun f nret entry cfg.


(** Comment it because we changed the definition of select_stmt and
update_stmt, and tr_fun is unused in the proof of the compilation *)
Lemma add_instr_at:
    forall i n s s' R, add_instr i s = Res n s' R ->
    (st_code s') ! n = Some i.
Proof.
  intros. monadInv H. simpl. rewrite PTree.gss. auto.
Qed.

(* Lemma add_instr_next: *)
(*     forall n0 s n s' R, *)
(*     add_instr (Inop n0) s = Res n s' R -> *)
(*     n0 = n. *)
(* Proof. *)
(*   intros. monadInv H. inversion R. subst. *)
(*   Admitted. *)

(* Lemma update_instr_at: *)
(*     forall i n x s s' R, update_instr n i s = Res x s' R -> *)
(*     (st_code s') ! n = Some i. *)
(* Proof.  *)
(*   intros. unfold update_instr in H.  *)
(*   destruct (plt n (st_nextnode s)) eqn:E; *)
(*   destruct (check_empty_node s n) eqn:E2; inversion H. *)
(*   eapply PTree.gss. *)
(* Qed.  *)

(* Lemma ret_instr_at: *)
(*   forall (succ:positive) n s s' R, ret succ s = Res n s' R -> *)
(*   n = succ. *)
(* Proof. *)
(*   intros. inversion H. auto. *)
(* Qed. *)

(* Lemma select_stmt_sequence_first : *)
(*   forall body sel stmt1 stmt2, *)
(*     select_stmt body sel = Some (Ssequence stmt1 stmt2) -> *)
(*     select_stmt body (Selseqleft :: sel) = Some stmt1 *)
(* with select_stmt_sequence_second : *)
(*   forall body sel stmt1 stmt2, *)
(*     select_stmt body sel = Some (Ssequence stmt1 stmt2) -> *)
(*     select_stmt body (Selseqright :: sel) = Some stmt2 *)
(* with select_stmt_ifelse_if : *)
(*   forall body sel e stmt1 stmt2, *)
(*   select_stmt body sel = Some (Sifthenelse e stmt1 stmt2) -> *)
(*   select_stmt body (Selifthen :: sel) = Some stmt1 *)
(* with select_stmt_ifelse_else : *)
(*   forall body sel e stmt1 stmt2, *)
(*   select_stmt body sel = Some (Sifthenelse e stmt1 stmt2) -> *)
(*   select_stmt body (Selifelse :: sel) = Some stmt2 *)
(* with select_stmt_loop : *)
(*   forall body sel stmt, *)
(*   select_stmt body sel = Some (Sloop stmt) -> *)
(*   select_stmt body (Selloop :: sel) = Some stmt. *)
(* Proof. *)
(*   intros. simpl. rewrite H. reflexivity. *)
(*   intros. simpl. rewrite H. reflexivity. *)
(*   intros. simpl. rewrite H. reflexivity. *)
(*   intros. simpl. rewrite H. reflexivity. *)
(*   intros. simpl. rewrite H. reflexivity. *)
(* Qed. *)

Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> s2.(st_code)!n = Some i.
Proof.
  intros. inv H.
  destruct (INCL n); congruence.
Qed.

(* Lemma tr_stmt_incr: *)
(*   forall s1 s2, state_incr s1 s2 -> *)
(*   forall body stmt n succ cont brk nret, *)
(*   tr_stmt body (st_code s1) stmt n succ cont brk nret -> *)
(*   tr_stmt body (st_code s2) stmt n succ cont brk nret. *)
(* Proof. *)
(*   intros s1 s2 EXT. *)
(*   pose (AT:= fun pc i => instr_at_incr s1 s2 pc i EXT). *)
(*   induction 1; econstructor; eauto. *)
(* Qed. *)


(* (* tr_stmt matches transl_stmt *) *)
(* Lemma transl_stmt_charact: forall body sel stmt nret succ cont brk s s' n R, *)
(*     select_stmt body sel = Some stmt -> *)
(*     transl_stmt nret stmt sel succ cont brk s = Res n s' R -> *)
(*     tr_stmt body s'.(st_code) stmt n succ cont brk nret. *)
(* Proof. *)
(* intros until stmt. generalize dependent sel. *)
(* induction stmt; intros; simpl in H0. *)
(* (* Sskip *) *)
(* apply ret_instr_at in H0. subst. constructor. *)
(* (* Sassign *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Sassign_variant *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Sbox *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Sstoragelive *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Sstoragedead *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Sdrop *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Scall *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* (* Ssequence *) *)
(* monadInv H0. econstructor.  *)
(* eapply IHstmt1. eapply select_stmt_sequence_first. eauto. eauto. *)
(* eapply (tr_stmt_incr s0 s'). congruence. *)
(* eapply IHstmt2. eapply select_stmt_sequence_second. eauto. eauto. *)
(* (* Sifthenelse *) *)
(* monadInv H0. econstructor. eapply (tr_stmt_incr s0 s'). *)
(* eapply state_incr_trans; eauto. *)
(* eapply IHstmt1. eapply select_stmt_ifelse_if. eauto. eauto. *)
(* eapply (tr_stmt_incr s1 s'). eapply state_incr_trans; eauto. *)
(* eapply IHstmt2. eapply select_stmt_ifelse_else. eauto. eauto. *)
(* eapply add_instr_at. eauto. *)
(* (* Sloop *) *)
(* monadInv H0. econstructor.  *)
(* eapply (tr_stmt_incr s1 s'). eapply state_incr_trans; eauto. *)
(* eapply IHstmt. eapply select_stmt_loop. eauto. eauto. *)
(* eapply update_instr_at. eauto. *)
(* (* Sbreak *) *)
(* destruct brk. *)
(*   apply add_instr_next in H0. subst n0. apply tr_Sbreak. *)
(*   inversion H0. *)
(* (* Scontinue *) *)
(* destruct cont. *)
(*   apply add_instr_next in H0. subst n0. apply tr_Scontinue. *)
(*   inversion H0. *)
(* (* Sreturn *) *)
(* econstructor. eapply add_instr_at. eauto. eauto. *)
(* Qed. *)

(* Lemma generate_cfg_charact: forall f entry cfg, *)
(*     generate_cfg f.(fn_body) = OK (entry, cfg) -> *)
(*     exists nret, tr_fun f nret entry cfg. *)
(* Proof. *)
(*   intros f entry cfg GEN. *)
(*   generalize GEN. intros GEN'. *)
(*   unfold generate_cfg in GEN. *)
(*   destruct (generate_cfg' (fn_body f) init_state) eqn: GCFG; try congruence. *)
(*   inv GEN. unfold generate_cfg' in GCFG. *)
(*   monadInv GCFG. exists x. econstructor. eapply GEN'. *)
(*   eapply transl_stmt_charact with (sel:=nil). eauto. *)
(*   eauto. eapply add_instr_res_incr in EQ. *)
(*   eapply add_instr_at in EQ. eapply EQ.  *)
(*   eauto. eauto. Unshelve. eauto. *)
(*   (** Unshelve? *) *)
(* Qed. *)

(* Lemma generate_cfg_exists_nret: forall f entry cfg, *)
(*     generate_cfg f.(fn_body) = OK (entry, cfg) -> *)
(*     exists nret, cfg ! nret = Some Iend. *)
(* Proof. *)
(*   intros. exploit generate_cfg_charact; eauto. *)
(*   intros (nret & TRFUN). inv TRFUN. *)
(*   eauto. *)
(* Qed. *)


(** * A general framework for CFG compilation based on selectors *)

Local Open Scope error_monad_scope.

Definition set_stmt (pc: node) (body: statement) (sel: selector) 
(s: statement) : Errors.res statement :=
  match update_stmt body sel s with
  | Some body1 => OK body1
  | None =>
      Error [CTX pc; MSG " update_stmt error in set_stmt"]
  end.


Section TRANSL.

Context {AN: Type} {An: Type} (get_an: AN -> node -> An).
Context (ae: AN).
Context (transl_stmt: An -> statement -> Errors.res statement).

Definition transl_on_instr (src: statement) (pc: node) (instr: instruction)
 : Errors.res statement :=
  match instr with
  | Isel sel _ =>
      match select_stmt src sel with
      | Some s =>
          do ts <- transl_stmt (get_an ae pc) s;
          set_stmt pc src sel ts
      | None =>
          Error [CTX pc; MSG " select_stmt error in transl_on_instr"]
      end
  (* no way to translate them in the AST side without selector *)
  | _ => OK src
  end.

Definition transl_on :=
  fun body pc instr => 
    do body' <- body; transl_on_instr body' pc instr.

Definition transl_on_cfg (src: statement) (cfg: rustcfg) 
: Errors.res statement :=
  PTree.fold transl_on cfg (OK src).

(* Translation relation between source statment and target statement *)

Section SPEC.

(* Dynamic elaboration of statement based on own_env *)
Inductive match_stmt (body: statement) (cfg: rustcfg) : statement -> 
statement -> node -> node -> option node -> option node -> node -> Prop :=
| match_Sskip: forall pc cont brk endn,
    match_stmt body cfg Sskip Sskip pc pc cont brk endn
| match_Sassign: forall pc next sel p e ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign p e))
    (TR: transl_stmt (get_an ae pc) (Sassign p e) = OK ts),
    match_stmt body cfg (Sassign p e) ts pc next cont brk endn
| match_Sassign_variant: forall pc next sel p e enum_id fid ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign_variant p enum_id fid e))
    (TR: transl_stmt (get_an ae pc) (Sassign_variant p enum_id fid e) = OK ts),
    match_stmt body cfg (Sassign_variant p enum_id fid e) ts pc next cont brk endn
| match_Sbox: forall pc next sel p e ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sbox p e))
    (TR: transl_stmt (get_an ae pc) (Sbox p e) = OK ts),
    match_stmt body cfg (Sbox p e) ts pc next cont brk endn
| match_Sstoragelive: forall pc next sel ts id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragelive id))
    (TR: transl_stmt (get_an ae pc) (Sstoragelive id) = OK ts),
    match_stmt body cfg (Sstoragelive id) ts pc next cont brk endn
| match_Sstoragedead: forall pc next sel ts id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragedead id))
    (TR: transl_stmt (get_an ae pc) (Sstoragedead id) = OK ts),
    match_stmt body cfg (Sstoragedead id) ts pc next cont brk endn
| match_Sdrop: forall p pc next ts sel cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sdrop p))
    (TR: transl_stmt (get_an ae pc) (Sdrop p) = OK ts),
    match_stmt body cfg (Sdrop p) ts pc next cont brk endn
| match_Scall: forall pc next sel ts p e l cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Scall p e l))
    (TR: transl_stmt (get_an ae pc) (Scall p e l) = OK ts),
    match_stmt body cfg (Scall p e l) ts pc next cont brk endn
| match_Ssequence: forall s1 ts1 s2 ts2 n1 n2 n3 cont brk endn
    (MSTMT1: match_stmt body cfg s1 ts1 n1 n2 cont brk endn)
    (MSTMT2: match_stmt body cfg s2 ts2 n2 n3 cont brk endn),
    match_stmt body cfg (Ssequence s1 s2) (Ssequence ts1 ts2) n1 n3 cont brk endn
| match_Sifthenelse: forall s1 ts1 s2 ts2 n1 n2 endif cont brk endn e
    (MSTMT1: match_stmt body cfg s1 ts1 n1 endif cont brk endn)
    (MSTMT2: match_stmt body cfg s2 ts2 n2 endif cont brk endn),
    (* For now, no way to compile the expression in Icond *)
    match_stmt body cfg (Sifthenelse e s1 s2) (Sifthenelse e ts1 ts2) n1 endif cont brk endn
| match_Sloop: forall s ts next loop_start loop_jump_node cont brk endn
    (MSTMT: match_stmt body cfg s ts loop_start loop_jump_node (Some loop_jump_node) (Some next) endn)
    (START: cfg ! loop_jump_node = Some (Inop loop_start)),
    match_stmt body cfg (Sloop s) (Sloop ts) loop_jump_node next brk cont endn
| match_Sbreak: forall brk cont endn next,
    match_stmt body cfg Sbreak Sbreak brk next cont (Some brk) endn
| match_Scontinue: forall brk cont endn next,
    match_stmt body cfg Scontinue Scontinue cont next (Some cont) brk endn
| match_Sreturn: forall pc sel next e ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sreturn e))
    (TR: transl_stmt (get_an ae pc) (Sreturn e) = OK ts),
    match_stmt body cfg (Sreturn e) ts pc next cont brk endn
.


Lemma select_stmt_nil: forall s,
    select_stmt s [] = Some s.
  induction s; auto.
Qed.

Lemma select_stmt_app: forall sel1 sel2 s1 s2 s3,
    select_stmt s1 sel1 = Some s2 ->
    select_stmt s2 sel2 = Some s3 ->
    select_stmt s1 (sel1 ++ sel2) = Some s3.
Proof.
  induction sel1; intros.
  - simpl. erewrite select_stmt_nil in H. inv H. auto.
  - destruct a; destruct s1; simpl in *; try congruence; eauto.
Qed.

Lemma select_stmt_app_inv: forall l1 l2 body s,
    select_stmt body (l1 ++ l2) = Some s ->
    exists body1, select_stmt body l1 = Some body1
             /\ select_stmt body1 l2 = Some s.
Proof.
  induction l1; intros; simpl in *.
  - exists body. split. eapply select_stmt_nil.
    auto.
  - destruct a; destruct body; simpl in *; try congruence; eauto.
Qed.

Lemma update_stmt_nil: forall s body,
    update_stmt body [] s = Some s.
  induction body; auto.
Qed.


Lemma update_stmt_select: forall sel body1 body2 s,
    update_stmt body1 sel s = Some body2 ->
    select_stmt body2 sel = Some s.
Proof.
  induction sel; intros; simpl in *.
  - erewrite update_stmt_nil in H. inv H.
    eapply select_stmt_nil.
  - destruct a; destruct body1; simpl in *; try congruence; eauto.
    + destruct (update_stmt body1_1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_2 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_2 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
Qed.

Lemma set_stmt_select: forall sel body1 body2 s pc,
    set_stmt pc body1 sel s = OK body2 ->
    select_stmt body2 sel = Some s.
Proof.
  intros. unfold set_stmt in H.
  destruct (update_stmt body1 sel s) eqn: A; try congruence.
  inv H.
  eapply update_stmt_select; eauto.
Qed.  

Lemma transl_on_instrs_error: forall l msg,
    fold_left (fun (a : Errors.res statement) (p : positive * instruction) =>
                 transl_on a (fst p) (snd p)) l (Error msg) = Error msg.
Proof.
  induction l; simpl; auto.
Qed.

Lemma update_stmt_disjoint_select: forall sel1 sel2 body1 body2 s1 s2,
    select_stmt body1 sel1 = Some s1 ->
    update_stmt body1 sel2 s2 = Some body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body2 sel1 = Some s1.
Proof.
  induction sel1; intros.
  - inv H1.
  - inv H1.
    + destruct body1; destruct a; destruct s3; simpl in *; try congruence.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
    + destruct body1; destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
Qed.

                
Lemma set_stmt_disjoint_select: forall sel1 sel2 body1 body2 s1 s2 pc,
    select_stmt body1 sel1 = Some s1 ->
    set_stmt pc body1 sel2 s2 = OK body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body2 sel1 = Some s1.
Proof.
  intros. unfold set_stmt in H0.
  destruct (update_stmt body1 sel2 s2) eqn: A in H0; try congruence.
  inv H0.
  eapply update_stmt_disjoint_select; eauto.
Qed.


Lemma transl_on_instrs_unchanged: forall l sel body1 body2 s
    (SEL: select_stmt body1 sel = Some s)
    (TRANSL: fold_left (fun (a : Errors.res statement) (p : positive * instruction) =>
                          transl_on a (fst p) (snd p)) l (OK body1) = OK body2)
    (DISJOINT: forall pc sel1 n, In (pc, (Isel sel1 n)) l ->
                                selector_disjoint sel sel1),
    select_stmt body2 sel = Some s.
Proof.
  induction l; intros; simpl in *.
  - inv TRANSL. auto.
  - destruct (transl_on_instr body1 (fst a) (snd a)) eqn: A.
    2: { erewrite transl_on_instrs_error in TRANSL. congruence. }
    destruct a. simpl in *.
    unfold transl_on_instr in A.
    destruct i.
    + inv A. eapply IHl; eauto.
    + destruct (select_stmt body1 s1) eqn: SEL1; try congruence.
      Errors.monadInv A.
      exploit set_stmt_select; eauto.
      intros SEL2.
      exploit DISJOINT. left. eauto. intros DIS.
      (* so select_stmt so sel = Some s *)      
      exploit set_stmt_disjoint_select. eapply SEL. eauto. auto.
      intros SEL3.
      eapply IHl; eauto.
    + inv A. eapply IHl; eauto.
    + inv A. eapply IHl; eauto.
Qed.
    
    
Lemma transl_on_cfg_unchanged: forall sel s body1 body2 cfg,
    select_stmt body1 sel = Some s ->
    transl_on_cfg body1 cfg = OK body2 ->
    (forall pc sel1 n, cfg ! pc = Some (Isel sel1 n) ->
                  selector_disjoint sel sel1) ->
    select_stmt body2 sel = Some s.
Proof.
  intros. unfold transl_on_cfg in H0.
  erewrite PTree.fold_spec in H0.
  eapply transl_on_instrs_unchanged; eauto.
  intros. eapply H1.
  eapply PTree.elements_complete. eauto.
Qed.
 
Definition is_atomic_stmt (s: statement) : Prop :=
  match s with
  | Sassign _ _
  | Sassign_variant _ _ _ _
  | Sbox _ _
  | Sstoragelive _
  | Sstoragedead _
  | Sdrop _
  | Scall _ _ _ => True
  | _ => False
  end.
                     
(* Cases of atomic statement in transl_on_cfg_charact *)
Lemma add_instr_charact: forall sel  g n g' R body1 body2 stmt succ cont brk nret
    (TRSTMT: add_instr (Isel sel succ) g = Res n g' R)
    (SEL: select_stmt body1 sel = Some stmt)
    (TRANSL: transl_on_cfg body1 (st_code g') = OK body2)
    (DISJOINT: forall (pc : positive) (sel1 : selector) (n : node),
        (st_code g) ! pc = Some (Isel sel1 n) -> selector_disjoint sel sel1)
    (ATOMIC: is_atomic_stmt stmt),
    exists ts,
      select_stmt body2 sel = Some ts /\
        match_stmt body1 (st_code g') stmt ts n succ cont brk nret.
Proof.
  intros.      
  unfold add_instr in TRSTMT. inv TRSTMT. simpl in *.
  set (pc:=st_nextnode g) in *.
  unfold transl_on_cfg in TRANSL.
  rewrite PTree.fold_spec in TRANSL.
  assert (A: (PTree.set pc (Isel sel succ) (st_code g)) ! pc = Some (Isel sel succ)).
  eapply PTree.gss.        
  exploit PTree.elements_remove; eauto.
  intros (l1 & l2 & B1 & B2).
  rewrite B1 in TRANSL.
  (* show disjointness of l1++l2 *)
  assert (E: forall i, (PTree.remove pc (PTree.set pc (Isel sel succ) (st_code g))) ! i = (st_code g) ! i).
  { intros.
    erewrite PTree.grspec.
    destruct PTree.elt_eq. subst.
    (* st_code must not contain pc by st_wf *)
    symmetry.
    destruct (st_wf g pc). unfold pc in *. extlia. auto.
    erewrite PTree.gso; auto. }
  erewrite PTree.elements_extensional in B2; eauto.
  (* simplify TRANSL *)
  rewrite fold_left_app in TRANSL.
  set (transl:= (fun (a : Errors.res statement) (p : positive * instruction) =>
                   transl_on a (fst p) (snd p))) in *.
  set (body1' := (fold_left transl l1 (OK body1))) in *.
  simpl in TRANSL.

  unfold node in *.
  destruct ((transl body1' (pc, Isel sel succ))) eqn: C1 in TRANSL.
  2: { erewrite transl_on_instrs_error in TRANSL. congruence. }      
  (* monadInv C1 *)
  unfold transl, transl_on_instr in C1.
  simpl in C1.
  Errors.monadInv C1.
  unfold transl_on_instr in EQ0.
  destruct (select_stmt x sel) eqn: SEL1; try congruence.
  unfold body1' in EQ. Errors.monadInv EQ0.
  (* transl on disjoint selector select_stmt is unchanged *)
  exploit transl_on_instrs_unchanged. eapply SEL. eauto.
  (* prove disjointness *)   
  intros. eapply DISJOINT. eapply PTree.elements_complete.
  erewrite B2. eapply in_app. eauto. intros SEL2.
  rewrite SEL1 in SEL2. inv SEL2.    
  exists x0.    
  split.
  (* set_stmt and then select it *)
  unfold set_stmt in EQ2.
  destruct (update_stmt x sel x0) eqn: UPDATE; try congruence.
  inv EQ2.
  exploit update_stmt_select; eauto. 
  intros SEL2.
  eapply transl_on_instrs_unchanged; eauto.
  (* prove disjointness *)   
  intros. eapply DISJOINT. eapply PTree.elements_complete.
  erewrite B2. eapply in_app. eauto.
  (* prove match_stmt *)
  destruct stmt; simpl in ATOMIC; try contradiction.
  all: econstructor; try eapply PTree.gss; auto. 
Qed.


(* The new instructions in the translated cfg can only contain
   some selectors whose prefix is sel *)
Lemma transl_stmt_selectors_prefix: forall s nret sel1 sel2 n1 n2 n3 cont brk g1 g2 R pc,
    RustIRcfg.transl_stmt nret s sel1 n1 cont brk g1 = Res n2 g2 R ->
    (st_code g1) ! pc = None ->
    (st_code g2) ! pc = Some (Isel sel2 n3) ->
    exists l, sel1 ++ l = sel2.
Proof.
  Ltac solve_atomic TRANSL G2 :=
    inv TRANSL; simpl in *;
    erewrite PTree.gsspec in G2;
    destruct peq in G2; try congruence; inv G2;
    exists nil; eapply app_nil_r.
    
  induction s; intros until pc; intros TRANSL G1 G2; simpl in TRANSL; try solve_atomic TRANSL G2.  
  - inv TRANSL. congruence.
  - monadInv TRANSL.
    (* case analysis of pc in s *)
    inv INCR0. generalize (INCL pc). intros [A1|A2].
    + exploit IHs1; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
    + erewrite A2 in G2.
      exploit IHs2; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
  - monadInv TRANSL.
    assert (G3: (st_code s0) ! pc = Some (Isel sel2 n3)).
    { unfold add_instr in EQ0. inv EQ0. simpl in *.
      erewrite PTree.gsspec in G2.
      destruct peq in G2; try congruence. }
    (* case analysis of pc in s *)
    generalize INCR1. intros.
    inv INCR5. generalize (INCL pc). intros [A1|A2].
    + exploit IHs2; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
    + erewrite A2 in G3.
      exploit IHs1; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
  - monadInv TRANSL.
    assert (G3: (st_code s1) ! pc = Some (Isel sel2 n3)).
    {  unfold update_instr in EQ0. destruct plt in EQ0; try congruence.
       destruct (check_empty_node s1 n2); try congruence.
       inv EQ0. simpl in *.
       erewrite PTree.gsspec in G2.
       destruct peq in G2; try congruence. }
    assert (G4: (st_code s0) ! pc = None).
    { unfold reserve_instr in EQ. inv EQ.
      simpl in *. auto. }    
    exploit IHs; eauto.
    intros (l & A3). subst.
    erewrite <- app_assoc. eauto.
  - destruct brk; try congruence.
    unfold add_instr in TRANSL. inv TRANSL. simpl in *.
    erewrite PTree.gsspec in G2.
    destruct peq in G2; try congruence.
    monadInv TRANSL.
  - destruct cont; try congruence.
    unfold add_instr in TRANSL. inv TRANSL. simpl in *.
    erewrite PTree.gsspec in G2.
    destruct peq in G2; try congruence.
    monadInv TRANSL.
Qed.


Lemma selector_disjoint_sym: forall s1 s2,
    selector_disjoint s1 s2 ->
    selector_disjoint s2 s1.
Proof.
  induction s1; intros; inv H.
  - econstructor. auto.
  - eapply sel_disjoint_cons. eauto.
Qed.

Lemma selector_disjoint_app1: forall s1 s2 l,
    selector_disjoint s1 s2 ->
    selector_disjoint s1 (s2 ++ l).
Proof.
  induction s1; intros; inv H.
  - simpl. econstructor. auto.
  - simpl. eapply sel_disjoint_cons. eauto.
Qed.

Lemma selector_disjoint_app2: forall l s1 s2,
    selector_disjoint s1 s2 ->
    selector_disjoint (l ++ s1) (l ++ s2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. eapply sel_disjoint_cons. eauto.
Qed.


Let transl := (fun (a : Errors.res statement) (p : positive * instruction) =>
                 transl_on a (fst p) (snd p)).

(* Lemma transl_on_instrs_sel_norepet: forall body g1 g2, *)
(*     list_sel_norepet (PTree.elements (st_code g1)) -> *)
(*     RustIRcfg.transl_stmt nret body n succ cont brk = Res n  *)

Lemma transl_on_cfg_state_incr: forall body1 body2 g1 g2,
    transl_on_cfg body1 (st_code g2) = OK body2 ->
    state_incr g1 g2 ->
    exists body3, transl_on_cfg body1 (st_code g1) = OK body3.
Admitted.


(* auxilary lemma for transl_on_cfg_state_incr_unchanged *)
Lemma transl_on_instrs_incr_unchanged: forall l1 l2 body body1 body2 sel1 s
    (TR1: fold_left transl l1 (OK body) = OK body1)
    (TR2: fold_left transl l2 (OK body) = OK body2)
    (INCL: incl l1 l2)
    (DISJOINT: forall pc sel2 n, ~ In (pc, (Isel sel2 n)) l1 ->          
                            In (pc, (Isel sel2 n)) l2 ->
                            selector_disjoint sel1 sel2)
    (SEL: select_stmt body1 sel1 = Some s),
    select_stmt body2 sel1 = Some s.
Proof.
  (* induction l1; intros; simpl in *. *)
  (* - inv TR1. eapply transl_on_instrs_unchanged. eauto. *)
  (*   eauto. *)
  (*   (* disjointness *) *)
  (*   intros. eapply DISJOINT. congruence. eauto. *)
  (* - destruct a. simpl in *. *)
  (*   destruct (transl_on_instr body p i) eqn: A. *)
  (*   2: { erewrite transl_on_instrs_error in TR1. congruence. } *)
  (*   unfold transl_on_instr in A. destruct i. *)
  (*   + inv A. eapply IHl1; eauto. *)
  (*     eapply incl_cons_inv. eauto.  *)
  (*     intros. eapply DISJOINT; eauto. intro. *)
  (*     destruct H1. inv H1. congruence. *)
  (*   + destruct (select_stmt body s1) eqn: SEL1; try congruence. *)
  (*     Errors.monadInv A. *)
  (*     in_split *)

  (*       PTree.fold_spec *)
  (*       PTree.fold1_spec *)

        
  (*   + inv A. eapply IHl1; eauto. *)
  (*     eapply incl_cons_inv. eauto.  *)
  (*     intros. eapply DISJOINT; eauto. intro. *)
  (*     destruct H1. inv H1. congruence. *)
  (*   + inv A. eapply IHl1; eauto. *)
  (*     eapply incl_cons_inv. eauto.  *)
  (*     intros. eapply DISJOINT; eauto. intro. *)
  (*     destruct H1. inv H1. congruence. *)
Admitted.

Lemma transl_on_cfg_state_incr_unchanged: forall body body1 body2 g1 g2 sel1 s
    (TR1: transl_on_cfg body (st_code g1) = OK body1)
    (TR2: transl_on_cfg body (st_code g2) = OK body2)
    (INCR: state_incr g1 g2)
    (SEL: select_stmt body1 sel1 = Some s)
    (DISJOINT: forall pc sel2 n, (st_code g1) ! pc = None ->
                            (st_code g2) ! pc = Some (Isel sel2 n) ->
                            selector_disjoint sel1 sel2),
    select_stmt body2 sel1 = Some s.
Proof.
  intros.
  unfold transl_on_cfg in *.
  rewrite PTree.fold_spec in *.
Admitted.  

Lemma match_stmt_state_incr: forall s ts body g1 g2 pc succ cont brk nret,
    match_stmt body (st_code g1) s ts pc succ cont brk nret ->
    state_incr g1 g2 ->
    match_stmt body (st_code g2) s ts pc succ cont brk nret.
Proof.
  induction s; intros until nret; intros MSTMT INCR; inv MSTMT; try econstructor; eauto.
  all : inv INCR; destruct (INCL pc); try congruence;
    erewrite H1; auto.
Qed.


(** Key proof of transl_on_cfg_meet_spec  *)
Lemma transl_on_cfg_charact: forall s body1 body2 n succ cont brk nret sel g g' R
  (* similar to transl_stmt_charact *)
  (TRSTMT: RustIRcfg.transl_stmt nret s sel succ cont brk g = Res n g' R)
  (SEL: select_stmt body1 sel = Some s)
  (* transl_on the updated cfg (st_code g') *)
  (TRANSL: transl_on_cfg body1 (st_code g') = OK body2)
  (DISJOINT: forall pc sel1 n, (st_code g) ! pc = Some (Isel sel1 n) ->
                          selector_disjoint sel sel1),
  (* disjointness in the g *)
  (* list_norepet_app *)
  exists ts,
    select_stmt body2 sel = Some ts
    /\ match_stmt body1 (st_code g') s ts n succ cont brk nret.
Proof.
  induction s; intros; simpl in TRSTMT.
  - inv TRSTMT.        
    exists Sskip. split.
    eapply transl_on_cfg_unchanged; eauto.
    econstructor.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  - eapply add_instr_charact; eauto.
    red. auto.
  (* Ssequence *)
  - monadInv TRSTMT.    
    exploit IHs1; eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    (* prove disjointness: the new selectors in s not in g must be (sel++[Selseqleft]++l)) *)
    intros. generalize INCR as A. intros. inv A.
    generalize (INCL pc). intros [B1|B2].
    exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
    intros (l & B3). subst.
    eapply selector_disjoint_app1.
    eapply selector_disjoint_app2. econstructor. congruence.
    eapply selector_disjoint_sym.
    eapply selector_disjoint_app1. eapply selector_disjoint_sym.
    eapply DISJOINT; eauto. erewrite <- B2. eauto.
    intros (ts1 & SEL1 & MSTMT1).
    (* use IHs2 *)
    (* first prove that transl_on_cfg s also success *)
    exploit transl_on_cfg_state_incr. eapply TRANSL. eapply INCR1. 
    intros (body3 & T1).    
    exploit IHs2. eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    eauto.    
    (* prove disjointness *)
    intros.
    eapply selector_disjoint_sym.
    eapply selector_disjoint_app1. eapply selector_disjoint_sym.
    eapply DISJOINT; eauto.    
    intros (ts2 & SEL2 & MSTMT2).
    (* use SEL2 prove that the selection in body2 return the same result *)
    assert (SEL3: select_stmt body2 (sel++[Selseqright]) = Some ts2).
    { eapply transl_on_cfg_state_incr_unchanged.
      eapply T1. eauto. eauto. eauto.
      (* prove disjointness *)
      intros.
      exploit transl_stmt_selectors_prefix. eapply EQ1. eauto. eauto.
      intros (l & A). subst.
      rewrite <- app_assoc. eapply selector_disjoint_app2. econstructor.
      congruence. }
    exploit select_stmt_app_inv. eapply SEL1. intros (b1 & S1 & S2).
    exploit select_stmt_app_inv. eapply SEL3. intros (b2 & S3 & S4).
    rewrite S1 in S3. inv S3. destruct b2; simpl in *; try congruence.
    erewrite select_stmt_nil in *. inv S2. inv S4.
    exists (Ssequence ts1 ts2). split; auto.
    econstructor; eauto.
    (* match_stmt_state_Incr *)
    eapply match_stmt_state_incr; eauto.
  -       
    (* 2 cases, pc is in g or pc not in g and all selector in s is disjoint with  *)
    
  (* - rewrite  *)
Admitted.

Lemma transl_on_cfg_meet_spec: forall f ts cfg entry
    (CFG: generate_cfg (fn_body f) = OK (entry, cfg))
    (TRANSL: transl_on_cfg (fn_body f) cfg = OK ts),
  exists nret, match_stmt (fn_body f) cfg (fn_body f) ts entry nret None None nret
          /\ cfg ! nret = Some Iend.
Proof.  
  intros. unfold generate_cfg in CFG.
  destruct (generate_cfg' (fn_body f) init_state) eqn: GENCFG; try congruence.
  unfold generate_cfg' in GENCFG.
  monadInv GENCFG. inv CFG.
  exploit transl_on_cfg_charact; eauto.
  eapply select_stmt_nil.
  (* disjointness *)
  intros.
  unfold add_instr in EQ. inv EQ. simpl in *.
  (* if pc = x  *)
  erewrite PTree.gsspec in H. destruct peq in H; try congruence.
  erewrite PTree.gempty  in H. inv H.  
  intros (ts1 & SEL & MSTMT). simpl in SEL. inv SEL.
  exists x.
  erewrite select_stmt_nil in H0. inv H0.
  split; auto.
  (* prove cfg!nret = Some Iend *)
  clear EQ0.
  eapply instr_at_incr. eauto.
  eapply add_instr_at. eauto.
Qed.

End SPEC.

End TRANSL.

