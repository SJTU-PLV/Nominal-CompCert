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

Import ListNotations.

(** ** Definition of selector. It is the program pointer in AST-like program.  *)

Inductive select_kind : Type :=
| Selseqleft: select_kind
| Selseqright: select_kind
| Selifthen: select_kind
| Selifelse: select_kind
| Selloop: select_kind.

Definition selector := list select_kind.


Definition select_stmt_aux (sel: select_kind) (stmt: option statement) : option statement :=
  match sel, stmt with
  | Selseqleft, Some (Ssequence s1 s2) => Some s1
  | Selseqright, Some (Ssequence s1 s2) => Some s2
  | Selifthen, Some (Sifthenelse _ s1 s2) => Some s1
  | Selifelse, Some (Sifthenelse _ s1 s2) => Some s2
  | Selloop, Some (Sloop s) => Some s
  | _, _ => None
  end.

Definition select_stmt (stmt: statement) (sel: selector) : option statement :=
  fold_right select_stmt_aux (Some stmt) sel.

(* (** Maybe we can use fold_right to implement select_stmt and reverse *)
(* the selectors to simplify the proof *) *)
(* Fixpoint select_stmt (stmt: statement) (sel: selector) : option statement := *)
(*   match sel, stmt with *)
(*   | nil, _ => Some stmt *)
(*   | Selseqleft :: sel', Ssequence s1 s2 => select_stmt s1 sel' *)
(*   | Selseqright :: sel', Ssequence s1 s2 => select_stmt s2 sel' *)
(*   | Selifthen :: sel', Sifthenelse _ s1 s2 => select_stmt s1 sel' *)
(*   | Selifelse :: sel', Sifthenelse _ s1 s2 => select_stmt s2 sel' *)
(*   | Selloop :: sel', Sloop s => select_stmt s sel' *)
(*   | _, _ => None *)
(*   end. *)

(* Change in place the statement resided in this selector to an another
statement. And return the modified statement *)
(** TODO: we do not want to use [rev] *)
Fixpoint update_stmt_aux (root: statement) (sel: selector) (stmt: statement): option statement :=
  match sel, root with
  | nil, _ => Some stmt
  | Selseqleft :: sel', Ssequence s1 s2 =>
      match (update_stmt_aux s1 sel' stmt) with
      | Some s1' => Some (Ssequence s1' s2)
      | None => None
      end
  | Selseqright :: sel', Ssequence s1 s2 =>      
      match (update_stmt_aux s2 sel' stmt) with
      | Some s2' => Some (Ssequence s1 s2')
      | None => None
      end
  | Selifthen :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt_aux s1 sel' stmt) with
      | Some s1' => Some (Sifthenelse e s1' s2)
      | None => None
      end
  | Selifelse :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt_aux s2 sel' stmt) with
      | Some s2' => Some (Sifthenelse e s1 s2')
      | None => None
      end
  | Selloop :: sel', Sloop s =>
      match (update_stmt_aux s sel' stmt) with
      | Some s' => Some (Sloop s')
      | None => None
      end
  | _, _ => None
  end.

Definition update_stmt (root: statement) (sel: selector) (stmt: statement): option statement :=
  update_stmt_aux root (rev sel) stmt.


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


(** ** Genenrate CFG from a statement *)

(** * Translation state *)

Record generator: Type := mkstate {
  st_nextnode: node;
  st_code: rustcfg;
  st_wf: forall (pc: node), Plt pc st_nextnode \/ st_code!pc = None
}.


Inductive state_incr: generator -> generator -> Prop :=
  state_incr_intro:
    forall (s1 s2: generator),
    Ple s1.(st_nextnode) s2.(st_nextnode) ->
    (forall pc,
        s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl.
  intros. auto.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption.
  intros. generalize (H2 pc) (H3 pc). intuition congruence.
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


Definition error {A: Type} (msg: Errors.errmsg) : mon A := fun (s: generator) => Err msg.

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
  constructor; simpl.
  apply Ple_succ.
  intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto.
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

Fixpoint transl_stmt (end_node: node) (stmt: statement) (sel: selector) (succ: node) (cont: option node) (brk: option node) {struct stmt} : mon node :=
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
      do succ2 <- transl_stmt stmt2 (Selseqright :: sel) succ cont brk;
      do succ1 <- transl_stmt stmt1 (Selseqleft :: sel) succ2 cont brk;
      ret succ1
  | Sifthenelse e stmt1 stmt2 =>
      do n1 <- transl_stmt stmt1 (Selifthen :: sel) succ cont brk;
      do n2 <- transl_stmt stmt2 (Selifelse :: sel) succ cont brk;
      do n3 <- add_instr (Icond e n1 n2);
      ret n3
  | Sloop stmt =>
      do loop_jump_node <- reserve_instr;
      (* The succ in function body is loop_start *)
      do body_start <- transl_stmt stmt (Selloop :: sel) loop_jump_node (Some loop_jump_node) (Some succ);
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

(* compute the next selector in the execution (i.e., the starting
selector of the continuation) *)
Fixpoint next_sel (sel: selector) : selector :=
  match sel with
  | [] => []
  | Selseqleft :: sel1 => Selseqright :: sel1
  | Selseqright :: sel1 => next_sel sel1
  | Selifthen :: sel1 => next_sel sel1
  | Selifelse :: sel1 => next_sel sel1
  | Selloop :: sel1 => sel
  end.


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
| tr_Sreturn: forall pc sel endn e cont brk
    (SEL: cfg ! pc = Some (Isel sel endn))
    (STMT: select_stmt body sel = Some (Sreturn e)),
    tr_stmt body cfg (Sreturn e) pc endn cont brk endn
.

Inductive tr_fun (f: function) (nret: node) : rustcfg -> Prop :=
| tr_fun_intro: forall entry cfg
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (STMT: tr_stmt f.(fn_body) cfg f.(fn_body) entry nret None None nret)
    (RET: cfg ! nret = Some Iend),
    tr_fun f nret cfg.


(* tr_stmt matches transl_stmt *)
Lemma transl_stmt_charact: forall body sel stmt nret succ cont brk s s' n R,
    select_stmt body sel = Some stmt ->
    transl_stmt nret stmt sel succ cont brk s = Res n s' R ->
    tr_stmt body s'.(st_code) stmt n succ cont brk nret.
Admitted.


Lemma generate_cfg_charact: forall f entry cfg,
    generate_cfg f.(fn_body) = OK (entry, cfg) ->
    exists nret, tr_fun f nret cfg.
Proof.
  intros f entry cfg GEN.
  generalize GEN. intros GEN'.
  unfold generate_cfg in GEN.
  destruct (generate_cfg' (fn_body f) init_state) eqn: GCFG; try congruence.
  inv GEN. unfold generate_cfg' in GCFG.
  (** TODO: copy some monadInv from RTLgenspec.v *)
Admitted.


(** * A general framework for CFG compilation based on selectors *)

Local Open Scope error_monad_scope.

Definition set_stmt (pc: node) (body: statement) (sel: selector) (s: statement) : Errors.res statement :=
  match update_stmt body sel s with
  | Some body1 => OK body1
  | None =>
      Error [CTX pc; MSG " update_stmt error in set_stmt"]
  end.


Section TRANSL.

Context {AN: Type} {An: Type} (get_an: AN -> node -> An).
Context (ae: AN).
Context (transl_stmt: An -> statement -> Errors.res statement).

Definition transl_on_instr (src: statement) (pc: node) (instr: instruction) : Errors.res statement :=
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

Definition transl_on_cfg (src: statement) (cfg: rustcfg) : Errors.res statement :=
  PTree.fold (fun body pc instr => do body' <- body; transl_on_instr body' pc instr) cfg (OK src).

(* Translation relation between source statment and target statement *)

Section SPEC.

(* Dynamic elaboration of statement based on own_env *)
Inductive match_stmt (body: statement) (cfg: rustcfg) : statement -> statement -> node -> node -> option node -> option node -> node -> Prop :=
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

(** How to prove? added a visited list (list of pc) in match_stmt *)
Lemma transl_on_cfg_meet_spec: forall s ts cfg entry
    (CFG: generate_cfg s = OK (entry, cfg))
    (TRANSL: transl_on_cfg s cfg = OK ts),
  exists nret, match_stmt s cfg s ts entry nret None None nret.
Admitted.

End SPEC.

End TRANSL.
