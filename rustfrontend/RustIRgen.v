Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import RustlightBase RustIR.


(** Translation from Rustlight to RustIR. The first step is
translating the AST style program into CFG style program which is
useful for analyzing. The second step is to generate the drop
operation based on the ownership semantics in the source program. *)

(** * Translation state *)

Record state: Type := mkstate {
  st_nextnode: node;
  st_code: code;
  st_wf: forall (pc: node), Plt pc st_nextnode \/ st_code!pc = None
}.


Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
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

(** ** The state and error monad *)

(* just copy from RTLgen *)

Inductive res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).


Definition error {A: Type} (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s: state) =>
    match f s with
    | OK a s' i => OK a s' i
    | Error _ => g s
    end.

(** Move path environment: a map from places (move path) to temporary variables  *)

Record move_path_env := {
    move_map: PTree.t (list (place * ident))
  }.

Definition move_path_index (me: move_path_env) (p: place) : option ident :=
  match me.(move_map) ! (local_of_place p) with
  | Some l =>
      match filter (fun elt => if place_eq (fst elt) p then true else false) l with
      | nil => None
      | (_,id) :: _ => Some id
      end
  | None => None
  end.



(** ** Operations on state *)

(** The initial state (empty CFG). *)

Remark init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty statement)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : state :=
  mkstate 1%positive (PTree.empty statement) init_state_wf.


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

Definition add_instr (i: statement) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    OK n
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
  fun (s: state) =>
  let n := s.(st_nextnode) in
  OK n
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
  forall (s: state) (n: node), { s.(st_code)!n = None } + { True }.
Proof.
  intros. case (s.(st_code)!n); intros. right; auto. left; auto.
Defined.

Definition update_instr (n: node) (i: statement) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode), check_empty_node s n with
    | left LT, left EMPTY =>
        OK tt
           (mkstate s.(st_nextnode) (PTree.set n i s.(st_code))
                    (update_instr_wf s n i LT))
           (update_instr_incr s n i LT EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.             

(* add drop statement *)
Definition add_drop (ce: composite_env) (p: place) (succ: node) : mon node :=
  match own_type own_fuel ce (typeof_place p) with
  | Some true => add_instr (Sdrop p succ)
  | Some false => ret succ
  | None => error (Errors.msg "Running out of fuel in own_type in add_drop.")
  end.

Definition add_instr_endscope (ce: composite_env) (local: ident) (ty: type) (succ: node): mon node :=
  do n1 <- add_instr (Sstoragedead local succ);
  do n2 <- add_drop ce (Plocal local ty) n1;
  ret n2.

(* when a list of locals go out of scope, add [Drop] and [Sstoragedead] for them *)
Definition add_endscope_list (ce: composite_env) (locals: list (ident * type)) (succ: node) : mon node :=
  fold_right (fun elt acc => do n <- acc; add_instr_endscope ce (fst elt) (snd elt) n) (ret succ) locals.

Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.

(** Translation of statement *)

Section COMPOSITE_ENV.

Variable (ce: composite_env).

Fixpoint transl_stmt (stmt: RustlightBase.statement) (succ: node) (live_vars: list (list (ident * type))) (cont: option node) (break: option node) {struct stmt} : mon node :=
    match stmt with
    | RustlightBase.Sskip =>
        add_instr (Sskip succ)
    | Slet id ty e stmt' =>
        do n1 <- add_instr_endscope ce id ty succ;
        do n2 <- transl_stmt stmt' n1 (list_list_cons (id,ty) live_vars) cont break;
        do n3 <- add_instr (Sassign (Plocal id ty) e n2);
        do n4 <- add_instr (Sstoragelive id n3);
        ret n4
    | RustlightBase.Sassign p e =>
        do n1 <- add_drop ce p succ;
        do n2 <- add_instr (Sassign p e n1);
        ret n2
    | Ssequence stmt1 stmt2 =>
        do succ2 <- transl_stmt stmt2 succ live_vars cont break;
        do succ1 <- transl_stmt stmt1 succ2 live_vars cont break;
        ret succ1
    | RustlightBase.Sifthenelse e stmt1 stmt2 =>
        do n1 <- transl_stmt stmt1 succ live_vars cont break;
        do n2 <- transl_stmt stmt2 succ live_vars cont break;
        do n3 <- add_instr (Sifthenelse e n1 n2);
        ret n3
    | Sloop stmt =>
        do loop_start <- reserve_instr;
        do body_start <- transl_stmt stmt succ (nil::live_vars) (Some loop_start) (Some succ);
        do _ <- update_instr loop_start (Sskip body_start);
        ret loop_start
    | Sbreak =>
        match break with
        | None =>
            error (Errors.msg "No loop outside the break")
        | Some brk =>
            match live_vars with
            | nil =>             (* nothing to drop *)
                do succ' <- add_instr (Sskip brk);
                ret succ'
            | locals :: _ =>
                do drop_start <- add_endscope_list ce locals brk;
                do succ' <- add_instr (Sskip drop_start);
                ret succ'
            end
        end
    | Scontinue =>
        match cont with
        | None =>
            error (Errors.msg "No loop outside the continue")
        | Some cont =>            
            match live_vars with
            | nil =>
                do succ' <- add_instr (Sskip cont);
                ret succ'
            | locals :: _ =>
                do drop_start <- add_endscope_list ce locals cont;
                do succ' <- add_instr (Sskip drop_start);
                ret succ'
            end
        end
    | RustlightBase.Scall p a al =>
        do succ' <- add_instr (Scall p a al succ);
        ret succ'
    | RustlightBase.Sreturn e =>
        do n1 <- add_instr (Sreturn e);
        let locals := concat live_vars in        
        do n2 <- add_endscope_list ce locals n1;
        do n3 <- add_instr (Sskip n2);
        ret n3
    end.


Fixpoint extract_vars (stmt: RustlightBase.statement) : list (ident * type) :=
  match stmt with
  | Slet id ty _ s =>
      (id,ty) :: extract_vars s
  | Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | RustlightBase.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Sloop s =>
      extract_vars s
  | _ => nil
  end.

(** Translation of function  *)

(* return the entry block and the temporary variables *)
Definition transl_fun (f: RustlightBase.function) : mon node :=
  (* add this return statement in case of there is no return in f *)
  do return_node <- add_instr (Sreturn None);
  (* add drops for the function parameter in return_block *)
  do drop_start <- add_endscope_list ce f.(RustlightBase.fn_params) return_node;
  do entry <- transl_stmt f.(RustlightBase.fn_body) drop_start (f.(RustlightBase.fn_params) :: nil) None None;
  (* add storagelive for parameters *)
  do entry' <- fold_right (fun elt acc => do n <- acc; add_instr (Sstoragelive (fst elt) n)) (ret entry) f.(RustlightBase.fn_params);
  ret entry'.


Definition transl_function (f: RustlightBase.function) : Errors.res function :=
  let vars := extract_vars f.(RustlightBase.fn_body) in
  let init_state := init_state in
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK entry s i =>
      Errors.OK (Build_function
                   f.(RustlightBase.fn_return)
                   f.(RustlightBase.fn_callconv)
                   f.(RustlightBase.fn_params)
                   vars
                   nil
                   s.(st_code)
                  entry)
  end.

Global Open Scope error_monad_scope.

Definition transl_fundef (fd: RustlightBase.fundef) : Errors.res fundef :=
  match fd with
  | Internal f => do tf <- transl_function f; Errors.OK (Internal tf)
  | External _ ef targs tres cconv => Errors.OK (External function ef targs tres cconv)
  end.

End COMPOSITE_ENV.


(** Translation of a whole program. *)

Definition transl_program (p: RustlightBase.program) : Errors.res RustIR.program :=
  do p1 <- transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
