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
  st_nexttemps: ident;
  st_nextblock: bb;
  st_code: cfg;
  st_stmts: list statement;
  st_term: terminator                        
  (* st_wf: forall (bid: bb), Plt bid st_nextblock \/ st_code!bid = None *)
}.


Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_nextblock) s2.(st_nextblock) ->
    Ple s1.(st_nexttemps) s2.(st_nexttemps) ->
    (* (forall bid, *)
    (*     (** FIXME: exists stmts, s2.stmt = s1.stmt + stmts *) *)
    (*   s1.(st_code)!bid = None \/ s2.(st_code)!bid = s1.(st_code)!bid) -> *)
    state_incr s1 s2.


Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl. apply Ple_refl. (* intros; auto. *)
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextblock s2); assumption.
  apply Ple_trans with (st_nexttemps s2); assumption.
  (* intros. generalize (H3 bid) (H5 bid). intuition congruence. *)
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

Definition init_state (idents: list ident) (t: terminator) : state :=
  mkstate (fold_right Pos.max 1%positive idents) 1%positive (PTree.empty basic_block) nil t.


(** Add IR statement in the current block *)

Remark add_instr_incr:
  forall s stmt,
    state_incr s (mkstate
                    s.(st_nexttemps)
                    s.(st_nextblock)
                    s.(st_code)
                    (stmt :: s.(st_stmts))
                    s.(st_term)).
Proof.
  constructor; simpl.
  apply Ple_refl.
  apply Ple_refl.
  (* intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto. *)
Qed.


Definition add_instr (stmt: statement) : mon unit :=
  fun (s: state) =>
    OK tt (mkstate s.(st_nexttemps) s.(st_nextblock) s.(st_code) (stmt :: s.(st_stmts)) s.(st_term)) (add_instr_incr s stmt).

Definition add_instr_endlet (local_end: option ident) : mon unit :=
  match local_end with
  | Some id =>
      do _ <- add_instr (Sstoragedead id);
      (** TODO: insert drop *)
      ret tt
  | _ => ret tt
  end.


(** Generate a new basic block  *)

Remark add_block_incr:
  forall s c stmts term,
    state_incr s (mkstate
                    s.(st_nexttemps)
                    (Pos.succ s.(st_nextblock))
                    c
                    stmts
                    term).
Proof.
  constructor; simpl.
  apply Ple_succ.
  apply Ple_refl.
  (* intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto. *)
Qed.

(* very strange function: it build a basic block from the current
state, then use the new_term as the terminator for the next basic
block to be built, and return the latest block id *)
Definition add_block (new_term: terminator) : mon bb :=
  fun (s: state) =>
    let n := s.(st_nextblock) in
    let nb := Build_basic_block s.(st_stmts) s.(st_term) in
    let c := PTree.set n nb s.(st_code) in
    OK n (mkstate s.(st_nexttemps) (Pos.succ s.(st_nextblock)) c nil new_term) (add_block_incr s c nil new_term).


(** Translation of expression  *)

Fixpoint transl_expr (me: move_path_env) (e: expr) : mon (list statement) :=
  match e with
  | Eplace Move p ty =>
      match move_path_index me p with
      | Some id =>
          ret ((Sset id (Econst_int Int.zero (Tint IBool Signed noattr))) :: nil)
      | _ => ret nil
      end
  | Eunop _ e ty => transl_expr me e
  | Ebinop _ e1 e2 ty =>
      do stmts1 <- transl_expr me e1;
      do stmts2 <- transl_expr me e2;
      ret (stmts1 ++ stmts2)
  | _ => ret nil
  end.
             
 

(** Translation of statement *)

Fixpoint transl_stmt (me: move_path_env) (stmt: RustlightBase.statement) (succ: bb) (local_end: option ident) {struct stmt} : mon bb :=
  fun (s: state) =>
    do _ <- add_instr_endlet local_end;
    match stmt with
    | Sskip =>
        ret succ
    | Slet id ty e stmt' =>
        do succ' <- transl_stmt me stmt' succ (Some id);
        do _ <- add_instr (Sassign (Plocal id ty) e);
        do _ <- add_instr (Sstoragelive id);
        ret succ'
    | Ssequence stmt1 stmt2 =>
        do succ2 <- transl_stmt me stmt2 succ None;
        do succ1 <- transl_stmt me stmt1 succ2 None;
        ret succ1
    | Sifthenelse e stmt1 stmt2 =>
        do prev_succ1 <- add_block (Tgoto succ);
        do bb1 <- transl_stmt me stmt1 prev_succ1 None;
        do prev_succ2 <- add_block (Tgoto succ);
        do bb2 <- transl_stmt me stmt2 prev_succ2 None;
        do retb <- add_block (Tifthenelse e bb1 bb2);
        ret retb
    | Sloop stmt1 stmt2 =>
        (** Very Hard !  *)
            
(** Translation of function  *)

(* return the entry block and the temporary variables *)
Definition transl_fun (f: RustlightBase.function) : mon (bb * list (ident * type)) :=
  



Definition transl_function (f: RustlightBase.function) : Errors.res function :=
  do vars <- extract_vars f.(fn_body);
  let init_state := init_state (map fst (vars ++ f.(fn_params))) in
  match transl_fun f init_state with

                        


  
  
