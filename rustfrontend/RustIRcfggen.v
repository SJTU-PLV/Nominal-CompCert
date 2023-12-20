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
    (* (forall bid, *)
    (*     (** FIXME: exists stmts, s2.stmt = s1.stmt + stmts *) *)
    (*   s1.(st_code)!bid = None \/ s2.(st_code)!bid = s1.(st_code)!bid) -> *)
    state_incr s1 s2.


Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl. 
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextblock s2); assumption.
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

Definition init_state (t: terminator) : state :=
  mkstate 1%positive (PTree.empty basic_block) nil t.


(** Add IR statement in the current block *)

Remark add_instr_incr:
  forall s stmt,
    state_incr s (mkstate
                    s.(st_nextblock)
                    s.(st_code)
                    (stmt :: s.(st_stmts))
                    s.(st_term)).
Proof.
  constructor; simpl.
  apply Ple_refl.
  (* intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto. *)
Qed.


Definition add_instr (stmt: statement) : mon unit :=
  fun (s: state) =>
    OK tt (mkstate s.(st_nextblock) s.(st_code) (stmt :: s.(st_stmts)) s.(st_term)) (add_instr_incr s stmt).

(* add drop statement *)
Definition add_drop (ce: composite_env) (p: place) : mon unit :=
  match own_type own_fuel ce (typeof_place p) with
  | Some true => do _ <- add_instr (Sdrop p); ret tt
  | Some false => ret tt
  | None => error (Errors.msg "Running out of fuel in own_type in add_drop.")
  end.


Definition add_instr_endlet (ce: composite_env) (local: ident) (ty: type) : mon unit :=
  do _ <- add_instr (Sstoragedead local);
  do _ <- add_drop ce (Plocal local ty);
  ret tt.

(** Generate a new basic block  *)

Remark add_block_incr:
  forall s c stmts term,
    state_incr s (mkstate                  
                    (Pos.succ s.(st_nextblock))
                    c
                    stmts
                    term).
Proof.
  constructor; simpl.
  apply Ple_succ.
  (* intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto. *)
Qed.

(* very strange function: it build a basic block from the current
state, then use the new_term as the terminator for the next basic
block to be built, and return the latest block id *)
Definition add_block (cur: bb) (new_term: terminator) : mon bb :=
  fun (s: state) =>
    match plt cur s.(st_nextblock) with
    | left LT =>        
        let nb := Build_basic_block s.(st_stmts) s.(st_term) in
        let c := PTree.set cur nb s.(st_code) in
        OK s.(st_nextblock) (mkstate (Pos.succ s.(st_nextblock)) c nil new_term) (add_block_incr s c nil new_term)
    | _ =>
        Error (Errors.msg "RustIRgen.add_block")
    end.

Remark reserve_block_incr:
  forall s,
    state_incr s (mkstate (Pos.succ s.(st_nextblock)) s.(st_code) s.(st_stmts) s.(st_term)).
Proof.
  constructor; simpl.
  apply Ple_succ.
Qed.

Definition reserve_block : mon bb :=
  fun (s: state) =>
    OK s.(st_nextblock) (mkstate (Pos.succ s.(st_nextblock)) s.(st_code) s.(st_stmts) s.(st_term)) (reserve_block_incr s).


Remark construct_block_incr:
  forall s c stmts,
    state_incr s (mkstate                  
                    s.(st_nextblock)
                    c
                    stmts
                    s.(st_term)).
Proof.
  constructor; simpl.
  apply Ple_refl.
  (* intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto. *)
Qed.

Definition construct_block (cur: bb) : mon unit :=
  fun (s: state) =>
    match plt cur s.(st_nextblock) with
    | left LT =>        
        let nb := Build_basic_block s.(st_stmts) s.(st_term) in
        let c := PTree.set cur nb s.(st_code) in
        OK tt (mkstate s.(st_nextblock) c nil s.(st_term)) (construct_block_incr s c nil)
    | _ =>
        Error (Errors.msg "RustIRgen.construct_block")
    end.

Remark update_terminator_incr:
  forall s t,
    state_incr s (mkstate                  
                    s.(st_nextblock)
                    s.(st_code)
                    s.(st_stmts)
                    t).
Proof.
  constructor; simpl.
  apply Ple_refl.
Qed.

Definition update_terminator (t: terminator) : mon unit :=
  fun (s: state) =>
    OK tt (mkstate s.(st_nextblock) s.(st_code) s.(st_stmts) t) (update_terminator_incr s t).

Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.


Definition add_drop_list (ce: composite_env) (locals: list (ident * type)) : mon unit :=
  fold_right (fun elt acc => do _ <- acc; add_instr_endlet ce (fst elt) (snd elt)) (ret tt) locals.

(** Translation of expression  *)
(* unused: drop flag is generated in next pass *)
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

Section COMPOSITE_ENV.

Variable (ce: composite_env).

Fixpoint transl_stmt (stmt: RustlightBase.statement) (succ: bb) (live_vars: list (list (ident * type))) (cont: option bb) (break: option bb) {struct stmt} : mon bb :=
    match stmt with
    | Sskip =>
        ret succ
    | Slet id ty e stmt' =>
        do _ <- add_instr_endlet ce id ty;
        do succ' <- transl_stmt stmt' succ (list_list_cons (id,ty) live_vars) cont break;
        do _ <- add_instr (Sassign (Plocal id ty) e);
        do _ <- add_instr (Sstoragelive id);
        ret succ'
    | RustlightBase.Sassign p e =>
        do _ <- add_drop ce p;
        do _ <- add_instr (Sassign p e);
        ret succ
    | Ssequence stmt1 stmt2 =>
        do succ2 <- transl_stmt stmt2 succ live_vars cont break;
        do succ1 <- transl_stmt stmt1 succ2 live_vars cont break;
        ret succ1
    | Sifthenelse e stmt1 stmt2 =>
        do prev_succ1 <- add_block succ (Tgoto succ);
        do bb1 <- transl_stmt stmt1 prev_succ1 live_vars cont break;
        do prev_succ2 <- add_block bb1 (Tgoto succ);
        do bb2 <- transl_stmt stmt2 prev_succ2 live_vars cont break;
        do retb <- add_block bb2 (Tifthenelse e bb1 bb2);
        ret retb
    | Sloop stmt =>
        do loop_start <- reserve_block;
        do body_end <- add_block succ (Tgoto loop_start);
        do body_start <- transl_stmt stmt body_end (nil::live_vars) (Some loop_start) (Some succ);
        do _ <- construct_block body_start;
        do _ <- update_terminator (Tgoto body_start);
        do loop_start_prev <- add_block loop_start (Tgoto loop_start);
        ret loop_start_prev     (* loop start has no statements *)
    | Sbreak =>
        match break with
        | None =>
            error (Errors.msg "No loop outside the break")
        | Some brk =>            
            match live_vars with
            | nil =>             (* nothing to drop *)
                do prev <- add_block succ (Tgoto brk);
                ret prev
            | locals :: _ =>
                do drop_block <- add_block succ (Tgoto brk);
                (* insert drops in drop_block *)                              
                do _ <- add_drop_list ce locals;
                do prev <- add_block drop_block (Tgoto drop_block);
                ret prev
            end
        end
    | Scontinue =>
        match cont with
        | None =>
            error (Errors.msg "No loop outside the continue")
        | Some cont =>            
            match live_vars with
            | nil =>
                do prev <- add_block succ (Tgoto cont);
                ret prev
            | locals :: _ =>
                do drop_block <- add_block succ (Tgoto cont);
                (* insert drops in drop_block *)                              
                do _ <- add_drop_list ce locals;
                do prev <- add_block drop_block (Tgoto drop_block);
                ret prev
            end
        end
    | Scall p a al =>
        do call_block <- add_block succ (Tcall p a al succ);
        ret call_block
    | Sreturn e =>
        do return_block <- add_block succ (Treturn e);      
        let locals := concat live_vars in        
        do _ <- add_drop_list ce locals;
        (* Is it necessary to construct a new block? *)
        do prev <- add_block return_block (Tgoto return_block);
        ret prev
    end.


Fixpoint extract_vars (stmt: RustlightBase.statement) : list (ident * type) :=
  match stmt with
  | Slet id ty _ s =>
      (id,ty) :: extract_vars s
  | Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Sloop s =>
      extract_vars s
  | _ => nil
  end.

(** Translation of function  *)

(* return the entry block and the temporary variables *)
Definition transl_fun (f: RustlightBase.function) : mon bb :=
  do return_block <- reserve_block;
  (* add drops for the function parameter in return_block *)
  do _ <- fold_right (fun elt acc => do _ <- acc; add_drop ce (Plocal (fst elt) (snd elt))) (ret tt) f.(RustlightBase.fn_params);
  do return_prev <- add_block return_block (Tgoto return_block);
  do entry <- transl_stmt f.(RustlightBase.fn_body) return_prev (f.(RustlightBase.fn_params) :: nil) None None;
  do _ <- construct_block entry;
  ret entry.


Definition transl_function (f: RustlightBase.function) : Errors.res function :=
  let vars := extract_vars f.(RustlightBase.fn_body) in
  let init_state := init_state (Treturn None) in
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
