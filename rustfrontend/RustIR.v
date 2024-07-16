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
Require Import Clight RustlightBase.
Require Import InitDomain.

Import ListNotations.

(** * Rust Intermediate Rrepresentation  *)

(** To compile Rustlight to RustIR, we replace the scopes (let stmt)
with StorageLive (StorageDead) statements, use AST to represent the
program, analyze the AST by first transforming it to CFG (using
selector technique) and insert explicit drop operations (so that the
RustIR has no ownership semantics) *)


(* The definitions of expression and place are the same as Rustlight *)

(** Statement: we add [Storagelive] and [Storagedead] to indicate the
lifetime of a local variable, because all the variables are declared
in the entry of function which is different from Rustlight. For now,
this two statements have no semantics. They are used for borrow
checking. We use [drop(p)] statement to indicate that we may need to
drop the content of [p] depending on the ownership environment. The
[Sreturn] returns the a predefined return variable instead of an
expression because we need to insert drop between the evaluation of
the returned expression and the return statement *)

Inductive statement : Type :=
| Sskip: statement                   (**r do nothing *)
| Sassign: place -> expr -> statement (**r assignment [place = rvalue] *)
| Sassign_variant : place -> ident -> ident -> expr -> statement (**r [place] = [ident(expr)] *)
| Sbox: place -> expr -> statement       (**r [place = Box::new(expr)]  *)
| Sstoragelive: ident -> statement       (**r id becomes avalible *)
| Sstoragedead: ident -> statement       (**r id becomes un-avalible *)
| Sdrop: place -> statement             (**r conditionally drop the place [p]. [p] must be an ownership pointer. *)
| Scall: place -> expr -> list expr -> statement (**r function call, p = f(...). It is a abbr. of let p = f() in *)
| Ssequence: statement -> statement -> statement  (**r sequence *)
| Sifthenelse: expr  -> statement -> statement -> statement (**r conditional *)
| Sloop: statement -> statement (**r infinite loop *)
| Sbreak: statement                      (**r [break] statement *)
| Scontinue: statement                   (**r [continue] statement *)
| Sreturn: option expr -> statement.      (**r [return] statement *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue: option ident;
  fn_return: type;
  fn_callconv: calling_convention;
  fn_vars: list (ident * type);
  fn_params: list (ident * type);
  fn_body: statement
}.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc
  end.

(* some helper function *)

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' =>
      match s' with
      | Sskip => makeseq_rec s l'
      | _ =>
          makeseq_rec (Ssequence s s') l'
      end
  end.

(* optimized version. But we do not consider the difficulty of simulation proof *)
Definition makeseq (l: list statement) : statement :=
  let s := makeseq_rec Sskip l in
  match s with
  | Ssequence Sskip s' => s'
  | _ => s
  end.


(** ** Definition of selector. It is the program pointer in AST-like program.  *)

Inductive select_kind : Type :=
| Selseqleft: select_kind
| Selseqright: select_kind
| Selifthen: select_kind
| Selifelse: select_kind
| Selloop: select_kind.

Definition selector := list select_kind.

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

(* Change in place the statement resided in this selector to an another
statement. And return the modified statement *)
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
      add_instr (Isel sel succ)
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
      do n2 <- transl_stmt stmt2 (sel ++ [Selifelse]) succ cont brk;
      do n3 <- add_instr (Icond e n1 n2);
      ret n3
  | Sloop stmt =>
      do loop_jump_node <- reserve_instr;
      (* The succ in function body is loop_start *)
      do body_start <- transl_stmt stmt (sel ++ [Selloop]) loop_jump_node (Some loop_jump_node) (Some succ);
      do _ <- update_instr loop_jump_node (Inop body_start);
      (* return loop_jump_node and return body_start are equivalent *)
      ret body_start
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

Close Scope cfg_monad_scope.
Local Open Scope error_monad_scope.

(** Genenrate drop map which maps composite id to its drop glue id *)


(* Extract composite id to drop glue id list *)
Definition extract_drop_id (g: ident * globdef fundef type) : ident * ident :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => (comp_id, glue_id)
      | None => (1%positive, glue_id)
      end
  | _ => (1%positive, glue_id)
  end.

Definition check_drop_glue (g: ident * globdef fundef type) : bool :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => true
      | None => false
      end
  | _ => false
  end.

Definition generate_dropm (p: program) :=
  let drop_glue_ids := map extract_drop_id (filter check_drop_glue p.(prog_defs)) in
  PTree_Properties.of_list drop_glue_ids.


(** General semantics definitions *)

Section SEMANTICS.

(** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.
      

(** Substate for member drop *)
Inductive drop_member_state : Type :=
| drop_member_comp
    (fid: ident)
    (fty: type)
    (co_ty: type)
    (tys: list type): drop_member_state   
| drop_member_box
    (fid: ident)
    (fty: type)
    (tys: list type): drop_member_state
.

(** Allocate memory blocks for function parameters/variables and build
the local environment *)
Inductive alloc_variables (ce: composite_env) : env -> mem ->
                                                list (ident * type) ->
                                                env -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables ce e m nil e m
| alloc_variables_cons:
  forall e m id ty vars m1 b1 m2 e2,
    Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
    alloc_variables ce (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
    alloc_variables ce e m ((id, ty) :: vars) e2 m2.


Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
    alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
    bind_parameters ge e m1 f.(fn_params) vargs m' ->
    function_entry ge f vargs m e m'.

Section SMALLSTEP.

Variable ge: genv.

(* list of ownership types which are the children of [ty] *)
Fixpoint drop_glue_children_types (ty: type) : list type :=
  match ty with
  | Tbox ty' =>
      drop_glue_children_types ty' ++ [ty]
  | Tstruct _ id 
  | Tvariant _ id  => ty::nil
  | _ => nil
  end.

(* It corresponds to drop_glue_for_member in Clightgen *)
Definition type_to_drop_member_state (fid: ident) (fty: type) : option drop_member_state :=
  if own_type ge fty then
    let tys := drop_glue_children_types fty in
    match tys with
    | nil => None
    | ty :: tys' =>
        match ty with       
        | Tvariant _ id
        | Tstruct _ id =>
            (* provide evidence for the simulation *)
            match ge.(genv_dropm) ! id with
            | Some _ =>
                Some (drop_member_comp fid fty ty tys')
            | None => None
            end
        | _ => Some (drop_member_box fid fty tys)
        end
    end
  else None.

(* Load the value of [ty1] with the address of the starting block
(with type ty_k) from [ty1;ty2;ty3;...;ty_k] where ty_n points to
ty_{n-1} *)
Inductive deref_loc_rec (m: mem) (b: block) (ofs: ptrofs) : list type -> val -> Prop :=
| deref_loc_rec_nil:
    deref_loc_rec m b ofs nil (Vptr b ofs)
| deref_loc_rec_cons: forall ty tys b1 ofs1 v,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 v ->
    deref_loc_rec m b ofs (ty::tys) v
.

Inductive deref_loc_rec_mem_error (m: mem) (b: block) (ofs: ptrofs) : list type -> Prop :=
| deref_loc_rec_error1: forall ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
| deref_loc_rec_error2: forall ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc_mem_error ty m b ofs ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
.


(* big step to recursively drop boxes [Tbox (Tbox (Tbox
...))]. (b,ofs) is the address of the starting block *)
Inductive drop_box_rec (b: block) (ofs: ptrofs) : mem -> list type -> mem -> Prop :=
| drop_box_rec_nil: forall m,
    drop_box_rec b ofs m nil m
| drop_box_rec_cons: forall m m1 m2 b1 ofs1 ty tys,
    (* (b1, ofs1) is the address of [ty] *)
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m (ty :: tys) m2
.

Inductive extcall_free_sem_mem_error: val -> mem -> Prop :=
| free_error1: forall (b : block) (lo : ptrofs) (m : mem),
    ~ Mem.valid_access m Mptr b (Ptrofs.unsigned lo - size_chunk Mptr) Readable ->
    extcall_free_sem_mem_error (Vptr b lo) m
| free_error2: forall (b : block) (lo sz : ptrofs) (m m' : mem),
    Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
    Ptrofs.unsigned sz > 0 ->
    ~ Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable ->
    extcall_free_sem_mem_error (Vptr b lo) m.


Inductive drop_box_rec_mem_error (b: block) (ofs: ptrofs) : mem -> list type -> Prop :=
| drop_box_rec_error1: forall m ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error2: forall m ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem_mem_error (Vptr b1 ofs1) m -> 
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error3: forall m m1 ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec_mem_error b ofs m1 tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
.

End SMALLSTEP.

End SEMANTICS.


