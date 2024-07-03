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


(** ** Operational semantics for RustIR after drop elabration *)

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

(** Continuation *)
  
Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: option place -> function -> env -> cont -> cont
| Kdropcall: ident -> val -> option drop_member_state -> members -> cont -> cont
.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop s k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (m: mem) : state
(* | Calldrop *)
(*     (* It is necessary for reducing the number of states transition *) *)
(*     (v: val) *)
(*     (ty: type) *)
(*     (k: cont)   *)
(*     (m: mem): state *)
| Dropstate
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (m: mem): state.              


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


Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state fid fty) membs k m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid fty fofs bf orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK (fofs, bf))
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (STRUCT: co2.(co_sv) = Struct),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fid2 fty2 fofs bf tag orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK (fofs, bf))
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr cb cofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co2.(co_members) (Int.unsigned tag) = Some (Member_plain fid2 fty2)),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) m)
| step_dropstate_box: forall b ofs id co fid fofs bf m m' tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK (fofs, bf))
    (DROPB: drop_box_rec b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m) E0
      (Dropstate id (Vptr b ofs) None membs k m')
| step_dropstate_return1: forall b ofs id m f e k,
    step_drop
      (Dropstate id (Vptr b ofs) None nil (Kcall None f e k) m) E0
      (State f Sskip k e m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k m)
.

(* Some functions similar to Clightgen and are used in semantics  *)

Fixpoint drop_for_place (p: place) (ty: type) : list statement :=
  match ty with
  | Tbox ty' =>
      drop_for_place (Pderef p ty') ty' ++ [Sdrop p]
  | Tstruct _ id 
  | Tvariant _ id  =>
      [Sdrop p]
  | _ => nil
  end.

Definition drop_for_member (p: place) (memb: member) : list statement :=
  match memb with
  | Member_plain fid ty =>      
      if own_type ge ty then
        drop_for_place (Pfield p fid ty) ty
      else
        nil
  end.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m1 m2 b ofs v v1,
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    step (State f (Sassign p e) k le m1) E0 (State f Sskip k le m2)
| step_assign_variant: forall f e p ty k le m1 m2 m3 b ofs ofs' v v1 tag bf co fid enum_id,
    ge.(genv_cenv) ! enum_id = Some co ->
    field_type fid co.(co_members) = OK ty ->
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr *)
    eval_expr ge le m1 e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (** different from normal assignment: update the tag and assign value *)
    ge.(genv_cenv) ! enum_id = Some co ->
    field_tag fid co.(co_members) = Some tag ->
    (* set the tag *)
    Mem.storev Mint32 m1 (Vptr b ofs) (Vint (Int.repr tag)) = Some m2 ->
    variant_field_offset ge fid co.(co_members) = OK (ofs', bf) ->
    (* set the value *)
    assign_loc ge ty m2 b (Ptrofs.add ofs (Ptrofs.repr ofs')) v1 m3 ->
    step (State f (Sassign_variant p enum_id fid e) k le m1) E0 (State f Sskip k le m3)
| step_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs,
    typeof_place p = Tbox ty ->
    (* Simulate malloc semantics to allocate the memory block *)
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* evaluate the expression after malloc to simulate*)
    eval_expr ge le m3 e v ->
    (* sem_cast the value to simulate function call in Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (* assign the value to the allocated location *)
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* assign the address to p *)
    eval_place ge le m4 p pb pofs ->
    assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5 ->
    step (State f (Sbox p e) k le m1) E0 (State f Sskip k le m5)

(** Small-step drop semantics *)
| step_drop_box: forall le m m' k ty b' ofs' f b ofs p
    (* We assume that drop(p) where p is box type has been expanded in
    drop elaboration (see drop_fully_own in ElaborateDrop.v) *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    step (State f (Sdrop p) k le m) E0 (State f Sskip k le m')
| step_drop_struct: forall m k orgs co id p b ofs f le
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: eval_place ge le m p b ofs),
    step
      (State f (Sdrop p) k le m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kcall None f le k) m)
| step_drop_enum: forall m k p orgs co id fid fty tag b ofs f le
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    step
    (State f (Sdrop p) k le m) E0
    (Dropstate id (Vptr b ofs) (type_to_drop_member_state fid fty) nil (Kcall None f le k) m)
| step_dropstate: forall id v s membs k m S E
    (SDROP: step_drop (Dropstate id v s membs k m) E S),
    step (Dropstate id v s membs k m) E S
    
| step_storagelive: forall f k le m id,
    step (State f (Sstoragelive id) k le m) E0 (State f Sskip k le m)
| step_storagedead: forall f k le m id,
    step (State f (Sstoragedead id) k le m) E0 (State f Sskip k le m)
         
| step_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels,    
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m a vf ->
    eval_exprlist ge le m al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    step (State f (Scall p a al) k le m) E0 (Callstate vf vargs (Kcall (Some p) f le k) m)

| step_internal_function: forall vf f vargs k m e m'
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None),
    function_entry ge f vargs m e m' ->
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')

(** Return cases *)
| step_return_0: forall e lb m1 m2 f k ,
    blocks_of_env ge e = lb ->
    (* drop the stack blocks *)
    Mem.free_list m1 lb = Some m2 ->
    (* return unit or Vundef? *)
    step (State f (Sreturn None) k e m1) E0 (Returnstate Vundef (call_cont k) m2)
| step_return_1: forall le a v v1 lb m1 m2 f k ,
    eval_expr ge le m1 a v ->
    (* sem_cast to the return type *)
    sem_cast v (typeof a) f.(fn_return) = Some v1 ->
    (* drop the stack blocks *)
    blocks_of_env ge le = lb ->
    Mem.free_list m1 lb = Some m2 ->
    step (State f (Sreturn (Some a)) k le m1) E0 (Returnstate v1 (call_cont k) m2)
(* no return statement but reach the end of the function *)
| step_skip_call: forall e lb m1 m2 f k,
    is_call_cont k ->
    blocks_of_env ge e = lb ->
    Mem.free_list m1 lb = Some m2 ->
    step (State f Sskip k e m1) E0 (Returnstate Vundef (call_cont k) m2)
         
| step_returnstate: forall p v b ofs ty m1 m2 e f k,
    eval_place ge e m1 p b ofs ->
    assign_loc ge ty m1 b ofs v m2 ->    
    step (Returnstate v (Kcall (Some p) f e k) m1) E0 (State f Sskip k e m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m,
    step (State f (Ssequence s1 s2) k e m)
      E0 (State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall f s k e m,
    step (State f Sskip (Kseq s k) e m)
      E0 (State f s k e m)
| step_continue_seq: forall f s k e m,
    step (State f Scontinue (Kseq s k) e m)
      E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
    step (State f Sbreak (Kseq s k) e m)
      E0 (State f Sbreak k e m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e m)
      E0 (State f (if b then s1 else s2) k e m)
| step_loop: forall f s k e m,
    step (State f (Sloop s) k e m)
      E0 (State f s (Kloop s k) e m)
| step_skip_or_continue_loop:  forall f s k e m x,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e m)
      E0 (State f s (Kloop s k) e m)
| step_break_loop:  forall f s k e m,
    step (State f Sbreak (Kloop s k) e m)
      E0 (State f Sskip k e m)
.


(** Open semantics *)

Inductive initial_state: c_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    val_casted_list vargs targs ->
    Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
    initial_state (cq vf (signature_of_type targs tres tcc) vargs m)
                  (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> c_query -> Prop:=
| at_external_intro: forall vf name sg args k m targs tres cconv orgs org_rels,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name sg) targs tres cconv) ->    
    at_external (Callstate vf args k m) (cq vf sg args m).

Inductive after_external: state -> c_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (cr v m')
      (Returnstate v k m').

Inductive final_state: state -> c_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (cr v m).

(* Definition of memory error state in RustIR *)

Inductive function_entry_mem_error (f: function) (vargs: list val) (m: mem) (e: env) : Prop :=
  | function_entry_mem_error_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters_mem_error ge e m1 f.(fn_params) vargs ->
      function_entry_mem_error f vargs m e.

(* Inductive step_mem_error : state -> Prop := *)
(* | step_assign_error1: forall f e p k le m, *)
(*     eval_place_mem_error ge le m p -> *)
(*     step_mem_error (State f (Sassign p e) k le m) *)
(* | step_assign_error2: forall f e p k le m b ofs, *)
(*     eval_place ge le m p b ofs -> *)
(*     eval_expr_mem_error ge le m e -> *)
(*     step_mem_error (State f (Sassign p e) k le m) *)
(* | step_assign_error3: forall f e p k le m b ofs v v1 ty, *)
(*     eval_place ge le m p b ofs -> *)
(*     eval_expr ge le m e v -> *)
(*     sem_cast v (typeof e) (typeof_place p) = Some v1 -> *)
(*     assign_loc_mem_error ge ty m b ofs v1 -> *)
(*     step_mem_error (State f (Sassign p e) k le m) *)
(* | step_assign_variant_error1: forall f e p k le m enum_id fid, *)
(*     eval_place_mem_error ge le m p -> *)
(*     step_mem_error (State f (Sassign_variant p enum_id fid e) k le m) *)
(* | step_assign_variant_error2: forall f e p k le m b ofs enum_id fid, *)
(*     eval_place ge le m p b ofs -> *)
(*     eval_expr_mem_error ge le m e -> *)
(*     step_mem_error (State f (Sassign_variant p enum_id fid e) k le m) *)
(* | step_assign_variant_error3: forall f e p k le m b ofs enum_id fid v, *)
(*     eval_place ge le m p b ofs -> *)
(*     eval_expr ge le m e v -> *)
(*     ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable -> *)
(*     step_mem_error (State f (Sassign_variant p enum_id fid e) k le m) *)
(* | step_assign_variant_error4: forall f e p k le m1 m2 b ofs ofs' enum_id fid v v1 ty co bf tag, *)
(*     ge.(genv_cenv) ! enum_id = Some co -> *)
(*     field_type fid co.(co_members) = OK ty -> *)
(*     eval_place ge le m1 p b ofs -> *)
(*     eval_expr ge le m1 e v -> *)
(*     sem_cast v (typeof e) ty = Some v1 -> *)
(*     field_tag fid co.(co_members) = Some tag -> *)
(*     (* set the tag *) *)
(*     Mem.storev Mint32 m1 (Vptr b ofs) (Vint (Int.repr tag)) = Some m2 -> *)
(*     field_offset ge fid co.(co_members) = OK (ofs', bf) -> *)
(*     (* set the value *) *)
(*     assign_loc_mem_error ge ty m2 b (Ptrofs.add ofs (Ptrofs.repr ofs')) v1 -> *)
(*     step_mem_error (State f (Sassign_variant p enum_id fid e) k le m1) *)
(* | step_box_error1: forall le e p k m f, *)
(*     eval_expr_mem_error ge le m e -> *)
(*     step_mem_error (State f (Sbox p e) k le m) *)
(* | step_box_error2: forall le e p k m1 m2 f b ty v v1, *)
(*     typeof_place p = Tbox ty -> *)
(*     eval_expr ge le m1 e v -> *)
(*     sem_cast v (typeof e) ty = Some v1 -> *)
(*     (* allocate the memory block *) *)
(*     Mem.alloc m1 0 (sizeof ge ty) = (m2, b) -> *)
(*     assign_loc_mem_error ge ty m2 b Ptrofs.zero v1 -> *)
(*     step_mem_error (State f (Sbox p e) k le m1) *)

(* | step_calldrop_box_error1: forall p le m k ty , *)
(*     typeof_place p = Tbox ty  -> *)
(*     eval_place_mem_error ge le m p -> *)
(*     step_mem_error (Calldrop p k le m) *)
(* | step_calldrop_box_error2: forall p le m k ty  b ofs,     *)
(*     typeof_place p = Tbox ty  -> *)
(*     eval_place ge le m p b ofs -> *)
(*     ~ Mem.valid_access m Mptr b (Ptrofs.unsigned ofs) Readable -> *)
(*     step_mem_error (Calldrop p k le m) *)
(* | step_calldrop_box_error3: forall p le m k ty  b b' ofs ofs',     *)
(*     typeof_place p = Tbox ty  -> *)
(*     eval_place ge le m p b ofs -> *)
(*     Mem.load Mptr m b (Ptrofs.unsigned ofs) = Some (Vptr b' ofs') -> *)
(*     ~ Mem.range_perm m b' (Ptrofs.unsigned ofs') ((Ptrofs.unsigned ofs') + sizeof ge ty) Cur Freeable -> *)
(*     step_mem_error (Calldrop p k le m) *)

(* | step_calldrop_enum_error1: forall p le m k  orgs co id, *)
(*     typeof_place p = Tvariant orgs id  -> *)
(*     ge.(genv_cenv) ! id = Some co -> *)
(*     eval_place_mem_error ge le m p -> *)
(*     step_mem_error (Calldrop p k le m) *)
(* | step_calldrop_enum_error2: forall p le m k  orgs co id b ofs, *)
(*     typeof_place p = Tvariant orgs id  -> *)
(*     ge.(genv_cenv) ! id = Some co -> *)
(*     eval_place ge le m p b ofs -> *)
(*     ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable -> *)
(*     step_mem_error (Calldrop p k le m) *)

                   
(* | step_call_error: forall f a al k le m  tyargs vf fd cconv tyres p orgs org_rels, *)
(*     classify_fun (typeof a) = fun_case_f tyargs tyres cconv -> *)
(*     eval_expr ge le m a vf -> *)
(*     eval_exprlist_mem_error ge le m al tyargs -> *)
(*     Genv.find_funct ge vf = Some fd -> *)
(*     type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv -> *)
(*     step_mem_error (State f (Scall p a al) k le m) *)
(* | step_internal_function_error: forall vf f vargs k m e *)
(*     (FIND: Genv.find_funct ge vf = Some (Internal f)), *)
(*     function_entry_mem_error f vargs m e -> *)
(*     step_mem_error (Callstate vf vargs k m) *)
(* | step_return_0_error: forall f k le m, *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f (Sreturn None) k le m) *)
(* | step_return_1_error1: forall f a k le m, *)
(*     eval_expr_mem_error ge le m a -> *)
(*     step_mem_error (State f (Sreturn (Some a)) k le m) *)
(* | step_return_2_error2: forall f a k le m v, *)
(*     eval_expr ge le m a v -> *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f (Sreturn (Some a)) k le m) *)
(* | step_skip_call_error: forall f k le m, *)
(*     is_call_cont k -> *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f Sskip k le m) *)
(* | step_returnstate_error1: forall p v m f k e, *)
(*     eval_place_mem_error ge e m p -> *)
(*     step_mem_error (Returnstate v (Kcall (Some p) f e k) m) *)
(* | step_returnstate_error2: forall p v m f k e b ofs ty, *)
(*     ty = typeof_place p -> *)
(*     eval_place ge e m p b ofs -> *)
(*     assign_loc_mem_error ge ty m b ofs v -> *)
(*     step_mem_error (Returnstate v (Kcall (Some p) f e k) m) *)
(* | step_ifthenelse_error:  forall f a s1 s2 k e m, *)
(*     eval_expr_mem_error ge e m a -> *)
(*     step_mem_error (State f (Sifthenelse a s1 s2) k e m) *)
(* .                    *)
         

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

