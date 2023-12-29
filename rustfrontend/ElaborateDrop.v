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
Require Import Initialized.

Local Open Scope error_monad_scope.

(** Use the analysis from Initialized.v to elaborate the drop
statements. After this pass, the ownership semantics is removed. The
memory deallocation would be explicit and deterministic *)

(* return [(p,option id)] => id is the drop flag for p.  For now, we
do not consider fully owned or partial moved Box types and we do not
use monad to update the idents of drop flag *)
Fixpoint elaborate_drop_for (mayinit mayuninit universe: Paths.t) (fuel: nat) (ce: composite_env) (p: place) (next_flag: ident) (temps: list ident) : res ((list (place * option ident)) * (ident * list ident)) :=
  match fuel with
  | O => Error (msg "Run out of fuel in elaborate_drop_for")
  | S fuel' =>
      let elaborate_drop_for := elaborate_drop_for mayinit mayuninit universe fuel' ce in
      if Paths.mem p universe then
        match typeof_place p with        
        | Tstruct _ _
        | Tvariant _ _ => (* use drop function of this Tstruct (Tvariant) to drop p *)
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                OK (((p, Some next_flag) :: nil), (Pos.succ next_flag, next_flag :: temps))
              else                         (* must initialized *)
                OK (((p, None) :: nil), (next_flag, temps))
            else                (* must uninitialized *)
              OK (nil, (next_flag, temps))
        | Tbox ty _ =>
            (** TODO: we need to check if p is fully owned  *)
            (* first drop *p if necessary *)
            do (to_drops, flags) <- elaborate_drop_for (Pderef p ty) next_flag temps;
            let (next_flag', temps') := flags in
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                OK (((p, Some next_flag') :: to_drops), (Pos.succ next_flag', next_flag'::temps'))
              else                         (* must initialized *)
                OK (((p, None) :: to_drops), (next_flag', temps'))
            else                (* must uninitialized *)
              OK (to_drops, (next_flag', temps'))
        | _ => Error (msg "Normal types do not need drop: elaborate_drop_for")
        end
      else (* split p into its children and drop them *)
        match typeof_place p with
        | Tstruct id attr =>
            match ce!id with
            | Some co =>
                let children := map (fun elt => match elt with
                                             | Member_plain fid fty =>
                                                 Pfield p fid fty end)
                                  co.(co_members) in
                let rec elt acc :=
                  do (to_drops, flags) <- acc;
                  let '(next_flag', temps') := flags in
                  do (l, flags') <- elaborate_drop_for elt next_flag' temps';
                  let (next_flag'', temps'') := flags' in
                  OK ((to_drops ++ l), (next_flag'', temps'')) in                
                fold_right rec (OK (nil, (next_flag, temps))) children
            | None => Error (msg "Unfound struct id in composite_env: elaborate_drop_for")
            end
        | Tbox _ _ => Error (msg "Box does not exist in the universe set: elaborate_drop_for")
        | Tvariant _ _ => Error (msg "Variant cannot be split: elaborate_drop_for")
        | _ => OK (nil, (next_flag, temps))
        end
  end.
  

Section INIT_UNINIT.

Variable (maybeInit maybeUninit: PMap.t PathsMap.t).

(* Definition transf_stmt (ce: composite_env) (stmt: statement) := *)
(*   match stmt with *)
(*   | Sdrop p n => *)
(*       let id := local_of_place p in *)
(*       let mayinit := PathsMap.get id maybeInit in *)
(*       let mayuninit := PathsMap.get id maybeUninit in *)
(*       let universe := Paths.union mayinit mayuninit in *)
(*       let conditional := Paths.inter mayinit mayuninit in *)

Definition collect_elaborate_drops (ce: composite_env) (pc: node) (stmt: statement) (m: PTree.t (list (place * option ident))) (next_flag: ident) (temps: list ident) : res (PTree.t (list (place * option ident)) * (ident * list ident)):=
  match stmt with
  | Sdrop p _ =>
      let mayinit := maybeInit!!pc in
      let mayuninit := maybeUninit!!pc in
      if  PathsMap.beq mayinit PathsMap.bot && PathsMap.beq mayuninit PathsMap.bot then
        Error (msg "No initialized information: collect_elaborate_drops")
      else
        let id := local_of_place p in
        let init := PathsMap.get id mayinit in
        let uninit := PathsMap.get id mayuninit in
        let universe := Paths.union init uninit in
        do (l, flags) <- elaborate_drop_for init uninit universe own_fuel ce p next_flag temps;
        match m!id with
        | None =>
            OK (PTree.set id l m, flags)
        | _ =>
            Error (MSG "Double drop for variable: " :: CTX id :: nil)
        end        
  | _ => OK (m, (next_flag, temps))
  end
.

Definition collect_elaborate_drops_acc (ce: composite_env) (pcstmt: node * statement) (m: res (PTree.t (list (place * option ident)) * (ident * list ident))) : res (PTree.t (list (place * option ident)) * (ident * list ident)) :=
  do (m', flags) <- m;
  let (next_flag, temps) := flags in
  let (pc, stmt) := pcstmt in
  collect_elaborate_drops ce pc stmt m' next_flag temps.

End INIT_UNINIT.

(** State monad. We use the technique in [Inlining.v] to insert new
instructions *)

Record state : Type := mkstate {
  st_nextnode: positive;                (**r last used CFG node *)
  st_code: code                         (**r current CFG  *)
}.

Inductive sincr (s1 s2: state) : Prop :=
  Sincr (NEXTNODE: Ple s1.(st_nextnode) s2.(st_nextnode)).


Remark sincr_refl: forall s, sincr s s.
Proof.
  intros; constructor; extlia.
Qed.

Lemma sincr_trans: forall s1 s2 s3, sincr s1 s2 -> sincr s2 s3 -> sincr s1 s3.
Proof.
  intros. inv H; inv H0. constructor; extlia.
Qed.

(** Dependently-typed state monad, ensuring that the final state is
  greater or equal (in the sense of predicate [sincr] above) than
  the initial state. *)

Inductive res {A: Type} {s: state}: Type := R (x: A) (s': state) (I: sincr s s').

Definition mon (A: Type) : Type := forall (s: state), @res A s.

(** Operations on this monad. *)

Definition ret {A: Type} (x: A): mon A :=
  fun s => R x s (sincr_refl s).

Definition bind {A B: Type} (x: mon A) (f: A -> mon B): mon B :=
  fun s1 => match x s1 with R vx s2 I1 =>
              match f vx s2 with R vy s3 I2 =>
                R vy s3 (sincr_trans s1 s2 s3 I1 I2)
              end
            end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Definition initstate :=
  mkstate 1%positive (PTree.empty statement).

Program Definition set_instr (pc: node) (i: statement): mon unit :=
  fun s =>
    R tt
      (mkstate s.(st_nextnode) (PTree.set pc i s.(st_code)))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition add_instr (i: statement): mon node :=
  fun s =>
    let pc := s.(st_nextnode) in
    R pc
      (mkstate (Pos.succ pc) (PTree.set pc i s.(st_code)))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.

Program Definition reserve_nodes (numnodes: positive): mon node :=
  fun s =>
    R s.(st_nextnode)
      (mkstate (Pos.add s.(st_nextnode) numnodes) s.(st_code))
      _.
Next Obligation.
  intros; constructor; simpl; extlia.
Qed.


Program Definition ptree_mfold {A: Type} (f: positive -> A -> mon unit) (t: PTree.t A): mon unit :=
  fun s =>
    R tt
      (PTree.fold (fun s1 k v => match f k v s1 return _ with R _ s2 _ => s2 end) t s)
      _.
Next Obligation.
  apply PTree_Properties.fold_rec.
  auto.
  apply sincr_refl.
  intros. destruct (f k v a). eapply sincr_trans; eauto.
Qed.


Definition get_dropflag_temp (p: place) (m: PTree.t (list (place * option ident))) : option ident :=
  let id := local_of_place p in
  match m!id with
  | Some l =>
      match find (fun elt => place_eq p (fst elt)) l with
      | Some (_, optfid) => optfid
      | _ => None
      end
  | _ => None
  end.

Definition type_bool := Tint IBool Signed noattr.  

Definition Ibool (b: bool) := Econst_int (if b then Int.one else Int.zero) type_bool.

Definition insert_dropflag (id: ident) (flag: bool) (succ: node) : mon node :=
  add_instr (Sset id (Ibool flag) succ).

Definition insert_dropflag_option (id: option ident) (flag: bool) (succ: node) : mon node :=
  match id with
  | Some id =>
      add_instr (Sset id (Ibool flag) succ)
  | None => ret succ
  end.

Definition add_dropflag (p: place) (m: PTree.t (list (place * option ident))) (flag: bool) (succ: node) : mon node :=
  insert_dropflag_option (get_dropflag_temp p m) flag succ.


Definition add_dropflag_option (p: option place) (m: PTree.t (list (place * option ident))) (flag: bool) (succ: node) : mon node :=
  match p with
  | Some p => add_dropflag p m flag succ
  | _ => ret succ
  end.

Definition add_dropflag_option_list (l: list (option place)) (m: PTree.t (list (place * option ident))) (flag: bool) (succ: node) : mon node :=
  fold_left (fun acc elt => do n <- acc;
                         do n' <- add_dropflag_option elt m flag n;
                         ret n') l (ret succ).

Definition add_drop (p: place) (flag: option ident) (succ: node) : mon node :=
  match flag with
  | Some id =>     
      do n1 <- add_instr (Sdrop p succ);
      do n2 <- add_instr (Sifthenelse (Etempvar id type_bool) n1 succ);
      ret n2
  | None => ret succ
  end.                        

Section DROP_FLAGS.

Variable flagm: PTree.t (list (place * option ident)).

Definition expand_stmt (pc: node) (stmt: statement) : mon unit :=
  match stmt with
  | Sassign p be n =>
      (*  pred -> pc (Sassign) -> succ
      pred -> pc (Sskip) -> n3 -> n2 -> n1 (Sassign) -> succ *)
      do n1 <- add_instr stmt;
      (* set p's flag if necessary *)
      do n2 <- add_dropflag p flagm true n1;
      let deinit := collect_boxexpr be in
      (* set deinit *)
      do n3 <- add_dropflag_option deinit flagm false n2;
      (* use an empty node to replace stmt in pc, so that it's predecessor can goto it *)
      set_instr pc (Sskip n3)
  | Scall op _ el n =>
      (* pred -> pc (Scall) -> succ
         pred -> pc (Sskip) -> n3 ... (dropflags for el) -> n2 (Scall) -> n1 (dropflag for op) -> succ *)
      do n1 <- add_dropflag_option op flagm true n;
      do n2 <- add_instr stmt;
      let mvpaths := map collect_expr el in
      do n3 <- add_dropflag_option_list mvpaths flagm false n2;
      set_instr pc (Sskip n3)      
  | Sreturn (Some e) =>
      let deinit := collect_expr e in
      do n1 <- add_instr stmt;
      do n2 <- add_dropflag_option deinit flagm false n1;
      set_instr pc (Sskip n2)
  | Sdrop p n =>
      (** Core of elaboration of drop  *)
      let id := local_of_place p in
      match flagm!id with
      | None =>
          (* no need to drop p *)
          set_instr pc (Sskip n)
      | Some l =>
          (* pred -> pc -> succ
             pred -> pc (Sskip) -> n1 ... (drops) -> succ *)
          do n1 <- fold_left (fun acc elt => do n <- acc;
                                         do n' <- add_drop (fst elt) (snd elt) n;
                                         ret n') l (ret n);
          set_instr pc (Sskip n1)
      end
  | _ => set_instr pc stmt
  end.


Definition expand_function (f: function) : mon node :=
  (* reserve pc *)
  let maxpc := max_pc_function f in
  do _  <- reserve_nodes maxpc;
  (* set all drop flags to false *)
  let (_, flags) := split (PTree.elements flagm) in
  (** TODO: change fold_left to something like ptree_mfold  *)
  do entry <- fold_left (fun acc elt => do n <- acc;
                                    insert_dropflag_option (snd elt) false n)
               (concat flags) (ret f.(fn_entryblock));
  do _ <- ptree_mfold expand_stmt f.(fn_body);
  ret entry.
      
End DROP_FLAGS.

  

Definition transf_function (ce: composite_env) (f: function) : Errors.res function :=
  match analyze ce f with
  | Some (mayinit, mayuninit) =>
      let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
      let next_flag := fold_left Pos.max vars 1%positive in
      let stmts := PTree.elements f.(fn_body) in
      do (m, flags) <- fold_right (collect_elaborate_drops_acc mayinit mayuninit ce) (OK (PTree.empty (list (place * option ident)), (next_flag, nil))) stmts;
      let (_, temps) := flags in
      let temps_typs := combine temps (repeat type_bool (length temps)) in
      (** Now elaborate the drop statements and insert the update of drop flags *)
      let '(R entry s _) := expand_function m f initstate in
      if Nat.eqb (length f.(fn_temps)) 0%nat then             
        OK (Build_function f.(fn_return)
                        f.(fn_callconv)
                        f.(fn_params)
                        f.(fn_vars)
                        temps_typs
                        s.(st_code)
                            entry)
      else
        Error(msg "ElaborateDrop: Temporary variables are not empty")
  | _ =>
      Error(msg "ElaborateDrop: Initialized analysis errors")
  end.

Local Open Scope error_monad_scope.

Definition transf_fundef (ce: composite_env) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f => do tf <- transf_function ce f; Errors.OK (Internal tf)
  | External _ ef targs tres cconv => Errors.OK (External function ef targs tres cconv)
  end.


(** Translation of a whole program. *)

Definition transl_program (p: program) : Errors.res program :=
  do p1 <- transform_partial_program (transf_fundef p.(prog_comp_env)) p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
              prog_public := AST.prog_public p1;
              prog_main := AST.prog_main p1;
              prog_types := prog_types p;
              prog_comp_env := prog_comp_env p;
              prog_comp_env_eq := prog_comp_env_eq p |}.

