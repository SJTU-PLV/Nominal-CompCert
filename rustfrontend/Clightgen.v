Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Kildall.
Require Import Clight.
Require Import RustlightBase RustIR.


(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * Ctypes.type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.


Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.

Definition initial_generator (x: ident) : generator :=
  mkgenerator x nil.

Definition gensym (ty: Ctypes.type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).
  

Fixpoint place_to_cexpr (p: place) : Clight.expr :=
  match p with
  | Plocal id ty =>      
      Evar id (to_ctype ty)
  | Pfield p' fid ty =>
      Efield (place_to_cexpr p') fid (to_ctype ty)
  | Pderef p' ty =>
      Ederef (place_to_cexpr p') (to_ctype ty)
  end.

Definition get_variant_tag (ce: Ctypes.composite_env) (id:ident) :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some tag
      | _, _ => None
      end
  | _ => None
  end.

Definition get_variant_body (ce: Ctypes.composite_env) (id:ident) :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some body
      | _, _ => None
      end
  | _ => None
  end.

          

Fixpoint expr_to_cexpr (ce: Ctypes.composite_env) (e: expr) : option Clight.expr :=
  match e with
  | Econst_int i ty => Some (Clight.Econst_int i (to_ctype ty))
  | Econst_float f ty => Some (Clight.Econst_float f (to_ctype ty))
  | Econst_single f ty => Some (Clight.Econst_single f (to_ctype ty))
  | Econst_long l ty => Some (Clight.Econst_long l (to_ctype ty))
  | Eplace _ p _ => Some (place_to_cexpr p)
  | Eget _ p fid ty =>
      (** FIXME: how to translate the get expression? *)
      match typeof_place p with
      | Tvariant id _ =>
          match get_variant_body ce id with
          | Some id' =>
              Some (Efield (Efield (place_to_cexpr p) id' (Ctypes.Tstruct id noattr)) fid (to_ctype ty))
          | _ => None
          end
      | _ => None
      end
  | Ecktag p fid ty =>
      (** TODO: how to get the tagz from ctypes composite env? or still use Rust composite env? *)      
      (* match typeof_place p with *)
      (* | Tvariant id _ => *)
      (*     match get_variant_body ce id,  with *)
      (*     | Some tagid => *)
      (*         Some (Ebinop Oeq (Efield (place_to_cexpr p) tagid type_int32s)  *)
      (* Ebinop Oeq (Efield (place_to_cexpr) *)
      None
  | Etempvar id ty =>
      Some (Clight.Etempvar id (to_ctype ty))
  | Eunop uop e ty =>
      match expr_to_cexpr ce e with
      | Some e' =>                          
          Some (Clight.Eunop uop e' (to_ctype ty))
      | None => None
      end
  | Ebinop binop e1 e2 ty =>
      match expr_to_cexpr ce e1, expr_to_cexpr ce e2 with
      | Some e1', Some e2' =>
          Some (Clight.Ebinop binop e1' e2' (to_ctype ty))
      | _, _ => None
      end
  end.

Section MALLOC_FREE.

Local Open Scope gensym_monad_scope.
  
Variable (malloc_id free_id: ident).

Fixpoint transl_boxexpr (ce: Ctypes.composite_env) (be: boxexpr) : mon (list Clight.statement * Clight.expr) :=
  match be with
  | Box be' =>
      do (stmts, e) <- transl_boxexpr ce be';
      let ty := to_ctype (typeof_boxexpr be) in
      do temp <- gensym ty;
      (* How to construct the expression for malloc function? *)
      let ty' := to_ctype (typeof_boxexpr be') in
      let malloc := (Evar malloc_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer ty' noattr) Ctypes.Tnil) (Tpointer ty' noattr) cc_default)) in
      ret (stmts ++ ((Clight.Scall (Some temp) malloc (e::nil)) :: nil), Clight.Etempvar temp ty)
  | Bexpr e =>
      match expr_to_cexpr ce e with
      | Some e' =>
          ret (nil, e')
      | None =>
          error (msg "Error in transl_boxexpr")
      end
  end.


Section STMT_FROM_EB.

Variable to_cexpr : (expr + place) -> Clight.expr.

Variable extended: PMap.t bool.

Variable unvisited: PMap.t bool.

Variable label_of_node : positive -> label.

(* return the next extened basic block (TODO: Is there always no more
than one extended basic block) and the constructed statement *)

Fixpoint build_stmt_until_extended_block (fuel: nat) (code: PTree.t statement) (pc: node) : mon (option node * Clight.statement) :=
  match fuel with
  | O => error (msg "Running out of fuel in: build_stmt_until_extended_block")
  | S fuel ' =>
  match code!pc with
  | None => Error (msg "Invalid control flow graph: build_stmt_until_extened_block")
  | Some stmt =>
      match stmt with
      | Sifthenelse e n1 n2 =>
          (* check if n1 and n2 are extened blocks *)
          do (r1, s1) <-
               (if extended!!n1 then
                  if unvisited!!n1 then
                    error (msg "Body entry of if statement has extened block: build_stmt_until_extened_block")                                       
                  else
                    ret (None, Sgoto (label_of_node n1))
                else
                  build_stmt_until_extended_block code n1) in
          do (r2, s2) <-
               (if extended!!n2 then
                  if unvisited!!n2 then
                    error (msg "Body entry of if statement has extened block: build_stmt_until_extened_block")
                  else
                    ret (None, Sgoto (label_of_node n2))
                else
                  build_stmt_until_extended_block code n2) in
          match r1,r2 with
          | Some r1, Some r2 =>              
              (* pc - n1 -* r2 
                    - n2 -* r1 *)  
              if Pos.eqb r1 r2 then
                ret (r, Clight.Sifthenelse (to_cexpr (inr e)) s1 s2)
              else 
                error (msg "Two case of if statement renach two different blocks: build_stmt_until_extened_block")
          | Some r1, None =>
              ret (r1, Clight.Sifthenelse (to_cexpr (inr e)) s1 s2)
          | None, Some r2 =>
              ret (r2, Clight.Sifthenelse (to_cexpr (inr e)) s1 s2)
          | None, None =>
              ret (None, Clight.Sifthenelse (to_cexpr (inr e)) s1 s2)
          end
      | Sskip n =>
          if extended n then
            if visited n then
              OK (None, Clight.Sgoto (label_of_node n))
            else 
              OK (Some n, Clight.Sskip)
          else
            build_stmt_until_extended_block code n
      | Sassign p be n =>
          if extended n then
            if visited n then
              OK (None, Clight.Sgoto (label_of_node n))
            else 
              OK (Some n, Clight.Sskip)
          else
            let (r, s) := build_stmt_until_extended_block code n in
            match be with
            | Box be
            OK (r, Ssequence (Clight.Sassign (to_cexpr (inl p)) (to_cexpr (inr ))
.


End STMT_FROM_EB.

Fixpoint transl_extened_block (fuel: nat) (code: PTree.t statement) (extened: PMap.t bool) (unvisited: PMap.t bool) (pc: node)  : mon Clight.statement :=
  match fuel with
  | O => error (msg "Running out of fuel in transl_extended_block")
  | S fuel' =>
      let unvisited' := PMap.set pc false unvisited in
      do (optnext, stmt) <- build_stmt_until_extended_block extended unvisited fuel' pc code;
      match optnext with
      | Some next =>
          do stmt' <- transl_extened_block fuel' code extended unvisited';
          ret (Ssequence stmt stmt')
      | None =>
          ret stmt
      end
  end
              
          
                              

Definition make_extened_basic_block (entry: node) (preds: PTree.t (list positive)) : PTree.t bool :=
  PTree.fold (fun acc pc elt =>
                if peq pc entry then PTree.set pc true acc else
                  match preds!!!pc with
                  | nil => PTree.set pc false acc
                  | s :: nil =>
                      if peq s pc then PTree.set pc true acc else PTree.set pc false acc
                  | _ :: _ :: _ =>
                      PTree.set pc true acc
                  end) preds (PTree.empty bool).


(* top level function *)
Fixpoint transl_function (f: function) :=
  let vars := var_names (f.(fn_vars) ++ f.(fn_params) ++ f.(fn_temps)) in
  let next_temp := fold_left Pos.max vars 1%positive in
  let gen := initial_generator next_temp in
  (* compute the extended blocks *)
  let preds := make_predecessors successors in
  let extended := make_extened_basic_block f.(fn_entryblock) preds in
  let unvisited := extended in 
.
                              
