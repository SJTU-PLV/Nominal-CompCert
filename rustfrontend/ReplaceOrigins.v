Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes RustlightBase RustIR.
Require Import Errors.

Import ListNotations.


(** ** Replace origins in RustIR *)


Definition find_elt {A: Type} (id: ident) (l: list (ident * A)) : option A :=
  match find (fun '(id', v) => ident_eq id id') l with
  | Some (_, v) => Some v
  | None => None
  end.

(** State and error monad for generating fresh identifiers. *)

Parameter first_unused_ident: unit -> ident.

Record generator : Type := mkgenerator {
  gen_next: origin;
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

Definition initial_generator (x: unit) : generator :=
  let fresh_id := first_unused_ident x in
  mkgenerator fresh_id.

Definition gensym : mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)))
        (Ple_succ (gen_next g)).

Open Scope gensym_monad_scope.

Fixpoint gensym_list (n: nat) : mon (list ident) :=
  match n with
  | O => ret nil
  | S n' =>
      do id <- gensym;
      do l <- gensym_list n';
      ret (id :: l)
  end.
    
(* replace origins in type with fresh origins *)

Fixpoint replace_origin_type (ty: type) : mon type :=
  match ty with
  | Treference _ mut ty' a =>
      do ty'' <- replace_origin_type ty';
      do org <- gensym;
      ret (Treference org mut ty'' a)
  | Tbox ty' a =>
      do ty'' <- replace_origin_type ty';
      ret (Tbox ty' a)
  | Tstruct orgs id a =>
      do orgs' <- gensym_list (length orgs);
      ret (Tstruct orgs' id a)
  | Tvariant orgs id a =>
      do orgs' <- gensym_list (length orgs);
      ret (Tvariant orgs' id a)
  | _ => ret ty
  end.
            
(* replace origins in variables *)

Definition replace_origin_var (var: ident * type) (acc: mon (list (ident * type))) : mon (list (ident * type)) :=
  do l <- acc;
  let (id, ty) := var in
  do ty' <- replace_origin_type ty;
  ret ((id, ty') :: l).

Definition replace_origin_vars (vars: list (ident * type)) : mon (list (ident * type)) :=
  fold_right replace_origin_var (ret nil) vars.


(* replace org with the the origin in rels *)
Definition replace_origin (rels: list origin_rel) (org: origin) : origin :=
  match find_elt org rels with
  | Some org' =>
      org'
  | None =>
      org
  end.

Fixpoint replace_origin_in_type (ty: type) (rels: list origin_rel) : type :=
  match ty with
  | Treference org mut ty a =>
      let ty' := replace_origin_in_type ty rels in
      Treference (replace_origin rels org) mut ty' a
  | Tbox ty a =>
      let ty' := replace_origin_in_type ty rels in
      Tbox ty' a
  | Tstruct orgs id a =>
      let orgs' := map (replace_origin rels) orgs in
      Tstruct orgs' id a
  | Tvariant orgs id a =>
      let orgs' := map (replace_origin rels) orgs in
      Tvariant orgs' id a
  | _ => ty
  end.


Section TYPE_ENV.

  Variable ce: composite_env.
  (* map from var/param to its type *)
  Variable e : PTree.t type.

  Fixpoint replace_origin_place' (p: place') : mon place' :=
    match p with
    | Plocal id ty =>
        match e!id with
        | Some ty' => ret (Plocal id ty')
        | None => error [CTX id; MSG "this variable has unknown type"]
        end
    | Pderef p ty =>
        do p' <- replace_origin_place' p;
        match typeof_place' p' with
        | Treference _ _ ty' _
        | Tbox ty' _ =>
            ret (Pderef p' ty')
        | _ =>
            error [CTX (local_of_place' p); MSG "dereference a non-deferencable type "]
        end
    | Pfield p fid ty =>
        do p' <- replace_origin_place' p;
        match typeof_place' p' with
        | Tstruct orgs id a =>
            match ce!id with
            | Some co =>
                match find (fun '(Member_plain fid' _) => Pos.eqb fid fid') co.(co_members) with
                | Some memb =>
                    let fty := type_member memb in
                    if Nat.eqb (length orgs) (length co.(co_generic_origins)) then
                      let rels := combine (co.(co_generic_origins)) orgs in
                      let fty' := replace_origin_in_type fty rels in
                      ret (Pfield p' fid fty')
                    else
                      error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    error [CTX id; CTX fid; MSG "cannot find this field (replace_origin_place')"]
                end
            | None =>
                error [CTX id; MSG "no such struct (replace_origin_place')"]
            end
        | _ => error [CTX (local_of_place' p); MSG "place is not a struct (replace_origin_place')"]
        end
    end.

  Definition replace_origin_place (p: place) : mon place :=
    match p with
    | Place p =>
        do p' <- replace_origin_place' p;
        ret (Place p')
    | Pdowncast p fid ty =>
        do p' <- replace_origin_place' p;
        match typeof_place' p' with
        | Tvariant orgs id a =>
            match ce!id with
            | Some co =>
                match find (fun '(Member_plain fid' _) => Pos.eqb fid fid') co.(co_members) with
                | Some memb =>
                    let fty := type_member memb in
                    if Nat.eqb (length orgs) (length co.(co_generic_origins)) then
                      let rels := combine (co.(co_generic_origins)) orgs in
                      let fty' := replace_origin_in_type fty rels in
                      ret (Pdowncast p' fid fty')
                    else
                      error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    error [CTX id; CTX fid; MSG "cannot find this constructor (replace_origin_place)"]
                end
            | None =>
                error [CTX id; MSG "no such variant (replace_origin_place)"]
            end
        | _ => error [CTX (local_of_place' p); MSG "place is not a variant (replace_origin_place)"]
        end
    end.

  (* type rewriting, does it matter? *)
  Fixpoint replace_origin_pure_expr (pe: pexpr) : mon pexpr :=
    match pe with
    | Eref _ mut p ty =>
        do org <- gensym;
        do p' <- replace_origin_place p;
        let ty' := Treference org mut (typeof_place p) (attr_of_type ty) in
        ret (Eref org mut p' ty')
    | Eplace p _ =>
        do p' <- replace_origin_place p;
        ret (Eplace p' (typeof_place p'))
    | Ecktag p id ty =>
        do p' <- replace_origin_place' p;
        ret (Ecktag p' id ty)
    | Eunop uop pe ty =>
        do pe' <- replace_origin_pure_expr pe;
        ret (Eunop uop pe' ty)
    | Ebinop bop pe1 pe2 ty =>
        do pe1' <- replace_origin_pure_expr pe1;
        do pe2' <- replace_origin_pure_expr pe2;
        ret (Ebinop bop pe1' pe2' ty)
    | _ => ret pe
    end.

  Definition replace_origin_expr (e: expr) : mon expr :=
    match e with
    | Emoveplace p ty =>
        do p' <- replace_origin_place p;
        ret (Emoveplace p' (typeof_place p'))
    | Epure pe =>
        do pe' <- replace_origin_pure_expr pe;
        ret (Epure pe')
    end.

  Fixpoint replace_origin_exprlist (l: list expr) : mon (list expr) :=
    match l with
    | nil => ret nil
    | e :: l' =>
        do e' <- replace_origin_expr e;
        do l'' <- replace_origin_exprlist l';
        ret (e' :: l'')
    end.
               
  
  Fixpoint replace_origin_statement (stmt: statement) : mon statement :=
    match stmt with
    | Sassign p e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        ret (Sassign p' e')
    | Sassign_variant p fid e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        ret (Sassign_variant p' fid e')
    | Sbox p e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        ret (Sbox p' e')
    | Sdrop p =>
        do p' <- replace_origin_place' p;
        ret (Sdrop p')
    | Scall p f l =>
        do p' <- replace_origin_place' p;
        do l' <- replace_origin_exprlist l;
        ret (Scall p' f l')
    | Sbuiltin p ef tyl al =>
        do p' <- replace_origin_place' p;
        do al' <- replace_origin_exprlist al;
        ret (Sbuiltin p' ef tyl al')                 
    | Sreturn (Some e) =>
        do e' <- replace_origin_expr e;
        ret (Sreturn (Some e'))
    | Ssequence s1 s2 =>
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        ret (Ssequence s1' s2')
    | Sifthenelse e s1 s2 =>
        do e' <- replace_origin_expr e;
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        ret (Sifthenelse e' s1' s2')
    | Sloop s =>
        do s' <- replace_origin_statement s;
        ret (Sloop s')
    | _ => ret stmt
    end.

End TYPE_ENV.

Open Scope error_monad_scope.

Definition replace_origin_function (ce: composite_env) (f: function) : Errors.res function :=
  let generic_orgs := f.(fn_generic_origins) in
  (* let next_org := Pos.succ (fold_left Pos.max generic_orgs 1%positive) in *)
  let gen := initial_generator tt in
  match replace_origin_vars f.(fn_vars) gen with
  | Err msg => Errors.Error msg
  | Res vars g _ =>
      let locals := f.(fn_params) ++ vars in
      if list_norepet_dec ident_eq (map fst vars) then
        let type_env := PTree_Properties.of_list locals in
        match replace_origin_statement ce type_env f.(fn_body) g with
        | Err msg => Errors.Error msg
        | Res stmt g' _ =>
            Errors.OK (RustIR.mkfunction
                         f.(fn_generic_origins)
                         f.(fn_origins_relation)                                  
                         f.(fn_return)
                         f.(fn_callconv)
                         f.(fn_params)
                         vars                             
                         stmt)
        end
      else Errors.Error [MSG "repeated idents in vars and params (replace_origin_function"]
  end.
        
