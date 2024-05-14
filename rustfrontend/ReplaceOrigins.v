Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes RustlightBase RustIR.
Require Import Errors.

Import ListNotations.
Local Open Scope error_monad_scope.

(** ** Replace origins in RustIR *)


Definition find_elt {A: Type} (id: ident) (l: list (ident * A)) : option A :=
  match find (fun '(id', v) => ident_eq id id') l with
  | Some (_, v) => Some v
  | None => None
  end.


Parameter fresh_atom: unit -> ident.

Definition gensym : ident := fresh_atom tt.

Fixpoint gensym_list (n: nat) : list ident :=
  match n with
  | O =>  nil
  | S n' =>
      let id := gensym in
      let l := gensym_list n' in
      (id :: l)
  end.
    
(* replace origins in type with fresh origins *)

Fixpoint replace_origin_type (ty: type) : type :=
  match ty with
  | Treference _ mut ty' a =>
      let ty'' := replace_origin_type ty' in
      let org := gensym in
      Treference org mut ty'' a
  | Tbox ty' a =>
      let ty'' := replace_origin_type ty' in
      Tbox ty' a
  | Tstruct orgs id a =>
      let orgs' := gensym_list (length orgs) in
      Tstruct orgs' id a
  | Tvariant orgs id a =>
      let orgs' := gensym_list (length orgs) in
      Tvariant orgs' id a
  | _ => ty
  end.
            
(* replace origins in variables *)

Definition replace_origin_var (var: ident * type) (l: list (ident * type)) : list (ident * type) :=
  let (id, ty) := var in
  let ty' := replace_origin_type ty in
  (id, ty') :: l.

Definition replace_origin_vars (vars: list (ident * type)) : list (ident * type) :=
  fold_right replace_origin_var nil vars.


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

  Fixpoint replace_origin_place' (p: place') : res place' :=
    match p with
    | Plocal id ty =>
        match e!id with
        | Some ty' => OK (Plocal id ty')
        | None => Error [CTX id; MSG "this variable has unknown type"]
        end
    | Pderef p ty =>
        do p' <- replace_origin_place' p;
        match typeof_place' p' with
        | Treference _ _ ty' _
        | Tbox ty' _ =>
            OK (Pderef p' ty')
        | _ =>
            Error [CTX (local_of_place' p); MSG "dereference a non-deferencable type "]
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
                      OK (Pfield p' fid fty')
                    else
                      Error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    Error [CTX id; CTX fid; MSG "cannot find this field (replace_origin_place')"]
                end
            | None =>
                Error [CTX id; MSG "no such struct (replace_origin_place')"]
            end
        | _ => Error [CTX (local_of_place' p); MSG "place is not a struct (replace_origin_place')"]
        end
    end.

  Definition replace_origin_place (p: place) : res place :=
    match p with
    | Place p =>
        do p' <- replace_origin_place' p;
        OK (Place p')
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
                      OK (Pdowncast p' fid fty')
                    else
                      Error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    Error [CTX id; CTX fid; MSG "cannot find this constructor (replace_origin_place)"]
                end
            | None =>
                Error [CTX id; MSG "no such variant (replace_origin_place)"]
            end
        | _ => Error [CTX (local_of_place' p); MSG "place is not a variant (replace_origin_place)"]
        end
    end.

  (* type rewriting, does it matter? *)
  Fixpoint replace_origin_pure_expr (pe: pexpr) : res pexpr :=
    match pe with
    | Eref _ mut p ty =>
        let org := gensym in
        do p' <- replace_origin_place p;
        let ty' := Treference org mut (typeof_place p) (attr_of_type ty) in
        OK (Eref org mut p' ty')
    | Eplace p _ =>
        do p' <- replace_origin_place p;
        OK (Eplace p' (typeof_place p'))
    | Ecktag p id ty =>
        do p' <- replace_origin_place' p;
        OK (Ecktag p' id ty)
    | Eunop uop pe ty =>
        do pe' <- replace_origin_pure_expr pe;
        OK (Eunop uop pe' ty)
    | Ebinop bop pe1 pe2 ty =>
        do pe1' <- replace_origin_pure_expr pe1;
        do pe2' <- replace_origin_pure_expr pe2;
        OK (Ebinop bop pe1' pe2' ty)
    | _ => OK pe
    end.

  Definition replace_origin_expr (e: expr) : res expr :=
    match e with
    | Emoveplace p ty =>
        do p' <- replace_origin_place p;
        OK (Emoveplace p' (typeof_place p'))
    | Epure pe =>
        do pe' <- replace_origin_pure_expr pe;
        OK (Epure pe')
    end.

  Fixpoint replace_origin_exprlist (l: list expr) : res (list expr) :=
    match l with
    | nil => OK nil
    | e :: l' =>
        do e' <- replace_origin_expr e;
        do l'' <- replace_origin_exprlist l';
        OK (e' :: l'')
    end.
               
  
  Fixpoint replace_origin_statement (stmt: statement) : res statement :=
    match stmt with
    | Sassign p e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        OK (Sassign p' e')
    | Sassign_variant p fid e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        OK (Sassign_variant p' fid e')
    | Sbox p e =>
        do p' <- replace_origin_place' p;
        do e' <- replace_origin_expr e;
        OK (Sbox p' e')
    | Sdrop p =>
        do p' <- replace_origin_place' p;
        OK (Sdrop p')
    | Scall p f l =>
        do p' <- replace_origin_place' p;
        do l' <- replace_origin_exprlist l;
        OK (Scall p' f l')
    | Sbuiltin p ef tyl al =>
        do p' <- replace_origin_place' p;
        do al' <- replace_origin_exprlist al;
        OK (Sbuiltin p' ef tyl al')                 
    | Sreturn (Some e) =>
        do e' <- replace_origin_expr e;
        OK (Sreturn (Some e'))
    | Ssequence s1 s2 =>
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        OK (Ssequence s1' s2')
    | Sifthenelse e s1 s2 =>
        do e' <- replace_origin_expr e;
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        OK (Sifthenelse e' s1' s2')
    | Sloop s =>
        do s' <- replace_origin_statement s;
        OK (Sloop s')
    | _ => OK stmt
    end.

End TYPE_ENV.

Open Scope error_monad_scope.

Definition replace_origin_function (ce: composite_env) (f: function) : Errors.res function :=
  let generic_orgs := f.(fn_generic_origins) in
  let vars := replace_origin_vars f.(fn_vars) in
  let locals := f.(fn_params) ++ vars in
  if list_norepet_dec ident_eq (map fst vars) then
    let type_env := PTree_Properties.of_list locals in
    do stmt <- replace_origin_statement ce type_env f.(fn_body);
    (* we need to check origins are no repeated *)
    Errors.OK (RustIR.mkfunction
                 f.(fn_generic_origins)
                     f.(fn_origins_relation)                                  
                         f.(fn_return)
                             f.(fn_callconv)
                                 f.(fn_params)
                                     vars                             
                                     stmt)
  else Errors.Error [MSG "repeated idents in vars and params (replace_origin_function"]
.
        
