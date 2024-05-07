Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes RustlightBase RustIR.
Require Import Errors.
Require Import BorrowCheckDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on Polonius (dataflow analysis) *)

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at "; CTX pc; MSG " : "].

(** Replace origins in RustIR *)

(* TODO  *)

(** Initialization *)

Definition init_function (f: function) : AE.t :=
  let live_loans := fold_left (fun acc elt => LoanSet.add (Lextern elt) acc) f.(fn_generic_origins) LoanSet.empty in
  let init_origin_env := fold_left (fun acc elt =>
                                let os := Live (LoanSet.singleton (Lextern elt)) in
                                LOrgEnv.set elt os acc) f.(fn_generic_origins) (LOrgEnv.Top_except (PTree.empty LOrgSt.t)) in
  AE.State live_loans init_origin_env LAliasGraph.bot.

(* initialize the variable origins *)

Definition init_variables (ae: AE.t) (f: function) : AE.t :=
  match ae with
  | AE.Bot
  | AE.Err _ _ => ae
  | AE.State ls oe a =>
      let tys := map snd f.(fn_vars) in
      (* For all origins in the variable type, set its state to Live(∅) *)
      let orgs := concat (map origins_of_type tys) in
      let oe' := fold_left (fun acc elt => LOrgEnv.set elt LOrgSt.bot acc) orgs oe in
      AE.State ls oe' a
  end.

(** Transition *)

(* Support prefixes and support origins *)

Definition support_origins (p: place) : list origin :=
  let support_prefixes := p :: support_parent_paths p in
  fold_right (fun elt acc => match elt with
                          | Place (Pderef p' ty) =>
                              match typeof_place' p' with
                              | Treference org _ _ _ => org :: acc
                              | _ => acc
                              end
                          | _ => acc
                          end) nil support_prefixes.

Definition aggregate_origin_states (e: LOrgEnv.t) (orgs: list origin) : LOrgSt.t :=
  fold_left (fun acc elt => LOrgSt.lub acc (LOrgEnv.get elt e)) orgs LOrgSt.bot.
               
(* Transition of pure expression *)

Fixpoint transfer_pure_expr (pc: node) (live: LoanSet.t) (e: LOrgEnv.t) (pe: pexpr) : res (LoanSet.t * LOrgEnv.t) :=
  match pe with
  | Eplace p ty =>
      (* simple type check *)
      if type_eq (typeof_place p) ty then
        (* check all the loans in this place are not invalidated *)
        if valid_access e p then
          (* invalide origins contain loans relevant to [p] *)
          let ls := relevant_loans live p Adeep in
          let e' := invalidate_origins ls Aread e in
          OK (live, e')
        else
          Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG " in Eplace"])
      else
        Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Eplace"])
  | Eref org mut p ty =>
      (* simple type check *)
      match ty with
      | Treference org' mut' ty' _ =>
          if Pos.eqb org org' && mutkind_eq mut mut' && type_eq ty ty' then
            let ak := match mut with | Mutable => Awrite | Immutable => Aread end in
            (* check all the loans in this place are not invalidated *)
            if valid_access e p then
              (* invalide origins contain loans relevant to [p] *)
              let ls := relevant_loans live p Adeep in
              let e' := invalidate_origins ls ak e in
              (* add Lintern(mut,p) to live loans *)
              let live' := LoanSet.add (Lintern mut p) live in
              (* handle reborrow: add all the loans in the support
              prefix to org *)
              let support_orgs := support_origins p in
              (* aggregate the loans in the support origins *)
              let org_st := aggregate_origin_states e' support_orgs in
              match org_st with
              | Dead => Error (error_msg pc ++ [MSG "there is invalid origin in the support prefixes of ";CTX (local_of_place p)])
              | Live s =>
                  (* Don't forget to add {Lintern mut p} *)
                  let s' := LoanSet.add (Lintern mut p) s in
                  let e'' := LOrgEnv.set org (Live s') e' in
                  OK (live', e'')
              end
            else
              Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p)])
          else
            Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Eref"])
      | _ => Error (error_msg pc ++ [MSG "reference expression is not of reference type in Eref"])
      end
  | Ecktag p id _ =>
      (* simple type check *)
      match typeof_place' p with
      | Tvariant _ _ _ _ =>
          if valid_access e p then
            (* invalide origins contain loans relevant to [p] *)
            let ls := relevant_loans live p Ashallow in
            let e' := invalidate_origins ls Aread e in
            OK (live, e')
          else
            Error (error_msg pc ++ [MSG "access an invalid place "; CTX (local_of_place p); MSG "in Ecktag"])
      | _ => Error (error_msg pc ++ [MSG "type of operand is not Tvariant in Ecktag"])
      end
  | Eunop _ pe _ =>
      transfer_pure_expr pc live e pe
  | Ebinop _ pe1 pe2 _ =>
      do (live', e') <- transfer_pure_expr pc live e pe1;
      transfer_pure_expr pc live' e' pe2
  (* Other constants *)
  | _ => OK (live, e)
  end.                      

(* transfer expression *)

Definition transfer_expr (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (e: expr) : res (LoanSet.t * LOrgEnv.t) :=
  match e with
  | Emoveplace p ty =>
      (* simple type check *)
      if type_eq (typeof_place p) ty then
        (* check all the loans in this place are not invalidated *)
        if valid_access oe p then
          (* invalide origins contain loans relevant to [p] *)
          let ls := relevant_loans live p Adeep in
          (* move a place is a deep write access *)
          let oe' := invalidate_origins ls Awrite oe in
          OK (live, oe')
        else
          Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG " in Emoveplace"])
      else
        Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Emoveplace"])
  | Epure pe =>
      transfer_pure_expr pc live oe pe
  end.

Fixpoint transfer_exprlist (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (l: list expr) : res (LoanSet.t * LOrgEnv.t) :=
  match l with
  | [] => OK (live, oe)
  | e :: l' =>
      do (live', oe') <- transfer_expr pc live oe e;
      transfer_exprlist pc live' oe' l'
  end.


(* Flowing loans from source type to destination type *)

Inductive flow_kind : Type := ByVal | ByRef.

Fixpoint flow_loans (pc: node) (e: LOrgEnv.t) (g: LAliasGraph.t) (s d: type) (k: flow_kind) : res (LOrgEnv.t * LAliasGraph.t) :=
  match s,d with
  | Treference org1 _ ty1 _, Treference org2 _ ty2 _ =>
      do (e', g') <- flow_loans pc e g ty1 ty2 ByRef;      
      let g'' := match k with | ByVal => g' | ByRef => set_alias org1 org2 g' end in
      let st := LOrgSt.lub (LOrgEnv.get org1 e') (LOrgEnv.get org2 e') in
      (* flow st2 to st1 *)
      match st with
      | Live ls =>
          let e'' := set_loans_with_alias org1 ls e' g' in
          OK (e'', g')
      | _ =>
          Error (error_msg pc ++ [MSG "the src/dest origin is invalid in flow_loans"])
      end
  | Tbox ty1 _, Tbox ty2 _ =>
      flow_loans pc e g ty1 ty2 ByRef
  | Tstruct orgs1 _ id1 _, Tstruct orgs2 _ id2 _
  | Tvariant orgs1 _ id1 _, Tvariant orgs2 _ id2 _ =>
      if Nat.eqb (length orgs1) (length orgs2) then
        let orgs := combine orgs1 orgs2 in
        (* set alias between orgs1 and orgs2 *)
        let g' := match k with
                  | ByVal => g
                  | ByRef =>
                      fold_left
                        (fun acc '(org1, org2) => set_alias org1 org2 acc)
                        orgs g
                  end in
        (* flow loans from orgs1 to orgs2 *)
        let stl := map (fun '(org1, org2) => LOrgSt.lub (LOrgEnv.get org1 e) (LOrgEnv.get org2 e)) orgs in
        do e' <- fold_left
                    (fun acc '(org, st) =>
                       do acc' <- acc;
                       match st with
                       | Live ls =>
                           OK (set_loans_with_alias org ls acc' g')
                       | _ =>
                           Error (error_msg pc ++ [CTX org; MSG "the src/dest origin is invalid in flow_loans"])
                       end) (combine orgs1 stl) (OK e);
        OK (e', g')
      else Error (error_msg pc ++ [MSG "mismatch between the length of origins in type"; CTX id1])
  (* scalar type *)
  | _, _ => OK (e, g)
  end.
      
          
(* Shallow write a place *)

Definition shallow_write_place (f: function) (pc: node) (live: LoanSet.t) (e: LOrgEnv.t) (g: LAliasGraph.t) (p: place) : res (LOrgEnv.t * LAliasGraph.t) :=
  match p with
  | Place (Plocal id ty) =>
      if valid_access e p then
        let ls := relevant_loans live p Ashallow in
        let e' := invalidate_origins ls Awrite e in
        if in_dec ident_eq id (var_names f.(fn_vars)) then
          (* this place is a local variable, we can kill its loans *)          
          (* remove the loans and alias edges for the origin in the type of p *)
          let orgs := origins_of_type ty in
          (* remove loans *)
          let e'' := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs e' in
          (* remove alias *)
          let g' := fold_left (fun acc elt => remove_alias elt acc) orgs g in
          OK (e'', g')
        else
          OK (e', g)
      else
        Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG "in (shallow_write_place)"])
  | _ =>
      if valid_access e p then
        let ls := relevant_loans live p Ashallow in
        let e' := invalidate_origins ls Awrite e in
        OK (e', g)
      else
        Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG "in (shallow_write_place)"])
  end.
        
        
