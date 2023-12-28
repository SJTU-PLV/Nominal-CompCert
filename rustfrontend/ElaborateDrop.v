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



Definition transf_function (ce: composite_env) (f: function) :=
  match analyze ce f with
  | Some mayinit, Some mayuninit =>
      let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
      let next_flag := fold_left Pos.max vars 0%positive in
      let stmts := PTree.elements f.(fn_body) in
      do (m, flags) <- fold_right (collect_elaborate_drops_acc mayinit mayuninit ce) (OK (PTree.empty (list (place * option ident)), (next_flag, nil))) stmts;
      let (_, temps) := flags in
      (** Now elaborate the drop statement and insert the update of
      drop flag in move or assign *)
      
  
     
