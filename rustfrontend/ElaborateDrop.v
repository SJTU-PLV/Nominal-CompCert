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

(* return [(p1,b1)] => b1 = true means that dropping p1 needs drop flag *)
Fixpoint elaborate_drop_for (mayinit mayuninit universe: Paths.t) (fuel: nat) (ce: composite_env) (p: place) : res (list (place * bool)) :=
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
                OK ((p, true) :: nil)
              else                         (* must initialized *)
                OK ((p, false) :: nil)
            else                (* must uninitialized *)
              OK nil
        | Tbox ty _ =>
            (* first drop *p if necessary *)
            do to_drops <- elaborate_drop_for (Pderef p ty);
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                OK ((p, true) :: to_drops)
              else                         (* must initialized *)
                OK ((p, false) :: to_drops)
            else                (* must uninitialized *)
              OK to_drops
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
                  do acc' <- acc;
                  do l <- elaborate_drop_for elt;
                  OK (acc' ++ l) in                
                fold_right rec (OK nil) children
            | None => Error (msg "Unfound struct id in composite_env: elaborate_drop_for")
            end
        | Tbox _ _ => Error (msg "Box does not exist in the universe set: elaborate_drop_for")
        | Tvariant _ _ => Error (msg "Variant cannot be split: elaborate_drop_for")
        | _ => OK nil
        end
  end.
  

(* Section WITH_INIT_UNINIT. *)

(* Variable (maybeInit maybeUninit: PathsMap.t). *)

(* Definition transf_stmt (ce: composite_env) (stmt: statement) := *)
(*   match stmt with *)
(*   | Sdrop p n => *)
(*       let id := local_of_place p in *)
(*       let mayinit := PathsMap.get id maybeInit in *)
(*       let mayuninit := PathsMap.get id maybeUninit in *)
(*       let universe := Paths.union mayinit mayuninit in *)
(*       let conditional := Paths.inter mayinit mayuninit in *)
     
