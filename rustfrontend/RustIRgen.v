Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Rustlight RustIR.


(** Translation from Rustlight to RustIR. The main step is to generate
the drop operations and lifetime annotations in the end of a
variable. We also need to insert drops for those out-of-scope variable
in [break], [continue] and [return] *)


Section COMPOSITE_ENV.

Variable ce: composite_env.

(* Insert storagedead before drop for local variables *)
Definition gen_drops (local: bool) (l: list (ident * type)) : statement :=
  let drops := fold_right
                 (fun elt acc =>                    
                    if own_type ce (snd elt) then
                      if local then
                        (Sdrop (Plocal (fst elt) (snd elt))) :: acc
                      else (Ssequence (Sdrop (Plocal (fst elt) (snd elt))) (Sstoragedead (fst elt))) :: acc
                    else
                      if local then
                        (Sstoragedead (fst elt)) :: acc
                      else acc) nil l in
  makeseq drops.

(* [vars] is a stack of variable list. Eack stack frame corresponds to
a loop where these variables are declared. [params_drops] are the
statement for dropping the parameters *)
Fixpoint transl_stmt (params_drops: statement) (oretv: option place) (stmt: Rustlight.statement) (vars: list (list (ident * type))) : statement :=
  let transl_stmt := transl_stmt params_drops oretv in
  match stmt with
  | Rustlight.Sskip => Sskip
  | Slet id ty stmt' =>
      let s := transl_stmt stmt' (list_list_cons (id,ty) vars) in
      let drop := Sdrop (Plocal id ty) in
      if own_type ce ty then
        Ssequence (Sstoragelive id) (Ssequence s (Ssequence drop (Sstoragedead id)))
      else
        Ssequence (Sstoragelive id) (Ssequence s (Sstoragedead id))
  | Rustlight.Sassign p e =>
      let drop := Sdrop p in
      if own_type ce (typeof_place p) then
        Ssequence drop (Sassign p e)
      else               
        Sassign p e
  | Rustlight.Sassign_variant p enum_id fid e =>
      let drop := Sdrop p in
      if own_type ce (typeof_place p) then
        Ssequence drop (Sassign_variant p enum_id fid e)
      else
        Sassign_variant p enum_id fid e
  | Rustlight.Sbox p e =>
      Sbox p e
  | Rustlight.Scall p e el =>
      Scall p e el    
  | Rustlight.Ssequence s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Ssequence s1' s2'
  | Rustlight.Sifthenelse e s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Sifthenelse e s1' s2'
  | Rustlight.Sloop s =>
      let s := transl_stmt s (nil :: vars) in
      Sloop s        
  | Rustlight.Sbreak =>
      let drops := gen_drops true (hd nil vars) in
      Ssequence drops Sbreak
  | Rustlight.Scontinue =>
      let drops := gen_drops true (hd nil vars) in
      Ssequence drops Scontinue
  | Rustlight.Sreturn e =>
      let drops := gen_drops true (concat vars) in
      (* TODO: The fresh return variable is used to store the return value before the drops because the moved place in return expression may be dropped and the return value depends on this moved place. May be we can use some temporary variables to do this so that we do not need to protect this variable *)
      match oretv, e with
      | Some retv, Some e =>
          let s := Sassign retv e in
          let ty := typeof_place retv in
          let rete := if own_type ce ty then Emoveplace retv ty else (Epure (Eplace retv ty)) in
          makeseq (s :: drops :: params_drops :: (Sreturn (Some rete)) :: nil)
      | _, _ =>
          makeseq (drops :: params_drops :: (Sreturn None) :: nil)
      end
  end.

(* Add return to the end of the program *)
Fixpoint elaborate_return (stmt: Rustlight.statement) : Rustlight.statement :=
  match stmt with
  | Rustlight.Ssequence _ s =>
      elaborate_return s
  | Rustlight.Sreturn _ => stmt
  | _ => Rustlight.Ssequence stmt (Rustlight.Sreturn None)
  end.

Definition ret_var (ty: type) (v: ident) : option place :=
  if type_eq ty Tunit then None else Some (Plocal v ty).


Parameter fresh_atom : unit -> ident.

(* The main job is to extract the variables and translate the statement *)

Definition transl_function (f: Rustlight.function) : function :=
  let vars := extract_vars f.(Rustlight.fn_body) in
  (* drop statements for parameters *)
  let params_drops := gen_drops false f.(Rustlight.fn_params) in
  (* generate the return variable *)
  let retv := fresh_atom tt in
  let oretv := ret_var f.(Rustlight.fn_return) retv in
  (* no need to insert return *)
  (* let body := elaborate_return f.(Rustlight.fn_body) in *)
  let stmt' := transl_stmt params_drops oretv f.(Rustlight.fn_body) nil in
  (* add the return variable to variable list *)
  let vars' := match oretv with | Some v => (local_of_place v, typeof_place v)  :: vars | None => vars end in
  mkfunction f.(Rustlight.fn_generic_origins)
             f.(Rustlight.fn_origins_relation)
             f.(Rustlight.fn_drop_glue)                     
             f.(Rustlight.fn_return)
             f.(Rustlight.fn_callconv)
             vars'
             f.(Rustlight.fn_params)
             stmt'.

Definition transl_fundef (fd: Rustlight.fundef) : fundef :=
  match fd with
  | Internal f => (Internal (transl_function f))
  | External orgs org_rels ef targs tres cconv => External orgs org_rels ef targs tres cconv
  end.

End COMPOSITE_ENV.

Definition transl_program (p: Rustlight.program) : program :=
  let p1 := transform_program (transl_fundef p.(prog_comp_env)) p in
  {| prog_defs := AST.prog_defs p1;
    prog_public := AST.prog_public p1;
    prog_main := AST.prog_main p1;
    prog_types := prog_types p;
    prog_comp_env := prog_comp_env p;
    prog_comp_env_eq := prog_comp_env_eq p |}.
