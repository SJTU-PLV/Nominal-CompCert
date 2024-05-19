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


(** Translation from Rustlight to RustIR. The main step is to generate
the drop operations and lifetime annotations in the end of a
variable. We also need to insert drops for those out-of-scope variable
in [break], [continue] and [return] *)


Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.

Section COMPOSITE_ENV.

Variable ce: composite_env.

Definition gen_drops (l: list (ident * type)) : statement :=
  let drops := fold_right
                 (fun elt acc =>
                    if own_type ce (snd elt) then
                      (Ssequence (Sdrop (Plocal (fst elt) (snd elt))) (Sstoragedead (fst elt))) :: acc
                    else acc) nil l in                
  makeseq drops.

(* [vars] is a stack of variable list. Eack stack frame corresponds to
a loop where these variables are declared. [params_drops] are the
statement for dropping the parameters *)
Fixpoint transl_stmt (params_drops: statement) (oretv: option place') (stmt: RustlightBase.statement) (vars: list (list (ident * type))) : statement :=
  let transl_stmt := transl_stmt params_drops oretv in
  match stmt with
  | RustlightBase.Sskip => Sskip
  | Slet id ty stmt' =>
      let s := transl_stmt stmt' (list_list_cons (id,ty) vars) in
      let drop := Sdrop (Plocal id ty) in
      if own_type ce ty then
        Ssequence (Sstoragelive id) (Ssequence s (Ssequence drop (Sstoragedead id)))
      else
        Ssequence (Sstoragelive id) (Ssequence s (Sstoragedead id))
  | RustlightBase.Sassign p e =>
      let drop := Sdrop p in
      if own_type ce (typeof_place' p) then
        Ssequence drop (Sassign p e)
      else               
        Sassign p e
  | RustlightBase.Sassign_variant p fid e =>
      let drop := Sdrop p in
      if own_type ce (typeof_place' p) then
        Ssequence drop (Sassign_variant p fid e)
      else               
        Sassign_variant p fid e
  | RustlightBase.Sbox p e =>
      Sbox p e
  | RustlightBase.Scall p e el =>
      Scall p e el
  | RustlightBase.Sbuiltin p ef tyl el =>
      Sbuiltin p ef tyl el            
  | RustlightBase.Ssequence s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Ssequence s1' s2'
  | RustlightBase.Sifthenelse e s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Sifthenelse e s1' s2'
  | RustlightBase.Sloop s =>
      let s := transl_stmt s (nil :: vars) in
      Sloop s        
  | RustlightBase.Sbreak =>
      let drops := gen_drops (hd nil vars) in
      Ssequence drops Sbreak
  | RustlightBase.Scontinue =>
      let drops := gen_drops (hd nil vars) in
      Ssequence drops Scontinue
  | RustlightBase.Sreturn e =>
      let drops := gen_drops (concat vars) in
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


Fixpoint extract_vars (stmt: RustlightBase.statement) : list (ident * type) :=
  match stmt with
  | Slet id ty s =>
      (id,ty) :: extract_vars s
  | RustlightBase.Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | RustlightBase.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | RustlightBase.Sloop s =>
      extract_vars s
  | _ => nil
  end.

Fixpoint elaborate_return (stmt: RustlightBase.statement) : RustlightBase.statement :=
  match stmt with
  | RustlightBase.Ssequence _ s =>
      elaborate_return s
  | RustlightBase.Sreturn _ => stmt
  | _ => RustlightBase.Ssequence stmt (RustlightBase.Sreturn None)
  end.

Definition ret_var (ty: type) (v: ident) : option place' :=
  if type_eq ty Tunit then None else Some (Plocal v ty).

(* The main job is to extract the variables and translate the statement *)

Definition transl_function (f: RustlightBase.function) : function :=
  let vars := extract_vars f.(RustlightBase.fn_body) in
  (* drop statements for parameters *)
  let params_drops := gen_drops f.(RustlightBase.fn_params) in
  (* generate the return variable *)
  let locals := var_names (vars ++ f.(RustlightBase.fn_params)) in
  let retv := Pos.succ (fold_left (fun acc elt => Pos.max acc elt) locals 1%positive) in
  let oretv := ret_var f.(RustlightBase.fn_return) retv in
  (* no need to insert return *)
  (* let body := elaborate_return f.(RustlightBase.fn_body) in *)
  let stmt' := transl_stmt params_drops oretv f.(RustlightBase.fn_body) nil in
  (* add the return variable to variable list *)
  let vars' := match oretv with | Some v => (local_of_place v, typeof_place v)  :: vars | None => vars end in
  mkfunction f.(RustlightBase.fn_generic_origins)
             f.(RustlightBase.fn_origins_relation)
             f.(RustlightBase.fn_return)
             f.(RustlightBase.fn_callconv)
             vars'
             f.(RustlightBase.fn_params)
             stmt'.

Definition transl_fundef (fd: RustlightBase.fundef) : fundef :=
  match fd with
  | Internal f => (Internal (transl_function f))
  | External _ orgs org_rels ef targs tres cconv => External function orgs org_rels ef targs tres cconv
  end.

End COMPOSITE_ENV.

Definition transl_program (p: RustlightBase.program) : program :=
  let p1 := transform_program (transl_fundef p.(prog_comp_env)) p in
  {| prog_defs := AST.prog_defs p1;
    prog_public := AST.prog_public p1;
    prog_main := AST.prog_main p1;
    prog_types := prog_types p;
    prog_comp_env := prog_comp_env p;
    prog_comp_env_eq := prog_comp_env_eq p |}.
