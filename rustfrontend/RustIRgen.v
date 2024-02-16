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

Definition gen_lives (l: list (ident * type)) : statement :=
  let lives := fold_right
                 (fun elt acc =>
                    if own_type ce (snd elt) then
                      (Sstoragelive (fst elt)) :: acc
                    else acc) nil l in
  makeseq lives.

(* [vars] is a stack of variable list. Eack stack frame corresponds to
a loop where these variables are declared. [params_drops] are the
statement for dropping the parameters *)
Fixpoint transl_stmt (params_drops: statement) (stmt: RustlightBase.statement) (vars: list (list (ident * type))) : statement :=
  let transl_stmt := transl_stmt params_drops in
  match stmt with
  | RustlightBase.Sskip => Sskip
  | Slet id ty stmt' =>
      let s := transl_stmt stmt' (list_list_cons (id,ty) vars) in
      let drop := Sdrop (Plocal id ty) in
      if own_type ce ty then
        Ssequence (Sstoragelive id) (Ssequence s (Ssequence drop (Sstoragedead id)))
      else
        Ssequence (Sstoragelive id) s
  | RustlightBase.Sassign p e =>
      Sassign p e
  | RustlightBase.Sbox p e =>
      Sbox p e
  | RustlightBase.Scall p e el =>
      Scall p e el
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
      makeseq (drops :: params_drops :: (Sreturn e) :: nil)
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


(* The main job is to extract the variables and translate the statement *)

Definition transl_function (f: RustlightBase.function) : function :=
  let vars := extract_vars f.(RustlightBase.fn_body) in
  (* drop statements for parameters *)
  let params_drops := gen_drops f.(RustlightBase.fn_params) in
  let params_live := gen_lives f.(RustlightBase.fn_params) in
  let body := elaborate_return f.(RustlightBase.fn_body) in
  let stmt' := transl_stmt params_drops body nil in
  let stmt'' := Ssequence params_live stmt' in
  mkfunction f.(RustlightBase.fn_return)
             f.(RustlightBase.fn_callconv)
             vars
             f.(RustlightBase.fn_params)
             stmt''.

Definition transl_fundef (fd: RustlightBase.fundef) : fundef :=
  match fd with
  | Internal f => (Internal (transl_function f))
  | External _ ef targs tres cconv => External function ef targs tres cconv
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
