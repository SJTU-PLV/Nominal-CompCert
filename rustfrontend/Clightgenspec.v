Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight.
Require Import Rusttypes RustlightBase RustIR.
Require Import Clightgen.

Import ListNotations.

Section SPEC.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.  
Variable dropm: PTree.t ident.

(** TODO: define some relations between ce and tce *)
Variable tr_composite: composite_env -> Ctypes.composite_env -> Prop.


Inductive tr_stmt : statement -> Clight.statement -> Prop :=
| tr_trivial: forall s ts g,
    transl_stmt ce tce dropm s g = Res ts g ->
    tr_stmt s ts
| tr_box: forall p e stmt lhs e' temp temp_ty,
    temp_ty = Tpointer (to_ctype (typeof e)) noattr ->
    transl_Sbox ce tce temp temp_ty e = OK (stmt, e') ->
    place_to_cexpr tce p = OK lhs ->
    tr_stmt (Sbox p e) (Clight.Ssequence stmt (Clight.Sassign lhs e'))
| tr_call: forall p e l temp e' l' assign pe,
    expr_to_cexpr_list ce tce l = OK l' ->
    expr_to_cexpr ce tce e = OK e' ->
    place_to_cexpr tce p = OK pe ->
    assign = Clight.Sassign pe (Etempvar temp (to_ctype (typeof_place p))) ->
    tr_stmt (Scall p e l) (Clight.Ssequence (Clight.Scall (Some temp) e' l') assign)
| tr_drop: forall p set_stmt drop_stmt temp pe,
    set_stmt = Clight.Sset temp (Eaddrof pe (Tpointer (to_ctype (typeof_place p)) noattr)) ->
    expand_drop dropm temp (typeof_place p) = Some drop_stmt ->
    tr_stmt (Sdrop p) (Clight.Ssequence set_stmt drop_stmt)
| tr_seq: forall s1 s2 s1' s2',
    tr_stmt s1 s1' ->
    tr_stmt s2 s2' ->
    tr_stmt (Ssequence s1 s2) (Clight.Ssequence s1' s2')
| Sifthenelse: forall e e' s1 s2 s1' s2',
    expr_to_cexpr ce tce e = OK e' ->
    tr_stmt s1 s1' ->
    tr_stmt s2 s2' ->
    tr_stmt (Sifthenelse e s1 s2) (Clight.Sifthenelse e' s1' s2')
  | Sloop: forall s s',
      tr_stmt s s' ->
      tr_stmt (Sloop s) (Clight.Sloop s' Clight.Sskip)
.

Inductive tr_function: function -> Clight.function -> Prop :=
| tr_function_intro: forall f tf,
    tr_stmt f.(fn_body) tf.(Clight.fn_body) ->
    Clight.fn_return tf = to_ctype (fn_return f) ->
    Clight.fn_callconv tf = fn_callconv f ->
    Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) ->
    Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) ->
    tr_function f tf.

End SPEC.

Inductive tr_fundef (p: program): fundef -> Clight.fundef -> Prop :=
| tr_internal: forall f tf co_defs tce dropm,
    transl_composites p.(prog_types) = co_defs ->
    Ctypes.build_composite_env co_defs = OK tce ->
    dropm = PTree_Properties.of_list p.(prog_drop_glue) ->
    tr_function p.(prog_comp_env) tce dropm f tf ->
    tr_fundef p (Internal f) (Ctypes.Internal tf)
| tr_external: forall ef targs tres cconv orgs rels,    
    tr_fundef p (External orgs rels ef targs tres cconv) (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv).

      
