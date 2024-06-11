Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight.
Require Import Rusttypes RustlightBase RustIR.
Require Import Clightgen.

Import ListNotations.

Definition tr_composite_env (ce: composite_env) (tce: Ctypes.composite_env) : Prop :=
  forall id co, ce!id = Some co ->        
         match co.(co_sv) with
         | Struct =>
             exists tco, tce!id = Some tco /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             map transl_composite_member co.(co_members) = tco.(Ctypes.co_members) /\
             co.(co_attr) = tco.(Ctypes.co_attr) /\
             co.(co_sizeof) = tco.(Ctypes.co_sizeof) /\
             co.(co_alignof) = tco.(Ctypes.co_alignof) /\
             co.(co_rank) = tco.(Ctypes.co_rank)
         | TaggedUnion =>
             exists tco union_id tag_fid union_fid union,
             let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
             let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in
             let m := (map transl_composite_member co.(co_members)) in
             tce!id = Some tco /\ tce!union_id = Some union /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             tco.(Ctypes.co_members) = [tag_member; union_member] /\
             tco.(Ctypes.co_sizeof) = co.(co_sizeof) /\
             tco.(Ctypes.co_alignof) = co.(co_alignof) /\
             tco.(Ctypes.co_rank) = co.(co_rank) /\
             union.(Ctypes.co_su) = Union /\
             union.(Ctypes.co_members) = m /\
             (* To specify *)
             union.(Ctypes.co_sizeof) = align (Ctypes.sizeof_composite tce Union m) (Ctypes.alignof_composite tce m) /\
             union.(Ctypes.co_alignof) = (Ctypes.alignof_composite tce m) /\
             union.(Ctypes.co_rank) = Ctypes.rank_members tce m
         end.

Lemma to_ctype_sizeof: forall ce tce ty cty,
    to_ctype ty = cty ->
    tr_composite_env ce tce ->
    sizeof ce ty = Ctypes.sizeof tce cty.
Admitted.

Lemma transl_composites_meet_spec: forall co_defs tco_defs ce tce,
    transl_composites co_defs = tco_defs ->
    build_composite_env co_defs = OK ce ->
    Ctypes.build_composite_env tco_defs = OK tce ->
    tr_composite_env ce tce.
Admitted.

Section SPEC.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.  
Variable dropm: PTree.t ident.

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

      
