
type id = string

type ty = | Tunit
          | Tint of Ctypes.intsize * Ctypes.signedness * Ctypes.attr
          | Tlong of Ctypes.signedness * Ctypes.attr
          | Tfloat of Ctypes.floatsize * Ctypes.attr
          | Tfunction of (ty list) * ty
          | Tbox of ty * Ctypes.attr
          | Tadt of id* Ctypes.attr
          | Treference of ty * Rusttypes.mutkind * Ctypes.attr

let bool_ty = Tint (Ctypes.IBool, Ctypes.Unsigned, Ctypes.noattr)

type expr = Eunit
          | Eval of Values.coq_val * ty
          | Evar of id
          | Ebox of expr                                 (** Box(expr) *)
          | Efield of expr * id                          (** expr.id *)
          | Eaccess of id * id                           (** expr::id *)
          | Ederef of expr                               (** *expr *)
          | Eref of expr * Rusttypes.mutkind
          | Eunop of Cop.unary_operation * expr
          | Estruct of id * id list * expr list          (** A {a: 1, b: 2} *)
          | Ebinop of Cop.binary_operation * expr * expr
          | Eassign of expr * expr
          | Ecall of expr * expr list

type case = { variant_name: id
            ; bind_to: id
            ; body: stmt }
and stmt = Sskip
          | Sdo of expr
          | Slet of id * ty * expr option
          | Ssequence of stmt * stmt
          | Sifthenelse of expr * stmt * stmt
          | Swhile of expr * stmt
          | Sloop of stmt
          | Sbreak
          | Scontinue
          | Sreturn of expr option
          | Smatch of expr * case list
          | Sscope of stmt

type fn = { return: ty
          ; params: (id * ty) list
          ; body: stmt }

type comp = { su: Rusttypes.struct_or_variant
            ; members: (id * ty) list }

module IdMap = Map.Make (struct
    type t = id
    let compare = String.compare
end)

type ident = AST.ident

module IdentMap = Map.Make (struct
    type t = ident
    let compare = Camlcoq.P.compare
end)

type prog_item = Pfn of id * fn
               | Pcomp of id * comp

type prog = { funcs: (id * fn) list
            ; composites: (id * comp) list }

let rec prog_of_items (pis: prog_item list): prog = match pis with
  | (Pfn (x, f))::pis ->
    let p = prog_of_items pis in
    { p with funcs = (x, f)::p.funcs }
  | (Pcomp (x, c))::pis ->
    let p = prog_of_items pis in
    { p with composites = (x, c)::p.composites }
  | nil -> { funcs = []; composites = [] }

module To_syntax = struct

  let noattr = Ctypes.noattr

  type state = { symmap: ident IdMap.t
               ; local_types: Rusttypes.coq_type IdentMap.t
               ; next_ident: ident
               ; funcs: fn IdentMap.t
               ; composites: Rusttypes.composite_definition IdentMap.t }

  type error = Eid_not_found of id
             | Efield_of_non_struct of Rusttypes.coq_type
             | Efield_not_found of id
             | Ederef_non_box of Rusttypes.coq_type
             | Enot_callable of Rusttypes.coq_type
             | Eunop_type_error of Cop.unary_operation * Rusttypes.coq_type
             | Ebinop_type_error of Cop.binary_operation
                                      * Rusttypes.coq_type
                                      * Rusttypes.coq_type
             | Econstructor_alone of id * id
             | Emulti_args_to_constructor of expr list * id * id
             | Enot_a_composite of id
             | Eno_variant of ident * id
             | Enot_a_enum of Rusttypes.coq_type

  let rec typelist_to_list (tl: Rusttypes.typelist)
    : (Rusttypes.coq_type list) =
    let module T = Rusttypes in
    match tl with
    | T.Tcons (t, tl) -> t::(typelist_to_list tl)
    | T.Tnil -> []

  let rec pp_print_rust_type pp (t: Rusttypes.coq_type) (symmap: id IdentMap.t) =
    let open Format in
    let module T = Rusttypes in
    match t with
    | T.Tunit -> pp_print_string pp "()"
    | T.Tint (s, si, _) -> (
      match si with
      | Ctypes.Signed -> pp_print_string pp "int"
      | Ctypes.Unsigned -> pp_print_string pp "uint"
      );(
      match s with
      | Ctypes.I32 -> pp_print_string pp "32"
      | Ctypes.I16 -> pp_print_string pp "16"
      | Ctypes.I8 -> pp_print_string pp "8"
      | Ctypes.IBool -> pp_print_string pp "_bool"
      )
    | T.Tlong (si, _) -> (
      match si with
      | Ctypes.Signed -> pp_print_string pp "long"
      | Ctypes.Unsigned -> pp_print_string pp "ulong"
      )
    | T.Tfloat (si, _) ->
      pp_print_string pp "float"; 
      pp_print_string pp (match si with
      | Ctypes.F32 -> "32"
      | Ctypes.F64 -> "64")
    | T.Tfunction (tl, r, _) ->
      pp_print_string pp "fn(";
      pp_print_space pp ();
      let _ = List.map
          (fun t -> pp_print_rust_type pp t symmap;
            pp_print_string pp ",";
            pp_print_space pp ())
          (typelist_to_list tl)
      in
      pp_print_string pp ")->";
      pp_print_space pp ();
      pp_print_rust_type pp r symmap
    | T.Tbox (t, _) ->
      pp_print_string pp "Box(";
      pp_print_rust_type pp t symmap;
      pp_print_string pp ")";
    | T.Tstruct (id, _) ->
      pp_print_string pp (IdentMap.find id symmap);
      pp_print_string pp "<struct>"
    | T.Tvariant (id, _) ->
      pp_print_string pp (IdentMap.find id symmap);
      pp_print_string pp "<enum>"
    | T.Treference (t, m, _) ->
      pp_print_string pp "&";
      if m = T.Mutable then
        pp_print_string pp "mut";
      pp_print_rust_type pp t symmap


  let pp_print_unop pp (op: Cop.unary_operation) =
    let module O = Cop in
    let open Format in
    match op with
    | O.Onotbool -> pp_print_string pp "!"
    | O.Onotint -> pp_print_string pp "~"
    | O.Oabsfloat -> pp_print_string pp "abs"
    | O.Oneg -> pp_print_string pp "neg"

  let pp_print_binop pp (op: Cop.binary_operation) =
    let module O = Cop in
    let open Format in
    pp_print_string pp (match op with
    | O.Oadd -> "+" | O.Osub -> "-" | O.Omul -> "*" | O.Odiv -> "/"
    | O.Oand -> "&&" | O.Oor -> "||" | O.Oxor -> "^"
    | O.Oeq -> "==" | O.One -> "!=" | O.Olt -> "<" | O.Ogt -> ">"
    | O.Ole -> "<=" | O.Oge -> ">="
    | O.Oshl -> "<<" | O.Oshr -> ">>"
    | O.Omod -> "%"
    )

  let pp_print_symmap pp (symmap: id IdentMap.t) =
    IdentMap.iter
      (fun k v ->
         let open Format in
         pp_print_int pp (Camlcoq.P.to_int k);
         pp_print_string pp ": ";
         pp_print_string pp v;
         pp_print_string pp "\n"
      )
      symmap

  let pp_print_error pp err (symmap: id IdentMap.t)=
    let open Format in
    match err with
    | Eid_not_found id -> Format.fprintf pp "Identifier %s not found" id
    | Efield_of_non_struct t ->
      pp_print_string pp "Attempt to read field of non-struct type ";
      pp_print_rust_type pp t symmap
    | Efield_not_found id -> Format.fprintf pp "Field %s not found" id
    | Ederef_non_box t ->
      pp_print_string pp "Dereference on non-box type ";
      pp_print_rust_type pp t symmap
    | Enot_callable t -> 
      pp_print_string pp "Not callable type ";
      pp_print_rust_type pp t symmap
    | Eunop_type_error (op, t)->
      pp_print_string pp "Type error in unary operation: ";
      pp_print_unop pp op;
      pp_print_rust_type pp t symmap
    | Ebinop_type_error (op, t1, t2) ->
      pp_print_string pp "Type error in binary operation: ";
      pp_print_rust_type pp t1 symmap;
      pp_print_binop pp op;
      pp_print_rust_type pp t2 symmap
    | Econstructor_alone (xenum, xvar) ->
      Format.fprintf pp "Constructor %s::%s cannot appear alone" xenum xvar
    | Emulti_args_to_constructor (_, xenum, xvar) ->
      Format.fprintf pp "Too many arguments to constructo %s::%s" xenum xvar
    | Enot_a_composite x ->
      Format.fprintf pp "%s is not a composite type" x
    | Eno_variant (ienum, xvar) ->
      Format.fprintf pp "%s is not a variant of enum " xvar;
      pp_print_string pp (IdentMap.find ienum symmap)
    | Enot_a_enum t ->
      pp_print_rust_type pp t symmap;
      pp_print_string pp " is not a enum"

  type 'a ret = ('a, error) result * state

  type 'a monad = state -> 'a ret


  let run_monad (m: 'a monad) (st: state) : ('a , error) result * id IdentMap.t =
    let rev_symmap st0 = IdMap.fold (fun k v m -> IdentMap.add v k m)
                                    st0.symmap IdentMap.empty in
    match m st with
    | (Ok r, st) -> (Ok r, rev_symmap st)
    | (Error e, st) -> (Error e, rev_symmap st)

  let (>>=) (x: 'a monad) (f: 'a -> 'b monad): 'b monad =
    fun (st: state) -> match x st with
    | (Result.Error e, st') -> (Result.Error e, st')
    | (Result.Ok x', st') ->
        match f x' st' with
          | (Result.Error e, st') -> (Result.Error e, st')
          | (Result.Ok x'', st'') -> (Result.Ok x'', st'')

  let return x = fun st -> (Result.Ok x, st)


  let rec map_m (xs: 'a list) (f: 'a -> 'b monad): 'b list monad =
    match xs with
    | x::xs' ->
      f x >>= fun y ->
      map_m xs' f >>= fun ys ->
      return (y::ys)
    | [] -> return []

  let throw (e: error) = fun st -> (Result.Error e, st)

  let skeleton_st : state = { symmap = IdMap.empty
                            ; local_types = IdentMap.empty
                            ; next_ident = Camlcoq.P.one
                            ; funcs = IdentMap.empty
                            ; composites = IdentMap.empty }


  let new_ident (x: id): ident monad =
    fun st -> (
        Result.Ok st.next_ident,
        { st with symmap = IdMap.add x st.next_ident st.symmap
                ; next_ident = Camlcoq.P.succ st.next_ident }
      )

  let get_ident (x: id): ident monad =
    fun st -> match IdMap.find_opt x st.symmap with
      | Some i -> (Result.Ok i, st)
      | None -> (Result.Error (Eid_not_found x), st)

  let get_or_new_ident (x: id): ident monad =
    fun st -> match IdMap.find_opt x st.symmap with
      | Option.Some i ->
        (Result.Ok i, st)
      | None -> (
          Result.Ok st.next_ident,
          { st with symmap = IdMap.add x st.next_ident st.symmap
                  ; next_ident = Camlcoq.P.succ st.next_ident }
        )


  let get_st : state monad = fun st -> (Result.Ok st, st)

  let set_st (st: state) : unit monad = fun _ -> (Result.Ok (), st)

  let add_fn (x: id) (f: fn) : unit monad =
    new_ident x >>= fun i ->
    get_st >>= fun st ->
    let funcs' = IdentMap.add i f st.funcs in
    set_st { st with funcs = funcs' }

  let get_composite (x: id) : (ident * Rusttypes.composite_definition) monad =
    get_ident x >>= fun i ->
    fun st -> match IdentMap.find_opt i st.composites with
      | Option.None -> (Result.Error (Enot_a_composite x), st)
      | Option.Some comp -> (Result.Ok (i, comp), st)

  let get_fn (x: id) : (ident * fn) monad =
    get_ident x >>= fun i ->
    fun st -> match IdentMap.find_opt i st.funcs with
      | Option.None -> (Result.Error (Enot_a_composite x), st)
      | Option.Some f -> (Result.Ok (i, f), st)

  let reg_local_type (x: id) (t: Rusttypes.coq_type): ident monad =
    new_ident x >>= fun i ->
    fun st -> (
        Result.Ok i,
        { st with local_types = IdentMap.add i t st.local_types }
      )

  let get_local_type (x: id): Rusttypes.coq_type option monad =
    get_ident x >>= fun i ->
    fun st -> (
        Result.Ok (IdentMap.find_opt i st.local_types),
        st
      )

  let rec transl_ty (t: ty): Rusttypes.coq_type monad =
    let module T = Rusttypes in
    match t with
    | Tunit -> return T.Tunit
    | Tint (size, si, attr) -> return (T.Tint (size, si, attr))
    | Tlong (size, attr) -> return (T.Tlong (size, attr))
    | Tfloat (size, attr) -> return (T.Tfloat (size, attr))
    | Tfunction (params, ret) ->
      let rec typelist_of ts =
        match ts with
        | t::ts -> T.Tcons (t, typelist_of ts)
        | nil -> T.Tnil
      in
      map_m params transl_ty  >>= fun args' ->
      transl_ty ret >>= fun ret' ->
      return (T.Tfunction (typelist_of args', ret', AST.cc_default))
    | Tbox (t, attr) ->
      transl_ty t >>= fun t' ->
      return (T.Tbox (t', attr))
    | Tadt (x, attr) ->
      get_composite x >>= fun (i, T.Composite (_, sv, _, _)) ->
      (match sv with
        | T.Struct -> return (T.Tstruct (i, attr))
        | T.TaggedUnion -> return (T.Tvariant (i, attr)))
    | Treference (t, m, attr) ->
      transl_ty t >>= fun t' ->
      return (T.Treference (t', m, attr))


  let add_composite (x: id) (c: comp) : unit monad =
    new_ident x >>= fun i ->
    map_m c.members
      (fun (x, t) ->
         (* Do variants of different enums need to  have different idents? *)
         get_or_new_ident x >>= fun i ->
         transl_ty t >>= fun t' ->
         return (Rusttypes.Member_plain (i, t'))) >>= fun members' ->
    let c' = Rusttypes.Composite (i, c.su, members', noattr) in
    get_st >>= fun st ->
    let cos' = IdentMap.add i c' st.composites in
    set_st { st with composites = cos' }

  let rec exprlist_of xs = match xs with
        |(x::xs) -> Rustsyntax.Econs (x, exprlist_of xs)
        | [] -> Rustsyntax.Enil

  let rec typelist_of xs = match xs with
    | (x::xs) -> Rusttypes.Tcons (x, typelist_of xs)
    | [] -> Rusttypes.Tnil


  let rty_bool = Rusttypes.Tint (Ctypes.I8, Ctypes.Unsigned, noattr)

  let infer_unop (op: Cop.unary_operation)
      (t: Rusttypes.coq_type) : Rusttypes.coq_type monad =
    let open Cop in
    let module T = Rusttypes in
    match op with
    | Onotbool ->
      (match t with
       | T.Tint (Ctypes.IBool, Ctypes.Unsigned, _) -> return rty_bool
       | _ -> throw (Eunop_type_error (op, t)))
    | Onotint ->
      (match t with
       | T.Tint (size, si, attr) -> return (T.Tint (size, si, attr))
       | _ -> throw (Eunop_type_error (op, t)))
    | Oneg ->
      (match t with
       | T.Tint (size1, si1, attr1) -> return (T.Tint (size1, si1, attr1))
       | T.Tfloat (size1, attr1) -> return (T.Tfloat (size1, attr1))
       | _ -> throw (Eunop_type_error (op, t)))
    | Oabsfloat ->
      (match t with
       | T.Tfloat (size1, attr1) -> return (T.Tfloat (size1, attr1))
       | _ -> throw (Eunop_type_error (op, t)))

  let infer_binop (op: Cop.binary_operation)
      (ta: Rusttypes.coq_type) (tb: Rusttypes.coq_type)
    : Rusttypes.coq_type monad =
    let module T = Rusttypes in
    let open Cop in
    match op with
    | Oadd | Osub | Omul | Odiv ->
      (match (ta, tb) with
       | (T.Tint (size1, si1, _), T.Tint (size2, si2, _))
         when size1 = size2 && si1 = si2 ->
         return (T.Tint (size1, si1, noattr))
       | (T.Tfloat (size1, _), T.Tfloat (size2, _))
         when size1 = size2 ->
         return (T.Tfloat (size1, noattr))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oand | Oor | Oxor ->
      (match (ta, tb) with
       | (T.Tint (Ctypes.IBool, Ctypes.Unsigned, _), T.Tint (Ctypes.IBool, Ctypes.Unsigned, _)) ->
         return rty_bool
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oeq | One | Olt | Ogt | Ole | Oge ->
      (match (ta, tb) with
       | (T.Tint (size1, si1, _), T.Tint (size2, si2, _))
         when size1 = size2 && si1 = si2 ->
         return rty_bool
       | (T.Tfloat (size1, _), T.Tfloat (size2, _))
         when size1 = size2 ->
         return rty_bool
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oshl | Oshr ->
      (match (ta, tb) with
       | (T.Tint (size, si, _), T.Tint (Ctypes.I8, Ctypes.Unsigned, _)) ->
         return (T.Tint (size, si, noattr))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Omod ->
      (match (ta, tb) with
       | (T.Tint (size1, si1, _), T.Tint (size2, si2, _))
         when size1 = size2 && si1 = si2 ->
         return (T.Tint (size1, si1, noattr))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))

  let rec transl_expr (e: expr) : Rustsyntax.expr monad =
    match e with
    | Eunit -> return (Rustsyntax.Eunit)
    | Eval (v, t) ->
      transl_ty t >>= fun t ->
      return (Rustsyntax.Eval (v, t))
    | Evar x ->
      get_ident x >>= fun ix ->
      get_local_type x >>= fun tx ->
      (match tx with
      (* x is local *)
      | Option.Some tx -> get_ident x >>= fun ix ->
        return (Rustsyntax.Evar (ix, tx))
      | Option.None ->
        get_fn x >>= fun (ix, f) ->
        transl_ty f.return >>= fun tr' ->
        let targs = List.map snd f.params in
        map_m targs transl_ty >>= fun targs' ->
        let targs'' = typelist_of targs' in
        let tf' = Rusttypes.Tfunction (targs'', tr', AST.cc_default) in
        return (Rustsyntax.Evar (ix, tf'))
      )
    | Ebox e ->
      transl_expr e >>= fun e ->
      let t = Rustsyntax.typeof e in
      return (Rustsyntax.Ebox (e, Rusttypes.Tbox (t, Ctypes.noattr)))
    | Efield (e, x) ->
      transl_expr e >>= fun e' ->
      let te = Rustsyntax.typeof e' in
      (match te with
      | Rusttypes.Tstruct (ist, _) ->
        get_st >>= fun st ->
        let Rusttypes.Composite (_, _, members, _) =
          IdentMap.find ist st.composites
        in
        get_ident x >>= fun ix ->
        (match List.find_opt
          (fun (Rusttypes.Member_plain (im, _)) -> Camlcoq.P.(=) ix im)
          members
        with
        | Option.Some tm ->
          return (Rustsyntax.Efield (e', ix, Rusttypes.type_member tm))
        | Option.None -> throw (Efield_not_found x)
        )
      | Rusttypes.Treference (Rusttypes.Tstruct (ist, _) as ts, _, _) ->
        get_st >>= fun st ->
        let Rusttypes.Composite (_, _, members, _) =
          IdentMap.find ist st.composites
        in
        get_ident x >>= fun ix ->
        (match List.find_opt
                 (fun (Rusttypes.Member_plain (im, _)) -> Camlcoq.P.(=) ix im)
                 members
         with
         | Option.Some tm ->
           return (Rustsyntax.Efield
                     (Rustsyntax.Ederef (e', ts), ix, Rusttypes.type_member tm))
         | Option.None -> throw (Efield_not_found x)
        )
      | _ -> throw (Efield_of_non_struct te)
      )
    | Eaccess (xenum, xvar) -> throw (Econstructor_alone (xenum, xvar))
    | Ederef e ->
      transl_expr e >>= fun e' ->
      let te = Rustsyntax.typeof e' in
      (match te with
       | Rusttypes.Tbox (t, _) -> return (Rustsyntax.Ederef (e', t))
       | Rusttypes.Treference (t, _, _) -> return (Rustsyntax.Ederef (e', t))
       | _ -> throw (Ederef_non_box te)
      )
    | Eunop (op, e) ->
      transl_expr e >>= fun e' ->
      infer_unop op (Rustsyntax.typeof e') >>= fun t ->
      return (Rustsyntax.Eunop (op, e', t))
    | Ebinop (op, e1, e2) ->
      transl_expr e1 >>= fun e1' ->
      transl_expr e2 >>= fun e2' ->
      infer_binop op (Rustsyntax.typeof e1') (Rustsyntax.typeof e2') >>=
      fun t ->
      return (Rustsyntax.Ebinop (op, e1', e2', t))
    | Eassign (e1, e2) ->
      transl_expr e1 >>= fun e1' ->
      transl_expr e2 >>= fun e2' ->
      return (Rustsyntax.Eassign (e1', e2', Rusttypes.Tunit))
    | Estruct (xstruct, xfl, es) ->
      map_m xfl get_ident >>= fun ifl ->
      map_m es transl_expr >>= fun es' ->
      get_composite xstruct >>=
      fun (istruct, Rusttypes.Composite (_, _, _, attr)) ->
      let t = Rusttypes.Tstruct (istruct, attr) in
      return (Rustsyntax.Estruct (istruct, ifl, exprlist_of es', t))
    | Ecall (callee, args) ->
      (match callee with
      | Eaccess (xenum, xvar) ->
        get_ident xenum >>= fun ienum ->
        get_ident xvar >>= fun ivar ->
        (match args with
         | arg::nil ->
           transl_expr arg >>= fun e' ->
           return (Rustsyntax.Eenum
                     (ienum, ivar, e', Rusttypes.Tvariant (ienum, noattr)))
         | _ -> throw (Emulti_args_to_constructor (args, xenum, xvar)))

      | _ ->
        transl_expr callee >>= fun callee' ->
        map_m args (fun arg -> transl_expr arg)
        >>= fun args' ->
        (match Rustsyntax.typeof callee' with
         | Rusttypes.Tfunction (_, tr, _) ->
           let args'' = exprlist_of args' in
           return (Rustsyntax.Ecall (callee', args'', tr))
         | t -> throw (Enot_callable t)))
    | Eref (e, m) ->
      transl_expr e >>= fun e' ->
      let t' = Rustsyntax.typeof e' in
      return (Rustsyntax.Eref (e', m, t'))

  let rec transl_cases (ienum: ident) (cs: case list)
    : Rustsyntax.arm_statements monad =
    let module T = Rusttypes in
    let module S = Rustsyntax in
    match cs with
    | c::cs ->
      get_ident c.variant_name >>= fun iv ->
      get_st >>= fun st -> 
      let (T.Composite (_, _, members, _)) = IdentMap.find ienum st.composites
      in
      (match List.find_opt
              (fun (T.Member_plain (i, t)) -> i = iv)
              members
      with
      | Option.None -> throw (Eno_variant (ienum, c.variant_name))
      | Option.Some member ->
        let T.Member_plain (_, t) = member in
        get_st >>= fun old_st ->
        reg_local_type c.bind_to t >>= fun ib ->
        transl_stmt (c.body) >>= fun body' ->
        set_st old_st >>= fun _ ->
        transl_cases ienum cs >>= fun cs' ->
        return (S.AScons (Option.Some (iv, ib), body', cs'))
      )
    | nil -> return S.ASnil


  and transl_stmt (s: stmt)
      : Rustsyntax.statement monad =
    let module S = Rustsyntax in
    let module T = Rusttypes in
    match s with
    | Sskip -> return S.Sskip
    | Sdo e ->
      transl_expr e >>= fun e' ->
      return (S.Sdo e')
    | Slet (x, t, v) ->
      (* If x is required in later statements, then Slet must be part of a Ssequence.
         That case is handled in Ssequence case.
         Here we only need evaluation of e *)
      (match v with
       | Option.Some e ->
         transl_expr e >>= fun e' ->
         return (Rustsyntax.Sdo e')
       | Option.None -> return Rustsyntax.Sskip
      )
    | Ssequence (s1, s2) ->
      (match s1 with
       | Slet (x, t, v) ->
         get_st >>= fun old_st ->
         let v' = match v with
           | Option.Some e -> transl_expr e >>= fun e' -> return (Some e')
           | Option.None -> return Option.None
         in
         v' >>= fun v' ->
         transl_ty t >>= fun t' ->
         reg_local_type x t' >>= fun i ->
         transl_stmt s2 >>= fun s' ->
         set_st old_st >>= fun _ ->
         return (S.Slet (i, t', v', s'))
       | s1 ->
         transl_stmt s1 >>= fun s1' ->
         transl_stmt s2 >>= fun s2' ->
         return (S.Ssequence (s1', s2'))
      )
    | Sifthenelse (e, s1, s2) ->
      transl_expr e >>= fun e' ->
      get_st >>= fun old_st ->
      transl_stmt s1 >>= fun s1' ->
      set_st old_st >>= fun _ ->
      transl_stmt s2 >>= fun s2' ->
      set_st old_st >>= fun _ ->
      return (S.Sifthenelse (e', s1', s2'))
    | Swhile (e, s) ->
      transl_expr e >>= fun e' ->
      transl_stmt s >>= fun s' ->
      return (S.Swhile (e', s'))
    | Sloop s ->
      get_st >>= fun old_st ->
      transl_stmt s >>= fun s' ->
      set_st old_st >>= fun _ ->
      return (S.Sloop s')
    | Sbreak -> return S.Sbreak
    | Scontinue -> return S.Scontinue
    | Sreturn v ->
      (match v with
       | Option.None -> return (S.Sreturn None)
       | Option.Some e ->
         transl_expr e >>= fun e' ->
         return (S.Sreturn (Option.Some e')))
    | Smatch (e, cases) ->
      transl_expr e >>= fun e' ->
      (match S.typeof e' with
       | T.Tvariant (ienum, _) ->
         transl_cases ienum cases >>= fun arms ->
         return (S.Smatch (e', arms))
       | _ -> throw (Enot_a_enum (S.typeof e'))
      )
    | Sscope s ->
      get_st >>= fun old_st ->
      transl_stmt s >>= fun s' ->
      set_st old_st >>= fun _ ->
      return s'

  let transl_fn (f: fn) : Rustsyntax.coq_function monad =
    get_st >>= fun old_st ->
    transl_ty f.return >>= fun fn_return ->
    map_m f.params
      (fun (x, t) ->
       transl_ty t >>= fun t' ->
       reg_local_type x t' >>= fun i ->
       return (i, t')) >>= fun fn_params ->
    transl_stmt f.body >>= fun fn_body ->
    set_st old_st >>= fun _ ->
    let open Rustsyntax in
    return ({ fn_return = fn_return; fn_params; fn_body; fn_callconv = AST.cc_default })

  let transl_prog (p: prog) : (Rustsyntax.coq_function Rusttypes.program) monad =
    map_m p.funcs
      (fun (x, f) -> add_fn x f) >>= fun _ ->
    map_m p.composites
      (fun (x, c) -> add_composite x c) >>= fun _ ->
    map_m p.funcs
      (fun (x, f) ->
         transl_fn f >>= fun f' ->
         get_ident x >>= fun i ->
         return (i, (AST.Gfun (Rusttypes.Internal f')))) >>= fun defs ->
    get_ident "main" >>= fun main_ident ->
    Format.eprintf "main ident is %d\n" (Camlcoq.P.to_int main_ident);
    get_st >>= fun st ->
    let comp_defs = IdentMap.fold
                      (fun _ c cs -> c::cs)
                      st.composites
                      []
    in
    return ({ Rusttypes.prog_defs = defs
            ; Rusttypes.prog_public = [main_ident]
            ; Rusttypes.prog_main = main_ident
            ; Rusttypes.prog_types = comp_defs
            ; Rusttypes.prog_comp_env = (Rustsyntax.build_composite_env' comp_defs) })
end

