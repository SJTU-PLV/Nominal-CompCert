%{
open Rustsurface
%}

%token <string> ID
%token <string> ORIGIN

%token <int> INT
%token <string> STR_LITERAL

%token TRUE
%token FALSE

%token NOT
%token ADD
%token SUBS
%token DIV
%token LE
%token GE
%token EQ
%token NE
%token OR
%token AND
%token REF

%token ASSIGN

%token ASTERISK
%token COLON
%token SEMICOLON
%token COLON2
%token COMMA
%token RARROW
%token DOT

%token STRUCT
%token ENUM
%token FN
%token WHERE
%token LET
%token IN
%token WHILE
%token IF
%token ELSE
%token CONTINUE
%token BREAK
%token RETURN
%token BOX
%token MATCH
%token CASE
%token AS
%token RARROWW
%token LOOP
%token EOF
%token MUT

%token LANGLE
%token RANGLE
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN

%token INT32
%token UINT32
%token INT16
%token UINT16
%token INT8
%token UINT8
%token INT64
%token UINT64
%token FLOAT32
%token FLOAT64
%token BOOL

%left ASSIGN
%left AND OR
%right NOT
%left EQ NE
%left LE GE RANGLE LANGLE
%left ADD SUBS
%left ASTERISK DIV
%left REF
%left DOT
%nonassoc LPAREN

%start <Rustsurface.prog_item list> prog_eof

%type <expr list> args_expr
%type <expr> expr
%type <case> match_arm
%type <case list> match_arms
%type <ty list> params_ty
%type <stmt> stmt
%type <stmt> stmt_item
%type <id list * expr list> struct_fields
%type <ty> ty
%type <(id * ty) list> composite_fields
%type <ty list> non_empty_ty_sequence
%type <(id * (ty list)) list> enum_fields
%type <id * comp_enum> enum
%type <id * comp_struc> struct_
%type <id * fn> fn
%type <prog_item list> prog
%type <pat> pattern
%type <pat list> args_pattern
%type <id list> generic_origins

%%

prog_eof:
  | p = prog; EOF { p }

prog:
  | c = enum { [Penum (fst c, snd c)] }
  | c = struct_ { [Pstruc (fst c, snd c)] }
  | f = fn { [Pfn (fst f, snd f)] }
  | c = enum; p = prog { (Penum (fst c, snd c))::p }
  | c = struct_; p = prog { (Pstruc (fst c, snd c))::p }
  | f = fn; p = prog { (Pfn (fst f, snd f))::p }

(* optional origin *)
origin_opt:
  | { Rustsurface.dummy_origin_str }
  | x = ORIGIN { x }

(* list of origins *)
generic_origins_:
  | { [] }
  | x = ORIGIN { [x] }
  | x = ORIGIN; COMMA; orgs = generic_origins_ { x::orgs }

(* list of origins with angle brackets *)
generic_origins:
  | { [] }
  | LANGLE; l = generic_origins_; RANGLE { l }

composite_fields:
  | { [] }
  | x = ID; COLON; t = ty { [(x, t)] }
  | x = ID; COLON; t = ty; COMMA; flds = composite_fields { (x, t)::flds }

non_empty_ty_sequence:
  | t = ty { [t] }
  | t = ty; COMMA; ts = non_empty_ty_sequence { t :: ts }

enum_fields:
  | x = ID; LPAREN; ts = non_empty_ty_sequence; RPAREN;
    { [(x, ts)] }
  | x = ID; LPAREN; ts = non_empty_ty_sequence; RPAREN; COMMA; flds = enum_fields
    { (x, ts) :: flds }

enum:
  | ENUM; x = ID; LBRACE; flds = enum_fields; RBRACE
    { (x, flds) }

struct_:
  | STRUCT; x = ID; LBRACE; flds = composite_fields; RBRACE
    { (x, flds) }

fn:
  | FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; LBRACE; s = stmt; RBRACE
    { (x, { generic_origins = orgs; return = Tunit; params = p; body = s }) }
  | FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; RARROW; tr = ty; LBRACE;
    s = stmt; RBRACE
    { (x, { generic_origins = orgs; return = tr; params = p; body = s }) }

args_expr:
  | { [] }
  | e = expr { [e] }
  | e = expr; COMMA; es = args_expr { e::es }

struct_fields:
  | { ([], []) }
  | x = ID; COLON; e = expr { ([x], [e]) }
  | x = ID; COLON; e = expr; COMMA; flds = struct_fields
    { (x::(fst flds), e::(snd flds)) }

expr:
  | LPAREN; e = expr; RPAREN { e }
  | LPAREN; RPAREN { Eunit }
  | i = INT
    { Eval (Values.Vint (Camlcoq.Z.of_sint i),
            Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr)) }
  | TRUE { Eval (Values.Vint (Camlcoq.Z.one), bool_ty) }
  | FALSE { Eval (Values.Vint (Camlcoq.Z.zero), bool_ty) }
  | x = ID { Evar x }
  | BOX; LPAREN; e = expr; RPAREN { Ebox e }
  | REF; MUT; e = expr { Eref (e,Rusttypes.Mutable)} %prec REF
  | REF; e = expr { Eref (e,Rusttypes.Immutable)}
  | e = expr; DOT; x = ID { Efield (e, x) }
  | ASTERISK; e = expr { Ederef e }
  | e1 = expr; ASSIGN; e2 = expr { Eassign (e1, e2) }
  | x1 = ID; COLON2; x2 = ID; LPAREN; e = expr; RPAREN
    { Ecall ((Eaccess (x1, x2)), [e]) }
  | SUBS; e = expr { Eunop (Cop.Oneg, e) }
  | NOT; e = expr { Eunop (Cop.Onotbool, e) }
  | e1 = expr; ADD; e2 = expr { Ebinop (Cop.Oadd, e1, e2) }
  | e1 = expr; SUBS; e2 = expr { Ebinop (Cop.Osub, e1, e2) }
  | e1 = expr; ASTERISK; e2 = expr { Ebinop (Cop.Omul, e1, e2) }
  | e1 = expr; DIV; e2 = expr { Ebinop (Cop.Odiv, e1, e2) }
  | e1 = expr; LE; e2 = expr { Ebinop (Cop.Ole, e1, e2) }
  | e1 = expr; GE; e2 = expr { Ebinop (Cop.Oge, e1, e2) }
  | e1 = expr; RANGLE; e2 = expr { Ebinop (Cop.Ogt, e1, e2) }
  | e1 = expr; LANGLE; e2 = expr { Ebinop (Cop.Olt, e1, e2) }
  | e1 = expr; EQ; e2 = expr { Ebinop (Cop.Oeq, e1, e2) }
  | e1 = expr; NE; e2 = expr { Ebinop (Cop.One, e1, e2) }
  | e1 = expr; OR; e2 = expr { Ebinop (Cop.Oor, e1, e2) }
  | e1 = expr; AND; e2 = expr { Ebinop (Cop.Oand, e1, e2) }
  | callee = expr ; LPAREN; args = args_expr; RPAREN { Ecall (callee, args) }
  | lit = STR_LITERAL { Estr lit }

args_pattern:
  | { [] }
  | p = pattern; { [p] }
  | p = pattern; COMMA; args = args_pattern { p :: args }

pattern:
  | x = ID; LPAREN; args = args_pattern; RPAREN { Pconstructor (x, args) }
  | x = ID { Pbind x }

params_ty:
  | { [] }
  | t = ty { [t] }
  | t = ty; COMMA; ts = params_ty  { t :: ts }
  
ty:
  | LPAREN; RPAREN { Tunit }
  | BOOL { Tint (Ctypes.IBool, Ctypes.Unsigned, Ctypes.noattr) }
  | INT32 { Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr) }
  | INT16 { Tint (Ctypes.I16, Ctypes.Signed, Ctypes.noattr) }
  | INT8 { Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr) }
  | UINT32 { Tint (Ctypes.I32, Ctypes.Unsigned, Ctypes.noattr) }
  | UINT16 { Tint (Ctypes.I16, Ctypes.Unsigned, Ctypes.noattr) }
  | UINT8 { Tint (Ctypes.I8, Ctypes.Unsigned, Ctypes.noattr) }
  | FLOAT64 { Tfloat (Ctypes.F64, Ctypes.noattr) }
  | FLOAT32 { Tfloat (Ctypes.F32, Ctypes.noattr) }
  | FN; LPAREN; pt = params_ty; RPAREN; RARROW; rt = ty { Tfunction (pt, rt) }
  | BOX; LANGLE; t = ty; RANGLE { Tbox (t, Ctypes.noattr) }
  | REF; org = origin_opt; MUT; t = ty; { Treference(t, org, Rusttypes.Mutable, Ctypes.noattr) }
  | REF; org = origin_opt; t = ty; { Treference(t, org, Rusttypes.Immutable, Ctypes.noattr) }
  | x = ID { Tadt (x, Ctypes.noattr) }

match_arm:
  | p = pattern; RARROWW; LBRACE; s = stmt; RBRACE
    { { pattern = p ; body = s } }

match_arms:
  | arm = match_arm { [arm] }
  | arm = match_arm; arms = match_arms { arm::arms }

stmt_item:
  | { Sskip }
  | e = expr { Sdo e }
  | e1 = expr; ASSIGN; x = ID; LBRACE; flds = struct_fields; RBRACE
    { Sdo (Eassign (e1, Estruct (x, fst flds, snd flds))) }
  | LET; x = ID; COLON; t = ty;
    { Slet (x, t, Option.None) }
  | LET; x = ID; COLON; t = ty; ASSIGN; e = expr
    { Slet (x, t, Option.Some e)}
  | LET; x = ID; COLON; t = ty; ASSIGN; xs = ID; LBRACE; flds = struct_fields; RBRACE
    { Slet (x, t, Option.Some (Estruct (xs, fst flds, snd flds))) }
  | BREAK { Sbreak }
  | CONTINUE { Scontinue }
  | RETURN; { Sreturn None }
  | RETURN; e = expr { Sreturn (Some e) }
  | MATCH; e = expr; LBRACE; arms = match_arms; RBRACE { Smatch (e, arms) }

stmt:
  | s = stmt_item { s }
  | IF; e = expr; LBRACE; s1 = stmt; RBRACE; ELSE; LBRACE; s2 = stmt; RBRACE; s3 = stmt;
    { Ssequence (Sifthenelse (e, s1, s2), s3) }
  | IF; e = expr; LBRACE; s1 = stmt; RBRACE; s3 = stmt;
    { Ssequence (Sifthenelse (e, s1, Sskip), s3) }
  | WHILE; e = expr; LBRACE; s = stmt; RBRACE; s1 = stmt;
    { Ssequence (Swhile (e, s), s1) }
  | LOOP; LBRACE; s = stmt; RBRACE; s1 = stmt;
    { Ssequence (Sloop s, s1) }
  | LBRACE; s = stmt; RBRACE; s1 = stmt; { Ssequence (Sscope s, s1) }
  | s = stmt_item; SEMICOLON; s2 = stmt { Ssequence (s, s2) }

