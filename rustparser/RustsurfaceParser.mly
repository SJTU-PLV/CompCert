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
%token MOD
%token DIV
%token LE
%token GE
%token EQ
%token NE
%token OR
%token AND
%token REF
%token PREF

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
%token EXTERN
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
%type <id * comp_enum * id list * (id * id) list> enum
%type <id * comp_struc * id list * (id * id) list> struct_
%type <id * id list * (id * id) list> enum_decl
%type <id * id list * (id * id) list> struct_decl
%type <id * fn> fn
%type <prog_item list> prog
%type <pat> pattern
%type <pat list> args_pattern
%type <id list> generic_origins
%type <(id * id) list> origin_relations

%%

prog_eof:
  | p = prog; EOF { p }

prog:
  | d = enum_decl { let (x, orgs, rels) = d in [Pcomp_decl (x, Enum, orgs, rels)] }
  | d = struct_decl { let (x, orgs, rels) = d in [Pcomp_decl (x, Struct, orgs, rels)] }
  | c = enum { let (x, flds, orgs, rels) = c in [Penum (x, flds, orgs, rels)] }
  | c = struct_ { let (x, flds, orgs, rels) = c in [Pstruc (x, flds, orgs, rels)] }
  | f = fn { [Pfn (fst f, snd f)] }
  | f = fn_decl { [Pfn_decl (fst f, snd f)]}
  | d = enum_decl; p = prog { let (x, orgs, rels) = d in (Pcomp_decl (x, Enum, orgs, rels)) :: p }
  | d = struct_decl; p = prog { let (x, orgs, rels) = d in (Pcomp_decl (x, Struct, orgs, rels)) :: p }
  | c = enum; p = prog { let (x, flds, orgs, rels) = c in (Penum (x, flds, orgs, rels))::p }
  | c = struct_; p = prog { let (x, flds, orgs, rels) = c in (Pstruc (x, flds, orgs, rels))::p }
  | f = fn; p = prog { let (id, f) = f in (Pfn (id, f))::p }
  | f = fn_decl; p = prog { let (id, f) = f in (Pfn_decl (id, f))::p }

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

origin_relations_:
  | { [] }
  | x = ORIGIN; COLON; y = ORIGIN { [(x,y)] }
  | x = ORIGIN; COLON; y = ORIGIN; COMMA; rels = origin_relations_ { (x, y)::rels }

origin_relations:
  | { [] }
  | WHERE; rels = origin_relations_ { rels }

composite_fields:
  | { [] }
  | x = ID; COLON; t = ty { [(x, t)] }
  | x = ID; COLON; t = ty; COMMA; flds = composite_fields { (x, t)::flds }

non_empty_ty_sequence:
  | t = ty { [t] }
  | t = ty; COMMA; ts = non_empty_ty_sequence { t :: ts }

enum_fields:
  | x = ID { [(x, [Tunit])] }
  | x = ID; COMMA; flds = enum_fields { (x, [Tunit]) :: flds }
  | x = ID; LPAREN; ts = non_empty_ty_sequence; RPAREN;
    { [(x, ts)] }
  | x = ID; LPAREN; ts = non_empty_ty_sequence; RPAREN; COMMA; flds = enum_fields
    { (x, ts) :: flds }

enum:
  | ENUM; x = ID; orgs = generic_origins; rels = origin_relations; LBRACE; flds = enum_fields; RBRACE
    { (x, flds, orgs, rels) }

enum_decl:
  | ENUM; x = ID; orgs = generic_origins; rels = origin_relations; SEMICOLON
    { (x, orgs, rels) }

struct_:
  | STRUCT; x = ID; orgs = generic_origins; rels = origin_relations; LBRACE; flds = composite_fields; RBRACE
    { (x, flds, orgs, rels) }

struct_decl:
  | STRUCT; x = ID; orgs = generic_origins; rels = origin_relations; SEMICOLON
    { (x, orgs, rels) }

fn:
  | FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; rels = origin_relations; LBRACE; s = stmt; RBRACE
    { (x, { generic_origins = orgs; origin_relations = rels; return = Tunit; params = p; body = s }) }
  (* function with return type *)
  | FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; RARROW; tr = ty; rels = origin_relations; LBRACE;
    s = stmt; RBRACE
    { (x, { generic_origins = orgs; origin_relations = rels; return = tr; params = p; body = s }) }

(* For now, all the function declaration must be external function *)
fn_decl:
  | EXTERN; FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; rels = origin_relations
    { (x, { generic_origins = orgs; origin_relations = rels; return = Tunit; params = p}) }
  (* function with return type *)
  | EXTERN; FN; x = ID; orgs = generic_origins; LPAREN; p = composite_fields; RPAREN; RARROW; tr = ty; rels = origin_relations
    { (x, { generic_origins = orgs; origin_relations = rels; return = tr; params = p}) }

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
            Tint (Ctypes.I32, Ctypes.Signed)) }
  | TRUE { Eval (Values.Vint (Camlcoq.Z.one), bool_ty) }
  | FALSE { Eval (Values.Vint (Camlcoq.Z.zero), bool_ty) }
  | x = ID { Evar x }
  | BOX; LPAREN; e = expr; RPAREN { Ebox e }
  | REF; MUT; e = expr { Eref (e,Rusttypes.Mutable)} %prec REF
  | REF; e = expr { Eref (e,Rusttypes.Immutable)}
  | e = expr; DOT; x = ID { Efield (e, x) }
  | ASTERISK; e = expr { Ederef e }
  | e1 = expr; ASSIGN; e2 = expr { Eassign (e1, e2) }
  (* Adhoc: support zero-ary constructor*)
  | p = path_expr { let (x1, x2) = p in Ecall ((Eaccess (x1, x2)), [Eunit]) }
  | x1 = ID; COLON2; x2 = ID; LPAREN; e = expr; RPAREN
    { Ecall ((Eaccess (x1, x2)), [e]) }
    (* support Estruct. *)
  | x = ID; LBRACE; flds = struct_fields; RBRACE { Estruct (x, fst flds, snd flds) }
  | SUBS; e = expr { Eunop (Cop.Oneg, e) }
  | NOT; e = expr { Eunop (Cop.Onotbool, e) }
  | e1 = expr; ADD; e2 = expr { Ebinop (Cop.Oadd, e1, e2) }
  | e1 = expr; SUBS; e2 = expr { Ebinop (Cop.Osub, e1, e2) }
  | e1 = expr; ASTERISK; e2 = expr { Ebinop (Cop.Omul, e1, e2) }
  | e1 = expr; DIV; e2 = expr { Ebinop (Cop.Odiv, e1, e2) }
  | e1 = expr; MOD; e2 = expr { Ebinop (Cop.Omod, e1, e2) }
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

// Adhoc: copy the expr to make a expr except sturct expr. I have no idea how to refactor this code...
expr_except_struct:
  | LPAREN; e = expr_except_struct; RPAREN { e }
  | LPAREN; RPAREN { Eunit }
  | i = INT
    { Eval (Values.Vint (Camlcoq.Z.of_sint i),
            Tint (Ctypes.I32, Ctypes.Signed)) }
  | TRUE { Eval (Values.Vint (Camlcoq.Z.one), bool_ty) }
  | FALSE { Eval (Values.Vint (Camlcoq.Z.zero), bool_ty) }
  | x = ID { Evar x }
  | BOX; LPAREN; e = expr_except_struct; RPAREN { Ebox e }
  | REF; MUT; e = expr_except_struct { Eref (e,Rusttypes.Mutable)} %prec REF
  | REF; e = expr_except_struct { Eref (e,Rusttypes.Immutable)}
  | e = expr_except_struct; DOT; x = ID { Efield (e, x) }
  | ASTERISK; e = expr_except_struct { Ederef e }
  | e1 = expr_except_struct; ASSIGN; e2 = expr_except_struct { Eassign (e1, e2) }
  (* Adhoc: support zero-ary constructor*)
  | p = path_expr { let (x1, x2) = p in Ecall ((Eaccess (x1, x2)), [Eunit]) }
  | x1 = ID; COLON2; x2 = ID; LPAREN; e = expr_except_struct; RPAREN
    { Ecall ((Eaccess (x1, x2)), [e]) }
  | SUBS; e = expr_except_struct { Eunop (Cop.Oneg, e) }
  | NOT; e = expr_except_struct { Eunop (Cop.Onotbool, e) }
  | e1 = expr_except_struct; ADD; e2 = expr_except_struct { Ebinop (Cop.Oadd, e1, e2) }
  | e1 = expr_except_struct; SUBS; e2 = expr_except_struct { Ebinop (Cop.Osub, e1, e2) }
  | e1 = expr_except_struct; ASTERISK; e2 = expr_except_struct { Ebinop (Cop.Omul, e1, e2) }
  | e1 = expr_except_struct; DIV; e2 = expr_except_struct { Ebinop (Cop.Odiv, e1, e2) }
  | e1 = expr_except_struct; LE; e2 = expr_except_struct { Ebinop (Cop.Ole, e1, e2) }
  | e1 = expr_except_struct; GE; e2 = expr_except_struct { Ebinop (Cop.Oge, e1, e2) }
  | e1 = expr_except_struct; RANGLE; e2 = expr_except_struct { Ebinop (Cop.Ogt, e1, e2) }
  | e1 = expr_except_struct; LANGLE; e2 = expr_except_struct { Ebinop (Cop.Olt, e1, e2) }
  | e1 = expr_except_struct; EQ; e2 = expr_except_struct { Ebinop (Cop.Oeq, e1, e2) }
  | e1 = expr_except_struct; NE; e2 = expr_except_struct { Ebinop (Cop.One, e1, e2) }
  | e1 = expr_except_struct; OR; e2 = expr_except_struct { Ebinop (Cop.Oor, e1, e2) }
  | e1 = expr_except_struct; AND; e2 = expr_except_struct { Ebinop (Cop.Oand, e1, e2) }
  | callee = expr_except_struct ; LPAREN; args = args_expr; RPAREN { Ecall (callee, args) }
  | lit = STR_LITERAL { Estr lit }


args_pattern:
  | { [] }
  | p = pattern; { [p] }
  | p = pattern; COMMA; args = args_pattern { p :: args }

(* Refer to [https://doc.rust-lang.org/reference/patterns.html].*)

path_expr:
  | x1 = ID; COLON2; x2 = ID { (x1, x2) }

(* Path patterns take precedence over identifier patterns *)
path_pattern:
  | p = path_expr { let (x, y) = p in Pconstructor (x, y, [Pbind(Option.None, wildcard_id)])}

identifier_pattern:
  | PREF; MUT; x = ID { Pbind(Option.Some(RefMut), x) }
  | PREF; x = ID { Pbind(Option.Some(RefImmut),x) }
  | x = ID { Pbind(Option.None, x) }

tuple_struct_pattern:
  | p = path_expr; LPAREN; args = args_pattern; RPAREN { let (x, y) = p in Pconstructor (x, y, args) }

pattern:
  | p = path_pattern { p }
  | p = tuple_struct_pattern { p }
  | p = identifier_pattern { p }

params_ty:
  | { [] }
  | t = ty { [t] }
  | t = ty; COMMA; ts = params_ty  { t :: ts }
  
ty:
  | LPAREN; RPAREN { Tunit }
  | BOOL { Tint (Ctypes.IBool, Ctypes.Unsigned) }
  | INT32 { Tint (Ctypes.I32, Ctypes.Signed) }
  | INT16 { Tint (Ctypes.I16, Ctypes.Signed) }
  | INT8 { Tint (Ctypes.I8, Ctypes.Signed) }
  | UINT32 { Tint (Ctypes.I32, Ctypes.Unsigned) }
  | UINT16 { Tint (Ctypes.I16, Ctypes.Unsigned) }
  | UINT8 { Tint (Ctypes.I8, Ctypes.Unsigned) }
  | FLOAT64 { Tfloat (Ctypes.F64) }
  | FLOAT32 { Tfloat (Ctypes.F32) }
  | FN; orgs = generic_origins; LPAREN; pt = params_ty; RPAREN; RARROW; rt = ty; rels = origin_relations { Tfunction (pt, rt, orgs, rels) }
  | BOX; LANGLE; t = ty; RANGLE { Tbox (t) }
  | REF; org = origin_opt; MUT; t = ty; { Treference(t, org, Rusttypes.Mutable) }
  | REF; org = origin_opt; t = ty; { Treference(t, org, Rusttypes.Immutable) }
  | x = ID; orgs = generic_origins { Tadt (x, Ctypes.noattr, orgs) }

match_arm:
  | p = pattern; RARROWW; LBRACE; s = stmt; RBRACE
    { { pattern = p ; body = s } }

match_arms:
  | arm = match_arm { [arm] }
  | arm = match_arm; arms = match_arms { arm::arms }

stmt_item:
  | { Sskip }
  | e = expr { Sdo e }
  // | e1 = expr; ASSIGN; x = ID; LBRACE; flds = struct_fields; RBRACE
  //   { Sdo (Eassign (e1, Estruct (x, fst flds, snd flds))) }
  | LET; x = ID; COLON; t = ty;
    { Slet (x, t, Option.None) }
  | LET; x = ID; COLON; t = ty; ASSIGN; e = expr
    { Slet (x, t, Option.Some e)}
  | LET; MUT; x = ID; COLON; t = ty;
    { Slet (x, t, Option.None) }
  | LET; MUT; x = ID; COLON; t = ty; ASSIGN; e = expr
    { Slet (x, t, Option.Some e)}
  // | LET; x = ID; COLON; t = ty; ASSIGN; xs = ID; LBRACE; flds = struct_fields; RBRACE
  //   { Slet (x, t, Option.Some (Estruct (xs, fst flds, snd flds))) }
  | BREAK { Sbreak }
  | CONTINUE { Scontinue }
  | RETURN; { Sreturn None }
  | RETURN; e = expr { Sreturn (Some e) }
  (* In rust document, this expr must not be struct expr *)
  | MATCH; e = expr_except_struct; LBRACE; arms = match_arms; RBRACE { Smatch (e, arms) }

stmt:
  | s = stmt_item { s }
  (* In rust document, conditional expr also must not be struct expr *)
  | IF; e = expr_except_struct; LBRACE; s1 = stmt; RBRACE; ELSE; LBRACE; s2 = stmt; RBRACE; s3 = stmt;
    { Ssequence (Sifthenelse (e, s1, s2), s3) }
  | IF; e = expr_except_struct; LBRACE; s1 = stmt; RBRACE; s3 = stmt;
    { Ssequence (Sifthenelse (e, s1, Sskip), s3) }
  | WHILE; e = expr; LBRACE; s = stmt; RBRACE; s1 = stmt;
    { Ssequence (Swhile (e, s), s1) }
  | LOOP; LBRACE; s = stmt; RBRACE; s1 = stmt;
    { Ssequence (Sloop s, s1) }
  | LBRACE; s = stmt; RBRACE; s1 = stmt; { Ssequence (Sscope s, s1) }
  | s = stmt_item; SEMICOLON; s2 = stmt { Ssequence (s, s2) }
