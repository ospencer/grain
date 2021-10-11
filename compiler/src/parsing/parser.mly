%{
(* These opens are used inside the actual parser *)
open Parsetree
open Ast_helper

(* Including the Parser_extra file allows it to be written in Reason and have editor tooling *)
include Parser_header
%}


%token <string> NUMBER_INT
%token <string> NUMBER_FLOAT
%token <string> INT32
%token <string> INT64
%token <string> FLOAT32
%token <string> FLOAT64
%token <string> WASMI32
%token <string> WASMI64
%token <string> WASMF32
%token <string> WASMF64
%token <string> ID
%token <string> TYPEID
%token <string> STRING
%token <string> CHAR
%token LBRACK RBRACK LPAREN RPAREN LBRACE RBRACE LCARET RCARET
%token LCARETLCARET RCARETRCARET RCARETRCARETRCARET
%token CARET
%token COMMA SEMI AS
%token THICKARROW ARROW
%token IS ISNT EQEQ LESSEQ GREATEREQ
%token NOTEQ EQUAL GETS
%token UNDERSCORE
%token COLON DOT ELLIPSIS

%token ASSERT FAIL EXCEPTION THROW

%token PLUS PLUSPLUS DASH STAR SLASH PERCENT
%token PLUSEQ DASHEQ STAREQ SLASHEQ PERCENTEQ
%token TRUE FALSE VOID

%token LET MUT REC IF WHEN ELSE MATCH WHILE FOR CONTINUE BREAK
%token AMPAMP PIPEPIPE NOT AT
%token AMP PIPE

%token ENUM RECORD IMPORT EXPORT FOREIGN WASM PRIMITIVE
%token EXCEPT FROM
%token EOL EOF

/* Operator precedence may be found in /docs/contributor/operator_precedence.md */

%right PLUSEQ DASHEQ STAREQ SLASHEQ PERCENTEQ
%left PIPEPIPE
%left AMPAMP
%left PIPE
%left CARET
%left AMP
%left EQEQ NOTEQ IS ISNT
%left LCARET LESSEQ RCARET GREATEREQ
%left LCARETLCARET RCARETRCARET RCARETRCARETRCARET
%left PLUS DASH PLUSPLUS
%left STAR SLASH PERCENT
%left COLON
%right NOT
%left DOT


%start <Parsetree.parsed_program> program

%%

eol :
  | EOL { () }

eols :
  | eol+ { () }

eos :
  | eols { () }
  | SEMI eols? { () }

lbrack :
  | LBRACK eols? { () }

rbrack :
  | eols? RBRACK { () }

lparen :
  | LPAREN eols? { () }

rparen :
  | eols? RPAREN { () }

lbrace :
  | LBRACE eols? { () }

rbrace :
  | eols? RBRACE { () }

lcaret :
  | LCARET eols? { () }

rcaret :
  | eols? RCARET { () }

comma :
  | eols? COMMA eols? { () }

/* prevents abiguity between EOL characters after the final comma and before the closing character */
trailing_comma :
  | eols? COMMA { () }

colon :
  | eols? COLON eols? { () }

dot :
  | eols? DOT eols? { () }

arrow :
  | eols? ARROW eols? { () }

thickarrow :
  | eols? THICKARROW eols? { () }

equal :
  | eols? EQUAL eols? { () }

const :
  | dash_op? NUMBER_INT { Const.number (PConstNumberInt (if Option.is_some $1 then "-" ^ $2 else $2)) }
  | dash_op? NUMBER_FLOAT { Const.number (PConstNumberFloat (if Option.is_some $1 then "-" ^ $2 else $2)) }
  | dash_op? NUMBER_INT SLASH eols? dash_op? NUMBER_INT { Const.number (PConstNumberRational ((if Option.is_some $1 then "-" ^ $2 else $2), (if Option.is_some $5 then "-" ^ $6 else $6))) }
  | dash_op? INT32 { Const.int32 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? INT64 { Const.int64 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? FLOAT32 { Const.float32 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? FLOAT64 { Const.float64 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? WASMI32 { Const.wasmi32 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? WASMI64 { Const.wasmi64 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? WASMF32 { Const.wasmf32 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | dash_op? WASMF64 { Const.wasmf64 (if Option.is_some $1 then "-" ^ $2 else $2) }
  | TRUE { Const.bool true }
  | FALSE { Const.bool false }
  | VOID { Const.void }
  | STRING { Const.string $1 }
  | CHAR { Const.char $1 }

expr :
  | stmt_expr { $1 }
  | binop_expr { $1 }

binop_expr :
  | binop_expr plus_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr dash_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr star_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr slash_op eols?     binop_expr { no_rational_literal $1 $4; Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr percent_op eols?   binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr is_op eols?        binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr isnt_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr eqeq_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr noteq_op eols?     binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr caret_op eols?     binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr lcaret_op eols?    binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr llcaret_op eols?   binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr rcaret_op eols?    binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr rrcaret_op eols?   binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr rrrcaret_op eols?  binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr lesseq_op eols?    binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr greatereq_op eols? binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr amp_op eols?       binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr ampamp_op eols?    binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr pipe_op eols?      binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr pipepipe_op eols?  binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr plusplus_op eols?  binop_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$2]) [$1; $4] }
  | binop_expr colon typ { Exp.constraint_ ~loc:(symbol_rloc dyp) $1 $3 }
  | lam_expr { $1 }
  | non_assign_expr { $1 }
  | one_sided_if_expr { $1 }
  | assign_expr { $1 }

ellipsis_prefix(X) :
  | ELLIPSIS X {$2}

pattern :
  | pattern colon typ { Pat.constraint_ ~loc:(symbol_rloc dyp) $1 $3 }
  | UNDERSCORE { Pat.any ~loc:(symbol_rloc dyp) () }
  | const { Pat.constant ~loc:(symbol_rloc dyp) $1 }
  /* If the pattern uses an external ID, we know it's a constructor, not a variable */
  | ext_constructor { Pat.construct ~loc:(symbol_rloc dyp) $1 [] }
  | ID { Pat.var ~loc:(symbol_rloc dyp) (mkstr dyp $1) }
  | special_id { Pat.var ~loc:(symbol_rloc dyp) (mkstr dyp $1) }
  | primitive_ { Pat.var ~loc:(symbol_rloc dyp) (mkstr dyp $1) }
  | lparen tuple_patterns rparen { Pat.tuple ~loc:(symbol_rloc dyp) $2 }
  | lbrack rcaret patterns rbrack { Pat.array ~loc:(symbol_rloc dyp) $3 }
  | lbrack rcaret rbrack { Pat.array ~loc:(symbol_rloc dyp) [] }
  | lparen pattern rparen { $2 }
  | lbrace record_patterns rbrace { Pat.record ~loc:(symbol_rloc dyp) $2 }
  | type_id lparen patterns rparen { Pat.construct ~loc:(symbol_rloc dyp) $1 $3 }
  | type_id { Pat.construct ~loc:(symbol_rloc dyp) $1 [] }
  | lbrack patterns comma_prefix(ellipsis_prefix(any_or_var_pat))? rbrack { Pat.list ~loc:(symbol_rloc dyp) $2 $3 }
  | lbrack ellipsis_prefix(any_or_var_pat)? rbrack { Pat.list ~loc:(symbol_rloc dyp) [] $2 }

any_or_var_pat :
  | UNDERSCORE { Pat.any ~loc:(symbol_rloc dyp) () }
  | ID { Pat.var ~loc:(symbol_rloc dyp) (mkstr dyp $1) }

comma_prefix(X) :
  | comma X {$2}

patterns :
  | pattern comma_prefix(pattern)* trailing_comma? { $1::$2 }

tuple_patterns :
  | pattern comma { [$1] }
  | pattern comma_prefix(pattern)+ trailing_comma? { $1::$2 }

record_patterns :
  | record_pattern comma_prefix(record_pattern)* trailing_comma? { $1::$2 }

record_pattern :
  | UNDERSCORE { None, Open }
  | id colon pattern { Some($1, $3), Closed }
  | id { Some($1, Pat.var ~loc:(symbol_rloc dyp) (mkstr dyp (Identifier.last $1.txt))), Closed }

data_typ :
  | type_id lcaret typ comma_prefix(typ)* rcaret { Typ.constr $1 ($3::$4) }
  | type_id { Typ.constr $1 [] }

typ :
  /* Convenience: Parens optional for single-argument functions */
  | data_typ arrow typ { Typ.arrow ~loc:(symbol_rloc dyp) [$1] $3 }
  | ID arrow typ { Typ.arrow ~loc:(symbol_rloc dyp) [(Typ.var $1)] $3 }
  | lparen typs? rparen arrow typ { Typ.arrow ~loc:(symbol_rloc dyp) $2 $5 }
  | lparen tuple_typs rparen { Typ.tuple ~loc:(symbol_rloc dyp) $2 }
  | lparen typ rparen { $2 }
  | ID { Typ.var $1 }
  | data_typ { $1 }

typs :
  | typ comma_prefix(typ)* trailing_comma? { $1::$2 }

tuple_typs :
  | typ comma { [$1] }
  | typ comma_prefix(typ)+ { $1::$2 }

value_bind :
  | pattern equal expr { Vb.mk ~loc:(symbol_rloc dyp) $1 $3 }

value_binds :
  | value_bind comma_prefix(value_bind)* { $1::$2 }

import_exception :
  | EXCEPT lbrace id comma_prefix(id)* trailing_comma? rbrace {$3::$4}

as_prefix(X) :
  | AS X {$2}

aliasable(X) :
  | X as_prefix(X)? {($1, $2)}

import_ids :
  | aliasable(id) comma_prefix(aliasable(id))* {$1::$2}

import_shape :
  | id { PImportModule $1 }
  | STAR import_exception? { PImportAllExcept (Option.value ~default:[] $2) }
  | lbrace import_ids? trailing_comma? rbrace { PImportValues (Option.value ~default:[] $2) }

import_stmt :
  | IMPORT import_shape comma_prefix(import_shape)* FROM file_path { Imp.mk ~loc:(symbol_rloc dyp) ($2::$3) $5 }

data_declaration_stmt :
  | EXPORT data_declaration { (Exported, $2) }
  | data_declaration { (Nonexported, $1) }

data_declaration_stmts :
  | data_declaration_stmt comma data_declaration_stmts { $1::$3 }
  | data_declaration_stmt { [$1] }

export_exception :
  | EXCEPT export_id_str comma_prefix(export_id_str)* {$2::$3}

export_stmt :
  | attributes EXPORT LET REC value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Exported Recursive Immutable $5 }
  | attributes EXPORT LET value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Exported Nonrecursive Immutable $4 }
  | attributes EXPORT LET REC MUT value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Exported Recursive Mutable $6 }
  | attributes EXPORT LET MUT value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Exported Nonrecursive Mutable $5 }
  | EXPORT foreign_stmt { Top.foreign ~loc:(symbol_rloc dyp) Exported $2 }
  | EXPORT primitive_stmt { Top.primitive ~loc:(symbol_rloc dyp) Exported $2 }
  | EXPORT exception_stmt { Top.grain_exception ~loc:(symbol_rloc dyp) Exported $2 }
  | EXPORT aliasable(any_id_str) comma_prefix(aliasable(any_id_str))* { Top.export ~loc:(symbol_rloc dyp) (Ex.mk ~loc:(symbol_rloc dyp) ($2::$3)) }
  | EXPORT STAR export_exception? { Top.export_all ~loc:(symbol_rloc dyp) (Option.value ~default:[] $3) }

data_constructor :
  | TYPEID { CDecl.singleton ~loc:(symbol_rloc dyp) (mkstr dyp $1) }
  | TYPEID lparen typs? rparen { CDecl.tuple ~loc:(symbol_rloc dyp) (mkstr dyp $1) $3 }
  /* Special support for lists */
  | lbrack rbrack { CDecl.singleton ~loc:(symbol_rloc dyp) (mkstr dyp "[]") }
  | lbrack ELLIPSIS rbrack lparen typs? rparen { CDecl.tuple ~loc:(symbol_rloc dyp) (mkstr dyp "[...]") $5 }

data_constructors :
  | lbrace data_constructor comma_prefix(data_constructor)* trailing_comma? rbrace { $2::$3 }

data_label :
  | simple_id colon typ { LDecl.mk ~loc:(symbol_rloc dyp) $1 $3 Immutable }
  | MUT simple_id colon typ { LDecl.mk ~loc:(symbol_rloc dyp) $2 $4 Mutable }

data_labels :
  | lbrace data_label comma_prefix(data_label)* trailing_comma? rbrace { $2::$3 }

id_vec :
  | lcaret ID comma_prefix(ID)* rcaret {$2::$3}

data_declaration :
  | ENUM TYPEID id_vec? data_constructors { Dat.variant ~loc:(symbol_rloc dyp) (mkstr dyp $2) (List.map Typ.var (Option.value ~default:[] $3)) $4 }
  | RECORD TYPEID id_vec? data_labels { Dat.record ~loc:(symbol_rloc dyp) (mkstr dyp $2) (List.map Typ.var (Option.value ~default:[] $3)) $4 }

prim1_expr :
  | NOT non_assign_expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp ["!"]) [$2] }

paren_expr :
  | lparen expr rparen { $2 }

app_arg_exprs :
  | expr comma_prefix(expr)* { $1::$2 }

app_expr :
  | left_accessor_expr lparen app_arg_exprs? trailing_comma? rparen { Exp.apply ~loc:(symbol_rloc dyp) $1 $3 }

dot_prefix(X) :
  | dot X {$2}

ext_constructor :
  | TYPEID dot_prefix(type_id)+ { prerr_string "\nid\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); (mkid ($1::$2)) (symbol_rloc dyp) }

plus_op :
  | PLUS { "+" }
plusplus_op :
  | PLUSPLUS { "++" }
dash_op :
  | DASH { "-" }
star_op :
  | STAR { "*" }
slash_op :
  | SLASH { "/" }
percent_op :
  | PERCENT { "%" }
is_op :
  | IS { "is" }
isnt_op :
  | ISNT { "isnt" }
eqeq_op :
  | EQEQ { "==" }
noteq_op :
  | NOTEQ { "!=" }
caret_op :
  | CARET { "^" }
lcaret_op :
  | LCARET { "<" }
llcaret_op :
  | LCARETLCARET { "<<" }
rcaret_op :
  | RCARET { ">" }
rrcaret_op :
  | RCARETRCARET { ">>" }
rrrcaret_op :
  | RCARETRCARETRCARET { ">>>" }
lesseq_op :
  | LESSEQ { "<=" }
greatereq_op :
  | GREATEREQ { ">=" }
amp_op :
  | AMP { "&" }
ampamp_op :
  | AMPAMP { "&&" }
pipe_op :
  | PIPE { "|" }
pipepipe_op :
  | PIPEPIPE { "||" }
pluseq_op :
  | PLUSEQ { "+" }
dasheq_op :
  | DASHEQ { "-" }
stareq_op :
  | STAREQ { "*" }
slasheq_op :
  | SLASHEQ { "/" }
percenteq_op :
  | PERCENTEQ { "%" }

infix_op :
  | plus_op
  | dash_op
  | star_op
  | slash_op
  | percent_op
  | is_op
  | isnt_op
  | eqeq_op
  | plusplus_op
  | noteq_op
  | caret_op
  | lcaret_op
  | llcaret_op
  | rcaret_op
  | rrcaret_op
  | rrrcaret_op
  | lesseq_op
  | greatereq_op
  | amp_op
  | ampamp_op
  | pipe_op
  | pipepipe_op
  | pluseq_op
  | dasheq_op
  | stareq_op
  | slasheq_op {$1}

prefix_op :
  | NOT { "!" }

primitive_ :
  | ASSERT { "assert" }
  | THROW { "throw" }
  | FAIL { "fail" }

special_op :
  | infix_op | prefix_op {$1}

special_id :
  | lparen special_op rparen { $2 }

all_ids :
  | ID | TYPEID | special_id {$1}

id :
  | TYPEID dot_prefix(TYPEID)* all_ids { prerr_string "\nid\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); (mkid (List.append $1 [$2])) (symbol_rloc dyp) }
  | all_ids { prerr_string "\nid\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); (mkid [$1]) (symbol_rloc dyp) }

simple_id :
  | ID { (mkid [$1]) (symbol_rloc dyp) }

type_id :
  | TYPEID dot_prefix(TYPEID)* { prerr_string "\nid\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); (mkid (List.append $1 [$2])) (symbol_rloc dyp) }

id_expr :
  | id { prerr_string "\nsimple_expr\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); Exp.ident ~loc:(symbol_rloc dyp) $1 }

simple_expr :
  | const { Exp.constant ~loc:(symbol_rloc dyp) $1 }
  | lparen tuple_exprs rparen { Exp.tuple ~loc:(symbol_rloc dyp) $2 }
  | lbrace record_exprs rbrace { Exp.record ~loc:(symbol_rloc dyp) $2 }
  | id_expr { $1 }

block_expr :
  | lbrace block_body rbrace { no_record_block $2; Exp.block ~loc:(symbol_rloc dyp) $2 }

block :
  | lbrace block_body rbrace { Exp.block ~loc:(symbol_rloc dyp) $2 }

block_or_expr :
  | block { $1 }
  | expr { no_brace_expr $1; $1 }

lam_expr :
  | lparen patterns? rparen thickarrow block_or_expr { Exp.lambda ~loc:(symbol_rloc dyp) (Option.value ~default:[] $2) $5 }
  | ID thickarrow block_or_expr { Exp.lambda ~loc:(symbol_rloc dyp) [Pat.var ~loc:(rhs_loc dyp 1) (mkstr dyp $1)] $3 }

attribute :
  | AT id_str eols? {$2}

attributes :
  | { None }
  | attribute attribute* { Some ($1::$2) }

let_expr :
  | attributes LET REC value_binds { Exp.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Recursive Immutable $4 }
  | attributes LET value_binds { Exp.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonrecursive Immutable $3 }
  | attributes LET REC MUT value_binds { Exp.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Recursive Mutable $5 }
  | attributes LET MUT value_binds { Exp.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonrecursive Mutable $4 }

if_expr :
  | IF lparen expr rparen eols? block_or_expr eols? ELSE eols? block_or_expr { Exp.if_ ~loc:(symbol_rloc dyp) $3 $6 $10 }

one_sided_if_expr :
  | IF lparen expr rparen eols? block_or_expr { Exp.if_ ~loc:(symbol_rloc dyp) $3 $6 (Exp.block []) }

while_expr :
  | WHILE lparen expr rparen block { Exp.while_ ~loc:(symbol_rloc dyp) $3 $5 }

for_expr :
  | FOR lparen block_body_expr? eols? SEMI eols? expr? eols? SEMI eols? expr? rparen block { Exp.for_ ~loc:(symbol_rloc dyp) $3 $7 $11 $13 }

when_guard :
  | WHEN expr {$2}

match_branch :
  | pattern when_guard? thickarrow expr { Mb.mk ~loc:(symbol_rloc dyp) $1 $4 $2 }

match_branches :
  | match_branch comma_prefix(match_branch)* trailing_comma? { $1::$2 }

match_expr :
  | MATCH lparen expr rparen lbrace match_branches rbrace { Exp.match_ ~loc:(symbol_rloc dyp) $3 $6 }

list_expr_ending :
  | trailing_comma? { None }
  | comma ELLIPSIS expr { Some $3 }

list_expr :
  | lbrack rbrack { Exp.list ~loc:(symbol_rloc dyp) [] None }
  | lbrack expr comma_prefix(expr)* list_expr_ending rbrack { Exp.list ~loc:(symbol_rloc dyp) ($2::$3) $4 }

array_expr :
  | lbrack rcaret rbrack { Exp.array ~loc:(symbol_rloc dyp) [] }
  | lbrack rcaret eols? expr comma_prefix(expr)* trailing_comma? rbrack { Exp.array ~loc:(symbol_rloc dyp) ($4::$5) }

stmt_expr :
  | THROW expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp ["throw"]) [$2] }
  | ASSERT expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp ["assert"]) [$2] }
  | FAIL expr { Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp ["fail"]) [$2] }
  | CONTINUE { Exp.continue ~loc:(symbol_rloc dyp) () }
  | BREAK { Exp.break ~loc:(symbol_rloc dyp) () }

assign_binop_op :
  | pluseq_op
  | dasheq_op
  | stareq_op
  | slasheq_op
  | percenteq_op {$1}

assign_expr :
  | binop_expr eols? GETS eols? expr { no_array_access $1; Exp.box_assign ~loc:(symbol_rloc dyp) $1 $5 }
  | id_expr equal expr { Exp.assign ~loc:(symbol_rloc dyp) $1 $3 }
  | id_expr eols? assign_binop_op eols? expr { Exp.assign ~loc:(symbol_rloc dyp) $1 (Exp.apply ~loc:(symbol_rloc dyp) (mkid_expr dyp [$3]) [$1; $5]) }
  | record_set { $1 }
  | array_set { $1 }

non_assign_expr :
  | app_expr    { prerr_string "\nexpr_app_expr\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); $1 }
  | prim1_expr  { $1 }
  | simple_expr { prerr_string "\nexpr_simple_expr\n"; when_debug ~n:1 (fun () -> dyp.print_state stderr); $1 }
  | record_get  { $1 }
  | paren_expr  { $1 }
  | block_expr  { $1 }
  | if_expr     { $1 }
  | while_expr  { $1 }
  | for_expr    { $1 }
  | match_expr  { $1 }
  | list_expr   { $1 }
  | array_get   { $1 }
  | array_expr  { $1 }

left_accessor_expr :
  | app_expr    { $1 }
  | simple_expr { $1 }
  /*| array_get   { $1 }*/
  | record_get  { $1 }
  | paren_expr  { $1 }
  | block_expr  { $1 }

block_body_expr :
  | let_expr    { $1 }
  | expr  { $1 }

block_body_stmt :
  | block_body_expr SEMI eols? { $1 }
  | block_body_expr eols { $1 }

tuple_exprs :
  | expr comma { [$1] }
  | expr comma_prefix(expr)+ trailing_comma? { $1::$2 }

array_get :
  | left_accessor_expr lbrack expr rbrack { Exp.array_get ~loc:(symbol_rloc dyp) $1 $3 }

array_set :
  | expr lbrack expr rbrack equal expr { Exp.array_set ~loc:(symbol_rloc dyp) $1 $3 $6 }

record_get :
  | left_accessor_expr dot simple_id { no_uppercase_ident $1; Exp.record_get $1 $3 }

record_set :
  | left_accessor_expr dot simple_id equal expr { no_uppercase_ident $1; Exp.record_set ~loc:(symbol_rloc dyp) $1 $3 $5 }

record_field :
  | id colon expr { $1, $3 }

record_pun :
  | ID { mkid [$1] (symbol_rloc dyp), Exp.ident ~loc:(symbol_rloc dyp) (mkid [$1] (symbol_rloc dyp)) }

record_expr :
  | record_field | record_pun {$1}

record_exprs :
  | record_expr comma_prefix(record_expr)* trailing_comma? {$1::$2}

block_body :
  | block_body_stmt* block_body_expr SEMI { $1 @ [$2] }
  | block_body_stmt* block_body_expr { $1 @ [$2] }

file_path :
  | STRING { Location.mkloc $1 (symbol_rloc dyp) }

id_str :
  | ID { Location.mkloc $1 (symbol_rloc dyp) }
  | special_id { Location.mkloc $1 (symbol_rloc dyp) }

type_id_str :
  | TYPEID { Location.mkloc $1 (symbol_rloc dyp) }

any_id_str :
  | id_str { $1 }
  | type_id_str { $1 }

export_id_str :
  | id_str { ExportExceptValue $1 }
  | type_id_str { ExportExceptData $1 }

foreign_stmt :
  | FOREIGN WASM id_str colon typ as_prefix(id_str)? FROM file_path { Val.mk ~loc:(symbol_rloc dyp) ~mod_:$8 ~name:$3 ~alias:$6 ~typ:$5 ~prim:[] }

prim :
  | primitive_ { Location.mkloc $1 (symbol_rloc dyp) }

primitive_stmt :
  | PRIMITIVE id_str colon typ equal STRING { Val.mk ~loc:(symbol_rloc dyp) ~mod_:{$2 with txt="primitive"} ~name:$2 ~alias:None ~typ:$4 ~prim:[$6] }
  | PRIMITIVE prim colon typ equal STRING { Val.mk ~loc:(symbol_rloc dyp) ~mod_:{$2 with txt="primitive"} ~name:$2 ~alias:None ~typ:$4 ~prim:[$6] }

exception_stmt :
  | EXCEPTION type_id_str { Except.singleton ~loc:(symbol_rloc dyp) $2 }
  | EXCEPTION type_id_str lparen typs? rparen { Except.tuple ~loc:(symbol_rloc dyp) $2 $4 }

toplevel_stmt :
  | attributes LET REC value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonexported Recursive Immutable $4 }
  | attributes LET value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonexported Nonrecursive Immutable $3 }
  | attributes LET REC MUT value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonexported Recursive Mutable $5 }
  | attributes LET MUT value_binds { Top.let_ ~loc:(symbol_rloc dyp) ~attributes:$1 Nonexported Nonrecursive Mutable $4 }
  | expr { Top.expr ~loc:(symbol_rloc dyp) $1 }
  | import_stmt { Top.import ~loc:(symbol_rloc dyp) $1 }
  | IMPORT foreign_stmt { Top.foreign ~loc:(symbol_rloc dyp) Nonexported $2 }
  | data_declaration_stmts { Top.data ~loc:(symbol_rloc dyp) $1 }
  | export_stmt { $1 }
  | primitive_stmt { Top.primitive ~loc:(symbol_rloc dyp) Nonexported $1 }
  | exception_stmt { Top.grain_exception ~loc:(symbol_rloc dyp) Nonexported $1 }

eos_prefix(X) :
  | eos X {$2}

toplevel_stmts :
  | toplevel_stmt eos_prefix(toplevel_stmt)* { $1::$2 }

program :
  | eols? toplevel_stmts eos? EOF { make_program $2 }

%%

(* Partially apply the `program` from the parser to our parse_program method *)
let parse_program = parse_program program

// %mli {
// val parse_program : Lexing.lexbuf -> ((Parsetree.parsed_program * 'a) list)
// }
