%{
(* These opens are used inside the actual parser *)
open Parsetree
open Ast_helper
open Asttypes

(* Including the Parser_extra file allows it to be written in Reason and have editor tooling *)
include Parser_header

(* https://github.com/ocaml/dune/issues/2450 *)
module Grain_parsing = struct end
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
%token LBRACK LBRACKRCARET RBRACK LPAREN RPAREN LBRACE RBRACE LCARET RCARET
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

// reserved tokens
%token TRY CATCH COLONCOLON

// Not a real token, this is injected by the lexer
%token FUN

/* Operator precedence may be found in /docs/contributor/operator_precedence.md */

%nonassoc _below_infix

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


// %right EOL
%right SEMI EOL COMMA DOT COLON

%nonassoc _if
%nonassoc ELSE


%start <Parsetree.parsed_program> program

%%

%inline eol :
  | EOL { () }

%inline eols :
  | eol+ { () }

// eols :
//   | eols EOL
//   | EOL { () }

%inline opt_eols :
  | ioption(eols) { () }

eos :
  | eols { () }
  | SEMI opt_eols %prec SEMI { () }

lbrack :
  | LBRACK opt_eols { () }

lbrackrcaret :
  | LBRACKRCARET opt_eols { () }

rbrack :
  | opt_eols RBRACK { () }

lparen :
  | LPAREN opt_eols { () }

rparen :
  | opt_eols RPAREN { () }

lbrace :
  | LBRACE opt_eols { () }

rbrace :
  | eols? RBRACE { () }

lcaret :
  | LCARET opt_eols { () }

rcaret :
  | opt_eols RCARET { () }

%inline comma :
  | COMMA opt_eols { () }

/* prevents abiguity between EOL characters after the final comma and before the closing character */
%inline trailing_comma :
  | COMMA { () }

%inline colon :
  | COLON opt_eols { () }

%inline dot :
  | DOT opt_eols { () }

arrow :
  | ARROW opt_eols { () }

thickarrow :
  | opt_eols THICKARROW opt_eols { () }

equal :
  | EQUAL opt_eols { () }

const :
  | dash_op? NUMBER_INT { Const.number (PConstNumberInt (if Option.is_some $1 then "-" ^ $2 else $2)) }
  | dash_op? NUMBER_FLOAT { Const.number (PConstNumberFloat (if Option.is_some $1 then "-" ^ $2 else $2)) }
  | dash_op? NUMBER_INT SLASH opt_eols dash_op? NUMBER_INT { Const.number (PConstNumberRational ((if Option.is_some $1 then "-" ^ $2 else $2), (if Option.is_some $5 then "-" ^ $6 else $6))) }
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
  | non_stmt_expr { $1 }

non_binop_expr :
  | lam_expr { $1 }
  | non_assign_expr { $1 }
  // | one_sided_if_expr { $1 }
  | assign_expr { $1 }

non_stmt_expr :
  | binop_expr { $1 }
  | annotated_expr { $1 }

%inline annotation :
  | colon typ { $2 }

annotated_expr :
  | non_binop_expr annotation? { Option.fold ~none:$1 ~some:(fun ann -> Exp.constraint_ ~loc:(to_loc $loc) $1 ann) $2 }

binop_expr :
  | non_stmt_expr infix_op opt_eols non_stmt_expr { Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($2) [$2]) [$1; $4] }

ellipsis_prefix(X) :
  | ELLIPSIS X {$2}

pattern :
  | pattern colon typ { Pat.constraint_ ~loc:(to_loc $loc) $1 $3 }
  | FUN? UNDERSCORE { Pat.any ~loc:(to_loc $loc) () }
  | const { Pat.constant ~loc:(to_loc $loc) $1 }
  /* If the pattern uses an external ID, we know it's a constructor, not a variable */
  // | ext_constructor { Pat.construct ~loc:(to_loc $loc) $1 [] }
  | FUN? ID { Pat.var ~loc:(to_loc $loc) (mkstr $loc $2) }
  | FUN? special_id { Pat.var ~loc:(to_loc $loc) (mkstr $loc $2) }
  | primitive_ { Pat.var ~loc:(to_loc $loc) (mkstr $loc $1) }
  // HACK: Some match cases look like functions
  | FUN? lparen tuple_patterns rparen { Pat.tuple ~loc:(to_loc $loc) $3 }
  | lbrackrcaret patterns rbrack { Pat.array ~loc:(to_loc $loc) $2 }
  | lbrackrcaret rbrack { Pat.array ~loc:(to_loc $loc) [] }
  | FUN? lparen pattern rparen { $3 }
  | lbrace record_patterns rbrace { Pat.record ~loc:(to_loc $loc) $2 }
  | type_id FUN? lparen patterns rparen { Pat.construct ~loc:(to_loc $loc) $1 $4 }
  | type_id { Pat.construct ~loc:(to_loc $loc) $1 [] }
  | lbrack lseparated_list(comma, list_item_pat) trailing_comma? rbrack { Pat.list ~loc:(to_loc $loc) $2 }
  // | lbrack ellipsis_prefix(any_or_var_pat)? rbrack { Pat.list ~loc:(to_loc $loc) [] $2 }

// any_or_var_pat :
//   | UNDERSCORE { Pat.any ~loc:(to_loc $loc) () }
//   | ID { Pat.var ~loc:(to_loc $loc) (mkstr $loc $1) }

list_item_pat :
  | ELLIPSIS pattern { ListSpread $2 }
  | pattern { ListItem $1 }

comma_prefix(X) :
  | comma X {$2}

patterns :
  | lseparated_nonempty_list(comma, pattern) trailing_comma? { $1 }

%inline tuple_pattern_ending :
  | ioption(eols) lseparated_nonempty_list(comma, pattern) ioption(trailing_comma) { $2 }

tuple_patterns :
  // | pattern comma { [$1] }
  // | pattern comma_prefix(pattern)+ trailing_comma? { $1::$2 }
  | pattern COMMA ioption(tuple_pattern_ending) { $1::(Option.value ~default:[] $3) }

record_patterns :
  | lseparated_nonempty_list(comma, record_pattern) trailing_comma? { $1 }

record_pattern :
  | UNDERSCORE { None, Open }
  | id colon pattern { Some($1, $3), Closed }
  | id { Some($1, Pat.var ~loc:(to_loc $loc) (mkstr $loc (Identifier.last $1.txt))), Closed }

data_typ :
  | type_id lcaret typs rcaret { Typ.constr ~loc:(to_loc $loc) $1 $3 }
  // Resolve Foo < n > abiguity in favor of the type vector
  | type_id %prec _below_infix { Typ.constr ~loc:(to_loc $loc) $1 [] }

typ :
  | data_typ arrow typ { Typ.arrow ~loc:(to_loc $loc) [$1] $3 }
  | FUN ID arrow typ { Typ.arrow ~loc:(to_loc $loc) [(Typ.var $2)] $4 }
  | FUN lparen typs? rparen arrow typ { Typ.arrow ~loc:(to_loc $loc) (Option.value ~default:[] $3) $6 }
  | lparen tuple_typs rparen { Typ.tuple ~loc:(to_loc $loc) $2 }
  | lparen typ rparen { $2 }
  | ID { Typ.var ~loc:(to_loc $loc) $1 }
  | data_typ { $1 }

typs :
  // | separated_nonempty_list_trailing(comma, typ) { $1 }
  | lseparated_nonempty_list(comma, typ) trailing_comma? { $1 }
  // | typ comma_prefix(typ)* trailing_comma? { $1::$2 }

%inline tuple_typ_ending :
  | ioption(eols) lseparated_nonempty_list(comma, typ) ioption(trailing_comma) { $2 }

tuple_typs :
  | typ COMMA ioption(tuple_typ_ending) { $1::(Option.value ~default:[] $3) }
  // | separated_nonempty_list_trailing(comma, typ) { $1 }
  // | typ comma_prefix(typ)+ { $1::$2 }

value_bind :
  | pattern equal expr { Vb.mk ~loc:(to_loc $loc) $1 $3 }

value_binds :
  | value_bind comma_prefix(value_bind)* { $1::$2 }

import_exception :
  | EXCEPT lbrace lseparated_nonempty_list(comma, id) trailing_comma? rbrace {$3}

as_prefix(X) :
  | AS X {$2}

aliasable(X) :
  | X as_prefix(X)? {($1, $2)}

import_ids :
  | lseparated_nonempty_list(comma, aliasable(id)) trailing_comma? {$1}

import_shape :
  | id { PImportModule $1 }
  | STAR import_exception? { PImportAllExcept (Option.value ~default:[] $2) }
  | lbrace import_ids? rbrace { PImportValues (Option.value ~default:[] $2) }

import_stmt :
  | IMPORT lseparated_nonempty_list(comma, import_shape) trailing_comma? FROM file_path { Imp.mk ~loc:(to_loc $loc) $2 $5 }

data_declaration_stmt :
  // TODO: Attach attributes to the node
  | attributes EXPORT data_declaration { (Exported, $3) }
  | attributes data_declaration { (Nonexported, $2) }

data_declaration_stmts :
  | separated_nonempty_list(comma, data_declaration_stmt) { $1 }

export_exception :
  | EXCEPT export_id_str comma_prefix(export_id_str)* {$2::$3}

export_stmt :
  | attributes EXPORT LET REC value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Exported Recursive Immutable $5 }
  | attributes EXPORT LET value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Exported Nonrecursive Immutable $4 }
  | attributes EXPORT LET REC MUT value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Exported Recursive Mutable $6 }
  | attributes EXPORT LET MUT value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Exported Nonrecursive Mutable $5 }
  | attributes EXPORT foreign_stmt { Top.foreign ~loc:(to_loc $loc) ~attributes:$1 Exported $3 }
  | attributes EXPORT primitive_stmt { Top.primitive ~loc:(to_loc $loc) ~attributes:$1 Exported $3 }
  | attributes EXPORT exception_stmt { Top.grain_exception ~loc:(to_loc $loc) ~attributes:$1 Exported $3 }
  | attributes EXPORT separated_nonempty_list(comma, aliasable(any_id_str)) { Top.export ~loc:(to_loc $loc) ~attributes:$1 (Ex.mk ~loc:(to_loc $loc) $3) }
  | attributes EXPORT STAR export_exception? { Top.export_all ~loc:(to_loc $loc) ~attributes:$1 (Option.value ~default:[] $4) }

data_constructor :
  | TYPEID { CDecl.singleton ~loc:(to_loc $loc) (mkstr $loc $1) }
  | TYPEID lparen typs? rparen { CDecl.tuple ~loc:(to_loc $loc) (mkstr $loc $1) (Option.value ~default:[] $3) }
  /* Special support for lists */
  | lbrack rbrack { CDecl.singleton ~loc:(to_loc $loc) (mkstr $loc "[]") }
  | lbrack ELLIPSIS rbrack lparen typs? rparen { CDecl.tuple ~loc:(to_loc $loc) (mkstr $loc "[...]") (Option.value ~default:[] $5) }

data_constructors :
  | lbrace lseparated_nonempty_list(comma, data_constructor) trailing_comma? rbrace { $2 }
  // | lbrace data_constructor comma_prefix(data_constructor)* trailing_comma? rbrace { $2::$3 }

data_label :
  | simple_id colon typ { LDecl.mk ~loc:(to_loc $loc) $1 $3 Immutable }
  | MUT simple_id colon typ { LDecl.mk ~loc:(to_loc $loc) $2 $4 Mutable }

data_labels :
  | lbrace lseparated_nonempty_list(comma, data_label) trailing_comma? rbrace { $2 }

id_typ :
  | ID { Typ.var ~loc:(to_loc $loc) $1 }

id_vec :
  | lcaret id_typ comma_prefix(id_typ)* rcaret {$2::$3}

data_declaration :
  | ENUM TYPEID id_vec? data_constructors { Dat.variant ~loc:(to_loc $loc) (mkstr $loc $2) (Option.value ~default:[] $3) $4 }
  | RECORD TYPEID id_vec? data_labels { Dat.record ~loc:(to_loc $loc) (mkstr $loc $2) (Option.value ~default:[] $3) $4 }

prim1_expr :
  | NOT non_assign_expr { Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($1) ["!"]) [$2] }

paren_expr :
  | lparen expr rparen { $2 }

// app_arg_exprs :
//   | lseparated_list(comma, expr) { $1 }

app_expr :
  | left_accessor_expr lparen lseparated_list(comma, expr) trailing_comma? rparen { Exp.apply ~loc:(to_loc $loc) $1 $3 }

// dot_prefix(X) :
//   | dot X {$2}

// ext_constructor :
//   | TYPEID dot_prefix(TYPEID)+ { (mkid ($1::$2)) (to_loc $loc) }
  // | TYPEID dot_prefix(TYPEID)+ { (mkid ($1::$2)) (to_loc $loc) }

%inline plus_op :
  | PLUS { "+" }
%inline plusplus_op :
  | PLUSPLUS { "++" }
%inline dash_op :
  | DASH { "-" }
%inline star_op :
  | STAR { "*" }
%inline slash_op :
  | SLASH { "/" }
%inline percent_op :
  | PERCENT { "%" }
%inline is_op :
  | IS { "is" }
%inline isnt_op :
  | ISNT { "isnt" }
%inline eqeq_op :
  | EQEQ { "==" }
%inline noteq_op :
  | NOTEQ { "!=" }
%inline caret_op :
  | CARET { "^" }
%inline lcaret_op :
  | LCARET { "<" }
%inline llcaret_op :
  | LCARETLCARET { "<<" }
%inline rcaret_op :
  | RCARET { ">" }
%inline rrcaret_op :
  | RCARETRCARET { ">>" }
%inline rrrcaret_op :
  | RCARETRCARETRCARET { ">>>" }
%inline lesseq_op :
  | LESSEQ { "<=" }
%inline greatereq_op :
  | GREATEREQ { ">=" }
%inline amp_op :
  | AMP { "&" }
%inline ampamp_op :
  | AMPAMP { "&&" }
%inline pipe_op :
  | PIPE { "|" }
%inline pipepipe_op :
  | PIPEPIPE { "||" }
%inline pluseq_op :
  | PLUSEQ { "+" }
%inline dasheq_op :
  | DASHEQ { "-" }
%inline stareq_op :
  | STAREQ { "*" }
%inline slasheq_op :
  | SLASHEQ { "/" }
%inline percenteq_op :
  | PERCENTEQ { "%" }

%inline infix_op :
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
  | pipepipe_op {$1}

prefix_op :
  | NOT { "!" }

primitive_ :
  | ASSERT { "assert" }
  | THROW { "throw" }
  | FAIL { "fail" }

special_op :
  | infix_op | prefix_op {$1}

%inline special_id :
  | lparen special_op rparen { $2 }

// %inline all_ids :
//   | ID | TYPEID | special_id {$1}

%inline separated_list_trailing(sep, X) :
  | separated_list(sep, X) ioption(sep) {$1}

%inline separated_nonempty_list_trailing(sep, X) :
  | separated_nonempty_list(sep, X) ioption(sep) {$1}

%inline separated_list_trailing_required(sep, X) :
  | separated_list(sep, X) sep {$1}

%inline separated_nonempty_list_trailing_required(sep, X) :
  | separated_nonempty_list(sep, X) sep {$1}

%inline modid :
  | lseparated_nonempty_list(dot, TYPEID) { $1 }

non_modid :
  | ID
  | special_id { [$1] }

id :
  // | separated_nonempty_list_trailing_required(dot, TYPEID)? all_ids { (mkid (List.append (Option.value ~default:[] $1) [$2])) (to_loc $loc) }
  // | separated_nonempty_list(dot, TYPEID) dot all_ids { (mkid (List.append $1 [$3])) (to_loc $loc) }
  // | TYPEID dot longid { $1::$3 }
  // | all_ids opt_eols { [$1] }
  | modid dot non_modid { mkid (List.append $1 $3) (to_loc $loc) }
  | modid %prec DOT { (mkid $1) (to_loc $loc) }
  | non_modid { (mkid $1) (to_loc $loc) }

// id :
//   | longid { (mkid $1) (to_loc $loc) }

simple_id :
  | ID { (mkid [$1]) (to_loc $loc) }

type_id :
  | separated_nonempty_list(dot, TYPEID) { (mkid $1) (to_loc $loc) }
  // | TYPEID dot_prefix(TYPEID)* { (mkid ($1::$2)) (to_loc $loc) }

id_expr :
  // Force any following colon to cause a shift
  | id %prec COLON { Exp.ident ~loc:(to_loc $loc) $1 }

simple_expr :
  | const { Exp.constant ~loc:(to_loc $loc) $1 }
  | lparen tuple_exprs rparen { Exp.tuple ~loc:(to_loc $loc) $2 }
  | id_expr { $1 }

braced_expr :
  | lbrace block_body rbrace { Exp.block ~loc:(to_loc $loc) $2 } // FIXME
  | lbrace record_exprs rbrace { Exp.record ~loc:(to_loc $loc) $2 }

block :
  | lbrace block_body rbrace { Exp.block ~loc:(to_loc $loc) $2 }

block_or_expr :
  // | block { $1 }
  | expr { $1 } // FIXME

lam_expr :
  | FUN lparen patterns? rparen thickarrow block_or_expr { Exp.lambda ~loc:(to_loc $loc) (Option.value ~default:[] $3) $6 }
  | FUN ID thickarrow block_or_expr { Exp.lambda ~loc:(to_loc $loc) [Pat.var ~loc:(to_loc $loc($2)) (mkstr $loc($2) $2)] $4 }

attribute :
  | AT id_str opt_eols {$2}

attributes :
  | attribute* { $1 }

let_expr :
  | attributes LET REC value_binds { Exp.let_ ~loc:(to_loc $loc) ~attributes:$1 Recursive Immutable $4 }
  | attributes LET value_binds { Exp.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonrecursive Immutable $3 }
  | attributes LET REC MUT value_binds { Exp.let_ ~loc:(to_loc $loc) ~attributes:$1 Recursive Mutable $5 }
  | attributes LET MUT value_binds { Exp.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonrecursive Mutable $4 }

%inline else_expr :
  | ELSE opt_eols block_or_expr { $3 }

if_expr :
  // | IF lparen expr rparen opt_eols block_or_expr { Exp.if_ ~loc:(to_loc $loc) $3 $6 (Exp.block []) }
  | IF lparen expr rparen opt_eols block_or_expr ioption(else_expr) %prec _if { Exp.if_ ~loc:(to_loc $loc) $3 $6 (Option.value ~default:(Exp.block ~loc:(to_loc $loc($7)) []) $7) }

// one_sided_if_expr :
//   | IF lparen expr rparen opt_eols block_or_expr { Exp.if_ ~loc:(to_loc $loc) $3 $6 (Exp.block []) }

while_expr :
  | WHILE lparen expr rparen block { Exp.while_ ~loc:(to_loc $loc) $3 $5 }

for_inner_expr :
  | %prec EOL { None }
  | expr { Some $1 }

for_expr :
  | FOR lparen block_body_expr? opt_eols SEMI opt_eols for_inner_expr opt_eols SEMI opt_eols for_inner_expr rparen block { Exp.for_ ~loc:(to_loc $loc) $3 $7 $11 $13 }

when_guard :
  | WHEN expr {$2}

match_branch :
  | pattern when_guard? thickarrow expr { Mb.mk ~loc:(to_loc $loc) $1 $4 $2 }

match_branches :
  | lseparated_nonempty_list(comma, match_branch) trailing_comma? { $1 }

match_expr :
  | MATCH lparen expr rparen lbrace match_branches rbrace { Exp.match_ ~loc:(to_loc $loc) $3 $6 }

// list_expr_ending :
//   | trailing_comma? { None }
//   | comma ELLIPSIS expr { Some $3 }

// list_expr_ending :
//   | trailing_comma? { None }
//   | comma ELLIPSIS expr { Some $3 }

// list_spread :
//   | comma ELLIPSIS expr { $3 }

list_item :
  | ELLIPSIS expr { ListSpread $2 }
  | expr { ListItem $1 }

list_expr :
  // | lbrack rbrack { Exp.list ~loc:(to_loc $loc) [] None }
  | lbrack lseparated_list(comma, list_item) trailing_comma? rbrack { Exp.list ~loc:(to_loc $loc) $2 }

array_expr :
  | lbrackrcaret rbrack { Exp.array ~loc:(to_loc $loc) [] }
  | lbrackrcaret opt_eols lseparated_nonempty_list(comma, expr) trailing_comma? rbrack { Exp.array ~loc:(to_loc $loc) $3 }

stmt_expr :
  | THROW expr { Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($1) ["throw"]) [$2] }
  | ASSERT expr { Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($1) ["assert"]) [$2] }
  | FAIL expr { Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($1) ["fail"]) [$2] }
  | CONTINUE { Exp.continue ~loc:(to_loc $loc) () }
  | BREAK { Exp.break ~loc:(to_loc $loc) () }

assign_binop_op :
  | pluseq_op
  | dasheq_op
  | stareq_op
  | slasheq_op
  | percenteq_op {$1}

assign_expr :
  | left_accessor_expr GETS opt_eols expr { Exp.box_assign ~loc:(to_loc $loc) $1 $4 } // FIXME
  | id_expr equal expr { Exp.assign ~loc:(to_loc $loc) $1 $3 }
  | id_expr assign_binop_op opt_eols expr { Exp.assign ~loc:(to_loc $loc) $1 (Exp.apply ~loc:(to_loc $loc) (mkid_expr $loc($2) [$2]) [$1; $4]) }
  | record_set { $1 }
  | array_set { $1 }

non_assign_expr :
  | app_expr    { $1 }
  | prim1_expr  { $1 }
  | simple_expr { $1 }
  | record_get  { $1 }
  | paren_expr  { $1 }
  | braced_expr  { $1 }
  | if_expr     { $1 }
  | while_expr  { $1 }
  | for_expr    { $1 }
  | match_expr  { $1 }
  | list_expr   { $1 }
  | array_get   { $1 }
  | array_expr  { $1 }

%inline left_accessor_expr :
  | app_expr    { $1 }
  | simple_expr { $1 }
  /*| array_get   { $1 }*/
  | record_get  { $1 }
  | paren_expr  { $1 }
  | braced_expr  { $1 }

block_body_expr :
  | let_expr    { $1 }
  | expr  { $1 }

// %inline block_body_stmt :
//   | eos block_body_expr { $2 }

lseparated_nonempty_list(sep, X) :
  | lseparated_nonempty_list(sep, X) sep X { $1 @ [$3] }
  | X { [$1] }

%inline lseparated_list(sep, X) :
  | { [] }
  | lseparated_nonempty_list(sep, X) { $1 }

// tuple_expr_list :
//   | tuple_expr_list expr comma { $1 @ [$2] }
//   | expr comma { [$1] }

// special_eols :
//   | eols? %prec EOL { () }

%inline tuple_expr_ending :
  | ioption(eols) lseparated_nonempty_list(comma, expr) trailing_comma? { $2 }

tuple_exprs :
  // | expr comma { [$1] }
  // | expr comma_prefix(expr)+ ioption(trailing_comma) { $1::$2 }
  // | tuple_expr_list expr? { Option.fold ~some:(fun x -> $1 @ [x]) ~none:$1 $2 }
  | expr COMMA ioption(tuple_expr_ending) { $1::(Option.value ~default:[] $3) }
  // | separated_nonempty_list_trailing_required(comma, expr) { $1 }
  // | expr comma separated_list_trailing(comma, expr) { $1::$3 }
  // | separated_nonempty_list(comma, expr) { $1 }

array_get :
  | left_accessor_expr lbrack expr rbrack { Exp.array_get ~loc:(to_loc $loc) $1 $3 }

array_set :
  | left_accessor_expr lbrack expr rbrack equal expr { Exp.array_set ~loc:(to_loc $loc) $1 $3 $6 }

record_get :
  | left_accessor_expr dot simple_id { Exp.record_get ~loc:(to_loc $loc) $1 $3 }

record_set :
  | left_accessor_expr dot simple_id equal expr { Exp.record_set ~loc:(to_loc $loc) $1 $3 $5 }

%inline record_field_value :
  | colon expr {$2}

punned_record_field :
  | id { $1, (Exp.ident ~loc:(to_loc $loc) $1) }

non_punned_record_field :
  | id record_field_value { $1, $2 }

record_field :
  | punned_record_field { $1 }
  | non_punned_record_field %prec COMMA { $1 }

// record_exprs_inner :
//   | record_exprs_inner comma record_field { $1 @ [$3] }
//   | record_field comma record_field { [$1; $3] }

record_exprs :
  // Don't ever parse {x} as a record
  | non_punned_record_field trailing_comma? { [$1] }
  | record_field comma lseparated_nonempty_list(comma, record_field) trailing_comma? { $1::$3 }

// block_body_inner :
//   | block_body_inner eos block_body_expr { $3::$1 }
//   | block_body_expr { [$1] }

block_body :
  // | block_body_expr block_body_stmt* SEMI? { $1::$2 }
  // | separated_nonempty_list(eos, block_body_expr) ioption(eos) { $1 }
  | lseparated_nonempty_list(eos, block_body_expr) ioption(eos) %prec SEMI { $1 }

file_path :
  | STRING { Location.mkloc $1 (to_loc $loc) }

id_str :
  | ID { Location.mkloc $1 (to_loc $loc) }
  | special_id { Location.mkloc $1 (to_loc $loc) }

type_id_str :
  | TYPEID { Location.mkloc $1 (to_loc $loc) }

any_id_str :
  | id_str { $1 }
  | type_id_str { $1 }

export_id_str :
  | id_str { ExportExceptValue $1 }
  | type_id_str { ExportExceptData $1 }

foreign_stmt :
  | FOREIGN WASM id_str colon typ as_prefix(id_str)? FROM file_path { Val.mk ~loc:(to_loc $loc) ~mod_:$8 ~name:$3 ~alias:$6 ~typ:$5 ~prim:[] }

prim :
  | primitive_ { Location.mkloc $1 (to_loc $loc) }

primitive_stmt :
  | PRIMITIVE id_str colon typ equal STRING { Val.mk ~loc:(to_loc $loc) ~mod_:{$2 with txt="primitive"} ~name:$2 ~alias:None ~typ:$4 ~prim:[$6] }
  | PRIMITIVE prim colon typ equal STRING { Val.mk ~loc:(to_loc $loc) ~mod_:{$2 with txt="primitive"} ~name:$2 ~alias:None ~typ:$4 ~prim:[$6] }

exception_stmt :
  | EXCEPTION type_id_str { Except.singleton ~loc:(to_loc $loc) $2 }
  | EXCEPTION type_id_str lparen typs? rparen { Except.tuple ~loc:(to_loc $loc) $2 (Option.value ~default:[] $4) }

toplevel_stmt :
  | attributes LET REC value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonexported Recursive Immutable $4 }
  | attributes LET value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonexported Nonrecursive Immutable $3 }
  | attributes LET REC MUT value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonexported Recursive Mutable $5 }
  | attributes LET MUT value_binds { Top.let_ ~loc:(to_loc $loc) ~attributes:$1 Nonexported Nonrecursive Mutable $4 }
  | expr { Top.expr ~loc:(to_loc $loc) $1 }
  | import_stmt { Top.import ~loc:(to_loc $loc) $1 }
  | IMPORT foreign_stmt { Top.foreign ~loc:(to_loc $loc) Nonexported $2 }
  | data_declaration_stmts { Top.data ~loc:(to_loc $loc) $1 }
  | export_stmt { $1 }
  | primitive_stmt { Top.primitive ~loc:(to_loc $loc) Nonexported $1 }
  | exception_stmt { Top.grain_exception ~loc:(to_loc $loc) Nonexported $1 }

toplevel_stmts :
  | toplevel_stmts eos toplevel_stmt { $3::$1 }
  | toplevel_stmt { [$1] }
  // | separated_nonempty_list(eos, toplevel_stmt) { $1 }

program :
  | opt_eols toplevel_stmts ioption(eos) EOF { make_program (List.rev $2) }
