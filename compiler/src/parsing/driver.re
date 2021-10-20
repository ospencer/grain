/** External frontend for running the parser. */
open Lexing;
open Location;

type error =
  | AmbiguousParse(list(Parsetree.parsed_program))
  | NoValidParse;

let report_error = ppf =>
  fun
  | AmbiguousParse(parses) =>
    if (Grain_utils.Config.verbose^
        || Grain_utils.Config.parser_debug_level^ > 0) {
      Format.fprintf(
        ppf,
        "The Grain compiler had trouble parsing your program. Here were the potential parses:@\n@[<v>%a@]",
        ppf =>
          List.iter(x =>
            Format.fprintf(
              ppf,
              "@[%s@]%,",
              Sexplib.Sexp.to_string_hum @@
              Parsetree.sexp_of_parsed_program(x),
            )
          ),
        parses,
      );
    } else {
      Format.fprintf(
        ppf,
        "The Grain compiler had trouble parsing your program.",
      );
    }
  | NoValidParse =>
    Format.fprintf(
      ppf,
      "The Grain compiler was unable to parse your program. If you see this message, please file an issue at https://github.com/grain-lang/grain",
    );

exception Error(Location.t, error);

let () =
  Location.register_error_of_exn(
    fun
    | Error(loc, err) =>
      Some(Location.error_of_printer(loc, report_error, err))
    | _ => None,
  );

let apply_filename_to_lexbuf = (name, lexbuf) => {
  lexbuf.lex_curr_p = {...lexbuf.lex_curr_p, pos_fname: name};
  Location.input_name := name;
};

open Parser;
let string_of_tok =
  fun
  | WHILE => "WHILE"
  | WHEN => "WHEN"
  | WASMI64(s) => "WASMI64(" ++ s ++ ")"
  | WASMI32(s) => "WASMI32(" ++ s ++ ")"
  | WASMF64(s) => "WASMF64(" ++ s ++ ")"
  | WASMF32(s) => "WASMF32(" ++ s ++ ")"
  | WASM => "WASM"
  | VOID => "VOID"
  | UNDERSCORE => "UNDERSCORE"
  | TYPEID(s) => "TYPEID(" ++ s ++ ")"
  | TRY => "TRY"
  | TRUE => "TRUE"
  | THROW => "THROW"
  | THICKARROW => "THICKARROW"
  | STRING(s) => "STRING(" ++ s ++ ")"
  | STAREQ => "STAREQ"
  | STAR => "STAR"
  | SLASHEQ => "SLASHEQ"
  | SLASH => "SLASH"
  | SEMI => "SEMI"
  | RPAREN => "RPAREN"
  | RECORD => "RECORD"
  | REC => "REC"
  | RCARETRCARETRCARET => "RCARETRCARETRCARET"
  | RCARETRCARET => "RCARETRCARET"
  | RCARET => "RCARET"
  | RBRACK => "RBRACK"
  | RBRACE => "RBRACE"
  | PRIMITIVE => "PRIMITIVE"
  | PLUSPLUS => "PLUSPLUS"
  | PLUSEQ => "PLUSEQ"
  | PLUS => "PLUS"
  | PIPEPIPE => "PIPEPIPE"
  | PIPE => "PIPE"
  | PERCENTEQ => "PERCENTEQ"
  | PERCENT => "PERCENT"
  | NUMBER_INT(s) => "NUMBER_INT(" ++ s ++ ")"
  | NUMBER_FLOAT(s) => "NUMBER_FLOAT(" ++ s ++ ")"
  | NOTEQ => "NOTEQ"
  | NOT => "NOT"
  | MUT => "MUT"
  | MATCH => "MATCH"
  | LPAREN => "LPAREN"
  | LET => "LET"
  | LESSEQ => "LESSEQ"
  | LCARETLCARET => "LCARETLCARET"
  | LCARET => "LCARET"
  | LBRACK => "LBRACK"
  | LBRACE => "LBRACE"
  | ISNT => "ISNT"
  | IS => "IS"
  | INT64(s) => "INT64(" ++ s ++ ")"
  | INT32(s) => "INT32(" ++ s ++ ")"
  | IMPORT => "IMPORT"
  | IF => "IF"
  | ID(s) => "ID(" ++ s ++ ")"
  | GREATEREQ => "GREATEREQ"
  | GETS => "GETS"
  | FUN => "FUN"
  | FROM => "FROM"
  | FOREIGN => "FOREIGN"
  | FOR => "FOR"
  | FLOAT64(s) => "FLOAT64(" ++ s ++ ")"
  | FLOAT32(s) => "FLOAT32(" ++ s ++ ")"
  | FALSE => "FALSE"
  | FAIL => "FAIL"
  | EXPORT => "EXPORT"
  | EXCEPTION => "EXCEPTION"
  | EXCEPT => "EXCEPT"
  | EQUAL => "EQUAL"
  | EQEQ => "EQEQ"
  | EOL => "EOL"
  | EOF => "EOF"
  | ENUM => "ENUM"
  | ELSE => "ELSE"
  | ELLIPSIS => "ELLIPSIS"
  | DOT => "DOT"
  | DASHEQ => "DASHEQ"
  | DASH => "DASH"
  | CONTINUE => "CONTINUE"
  | COMMA => "COMMA"
  | COLONCOLON => "COLONCOLON"
  | COLON => "COLON"
  | CHAR(s) => "CHAR(" ++ s ++ ")"
  | CATCH => "CATCH"
  | CARET => "CARET"
  | BREAK => "BREAK"
  | AT => "AT"
  | ASSERT => "ASSERT"
  | AS => "AS"
  | ARROW => "ARROW"
  | AMPAMP => "AMPAMP"
  | AMP => "AMP";

let inspect_token = (token, lexbuf) => {
  let tok = token(lexbuf);
  Printf.eprintf("%s ", string_of_tok(tok));
  tok;
};

// This parse is very fast, but cannot report useful errors.
// parse_program_for_syntax_error is 2-5x slower, but has real
// syntax error information.
let parse_program = Parser_header.parse_program(Parser.program);

module E = MenhirLib.ErrorReports;
module L = MenhirLib.LexerUtil;
module I = UnitActionsParser.MenhirInterpreter;

let env = checkpoint =>
  switch (checkpoint) {
  | I.HandlingError(env) => env
  | _ => assert(false)
  };

let state = checkpoint =>
  switch (I.top(env(checkpoint))) {
  | Some(I.Element(s, _, _, _)) => I.number(s)
  | None =>
    // The parser hasn't left its initial state. The state number is probably
    // zero, but it's not guaranteed. A future version of Menhir is supposed
    // to provide a real solution for this.
    0
  };

let show = (text, positions) =>
  E.extract(text, positions) |> E.sanitize |> E.compress |> E.shorten(20);

let get = (text, checkpoint, i) =>
  switch (I.get(i, env(checkpoint))) {
  | Some(I.Element(_, _, pos1, pos2)) => show(text, (pos1, pos2))
  | None => "???"
  };

let succeed = _v => assert(false);

let fail = (text, buffer, checkpoint: I.checkpoint(_)) => {
  /* Indicate where in the input file the error occurred. */
  let location = L.range(E.last(buffer));
  /* Show the tokens just before and just after the error. */
  let indication =
    Printf.sprintf("Syntax error %s.\n", E.show(show(text), buffer));
  /* Fetch an error message from the database. */
  // let message = ParserMessages.message(state(checkpoint));
  let message = "WHOOPS.\n";
  /* Expand away the $i keywords that might appear in the message. */
  let message = E.expand(get(text, checkpoint), message);
  /* Show these three components. */
  Printf.eprintf("%s%s%s%!", location, indication, message);
  exit(1);
};

let parse_program_for_syntax_error = (~name=?, lexbuf, source) => {
  Option.iter(n => {apply_filename_to_lexbuf(n, lexbuf)}, name);
  /* Allocate and initialize a lexing buffer. */
  /* Wrap the lexer and lexbuf together into a supplier, that is, a
     function of type [unit -> token * position * position]. */
  let supplier =
    I.lexer_lexbuf_to_supplier(inspect_token(Lexer.token), lexbuf);
  /* Equip the supplier with a two-place buffer that records the positions
     of the last two tokens. This is useful when a syntax error occurs, as
     these are the token just before and just after the error. */
  let (buffer, supplier) = E.wrap_supplier(supplier);
  /* Fetch the parser's initial checkpoint. */
  let checkpoint = UnitActionsParser.Incremental.program(lexbuf.lex_curr_p);
  /* Run the parser. */
  /* We do not handle [Lexer.Error] because we know that we will not
     encounter a lexical error during this second parsing run. */
  I.loop_handle(succeed, fail(source, buffer), supplier, checkpoint);
};

// let parse_program_for_syntax_error

let parse = (~name=?, lexbuf, source): Parsetree.parsed_program => {
  Option.iter(n => {apply_filename_to_lexbuf(n, lexbuf)}, name);
  let lexer = Wrapped_lexer.init(lexbuf);
  let token = _ => Wrapped_lexer.token(lexer);
  try({...parse_program(token, lexbuf), comments: Lexer.consume_comments()}) {
  | Parser.Error =>
    // Fast parse failed, so now we do a slow, thoughtful parse to produce a
    // good error message
    let source = source();
    ignore @@
    parse_program_for_syntax_error(
      ~name?,
      Lexing.from_string(source),
      source,
    );
    assert(false);
  };
};

let scan_for_imports = (~defer_errors=true, filename: string): list(string) => {
  let ic = open_in(filename);
  let lexbuf = Lexing.from_channel(ic);
  try({
    let source = () => {
      let ic = open_in_bin(filename);
      let source = really_input_string(ic, in_channel_length(ic));
      close_in(ic);
      source;
    };
    let {Parsetree.comments, Parsetree.statements} =
      parse(~name=filename, lexbuf, source);
    let implicit_opens =
      List.map(
        o => {
          switch (o) {
          | Grain_utils.Config.Pervasives_mod => "pervasives"
          | Grain_utils.Config.Gc_mod => "runtime/gc"
          }
        },
        switch (comments) {
        | [Block({cmt_content}), ..._] =>
          Grain_utils.Config.with_inline_flags(
            ~on_error=_ => (),
            cmt_content,
            Grain_utils.Config.get_implicit_opens,
          )
        | _ => Grain_utils.Config.get_implicit_opens()
        },
      );
    let found_imports = ref([]);
    let iter_mod = (self, import) =>
      found_imports := [import.Parsetree.pimp_path.txt, ...found_imports^];
    let iterator = {...Ast_iterator.default_iterator, import: iter_mod};
    List.iter(iterator.toplevel(iterator), statements);
    close_in(ic);
    List.sort_uniq(
      String.compare,
      List.append(implicit_opens, found_imports^),
    );
  }) {
  | e =>
    close_in(ic);
    if (!defer_errors) {
      raise(e);
    };
    []; // <- defer parse error until we try to compile this dependency
  // FIXME: we're exiting instead of throwing a real error here yikes
  };
};
