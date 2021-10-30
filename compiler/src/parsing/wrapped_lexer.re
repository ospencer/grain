/**
 This module was inspired by ReasonML's lexer.
 LR grammars have a terrible time determining if the expression
    (foo, bar, baz)
 is a tuple or the beginning of the function definition
    (foo, bar, baz) => { ... }
 as they would need to continuously shift all tokens and delay all
 reductions until the arrow was (or was not) encountered. (A tuple
 expression would contain more subexpressions, while function
 arguments can be arbitrary patterns.) This would be awfully
 difficult to express in terms of the grammar, so instead we inject
 FUN tokens during lexing if we see the pattern
    ( ... ) =>
    or
    ( ... ) =>
 */
open Parser;

type positioned('a) = ('a, Lexing.position, Lexing.position);

type fn_ctx =
  | DiscoverFunctions
  | IgnoreFunctions;

type t = {
  lexbuf: Lexing.lexbuf,
  mutable queued_tokens: list(positioned(token)),
  mutable queued_exn: option(exn),
  mutable fn_ctx_stack: list(fn_ctx),
};

let init = lexbuf => {
  {lexbuf, queued_tokens: [], queued_exn: None, fn_ctx_stack: []};
};

let lexbuf = state => state.lexbuf;

let token = state => {
  Lexer.token(state.lexbuf);
};

let save_triple = (lexbuf, tok) => (
  tok,
  lexbuf.Lexing.lex_start_p,
  lexbuf.Lexing.lex_curr_p,
);

let fake_triple = (t, (_, pos, _)) => (t, pos, pos);

exception Lex_balanced_failed(list(positioned(token)), option(exn));
exception Lex_fast_forward_failed(list(positioned(token)), option(exn));

let inject_fun =
  fun
  | [tok, ...acc] => [tok, fake_triple(FUN, tok), ...acc]
  | _ => assert(false);

let is_triggering_token =
  fun
  | THICKARROW
  | ARROW => true
  | _ => false;

let rec lex_fast_forward_step = (state, stop, acc, tok) => {
  let lexbuf = state.lexbuf;
  let acc = [save_triple(lexbuf, tok), ...acc];
  switch (tok, stop) {
  | _ when tok == stop => acc
  | (EOF, _) => raise(Lex_fast_forward_failed(acc, None))
  | _ => lex_fast_forward(state, stop, acc)
  };
}

and lex_fast_forward = (state, stop, acc) =>
  switch (token(state)) {
  | exception exn => raise(Lex_fast_forward_failed(acc, Some(exn)))
  | tok => lex_fast_forward_step(state, stop, acc, tok)
  };

let push_fn_ctx = (state, ctx) => {
  state.fn_ctx_stack = [ctx, ...state.fn_ctx_stack];
};

let pop_fn_ctx = state => {
  switch (state.fn_ctx_stack) {
  | [hd, ...tl] => state.fn_ctx_stack = tl
  | _ => assert(false)
  };
};

let ignore_fns = state => {
  switch (state.fn_ctx_stack) {
  | [IgnoreFunctions, ...tl] => true
  | _ => false
  };
};

let rec lex_balanced_step = (state, closing, acc, tok) => {
  let lexbuf = state.lexbuf;
  let acc = [save_triple(lexbuf, tok), ...acc];
  switch (tok, closing) {
  | (RPAREN, RPAREN)
  | (RBRACE, RBRACE)
  | (RBRACK, RBRACK) =>
    pop_fn_ctx(state);
    acc;
  | (RPAREN | RBRACE | RBRACK | EOF, _) =>
    raise(Lex_balanced_failed(acc, None))
  | (LBRACK, _) =>
    lex_balanced(
      state,
      closing,
      lex_balanced(~push=DiscoverFunctions, state, RBRACK, acc),
    )
  | (LBRACE, _) =>
    lex_balanced(
      state,
      closing,
      lex_balanced(~push=DiscoverFunctions, state, RBRACE, acc),
    )
  | (LPAREN, _) when ignore_fns(state) =>
    lex_balanced(
      state,
      closing,
      lex_balanced(~push=DiscoverFunctions, state, RPAREN, acc),
    )
  | (LPAREN, _) =>
    let rparen =
      try(lex_balanced(~push=DiscoverFunctions, state, RPAREN, [])) {
      | Lex_balanced_failed(rparen, None) =>
        raise(Lex_balanced_failed(rparen @ acc, None))
      };

    switch (token(state)) {
    | exception exn => raise(Lex_balanced_failed(rparen @ acc, Some(exn)))
    | tok' =>
      let acc =
        if (is_triggering_token(tok')) {
          inject_fun(acc);
        } else {
          acc;
        };
      lex_balanced_step(state, closing, rparen @ acc, tok');
    };
  | (MATCH, _) =>
    lex_balanced(
      state,
      closing,
      lex_balanced(
        ~push=IgnoreFunctions,
        state,
        RBRACE,
        lex_fast_forward(
          state,
          LBRACE,
          lex_balanced(
            ~push=DiscoverFunctions,
            state,
            RPAREN,
            lex_fast_forward(state, LPAREN, acc),
          ),
        ),
      ),
    )
  | (ID(_) | UNDERSCORE, _) when !ignore_fns(state) =>
    switch (token(state)) {
    | exception exn => raise(Lex_balanced_failed(acc, Some(exn)))
    | tok' =>
      let acc =
        if (is_triggering_token(tok')) {
          inject_fun(acc);
        } else {
          acc;
        };
      lex_balanced_step(state, closing, acc, tok');
    }
  | _ => lex_balanced(state, closing, acc)
  };
}

and lex_balanced = (~push=?, state, closing, acc) => {
  Option.iter(push_fn_ctx(state), push);
  switch (token(state)) {
  | exception exn => raise(Lex_balanced_failed(acc, Some(exn)))
  | tok => lex_balanced_step(state, closing, acc, tok)
  };
}

and lookahead_fun = (state, (tok, _, _) as lparen) =>
  switch (lex_balanced(~push=DiscoverFunctions, state, RPAREN, [])) {
  | exception (Lex_balanced_failed(tokens, exn)) =>
    state.queued_tokens = List.rev(tokens);
    state.queued_exn = exn;
    lparen;
  | tokens =>
    switch (token(state)) {
    | exception exn =>
      state.queued_tokens = List.rev(tokens);
      state.queued_exn = Some(exn);
      lparen;
    | token =>
      let tokens = [save_triple(state.lexbuf, token), ...tokens];
      if (is_triggering_token(token)) {
        state.queued_tokens = [lparen, ...List.rev(tokens)];
        fake_triple(FUN, lparen);
      } else {
        state.queued_tokens = List.rev(tokens);
        lparen;
      };
    }
  }

and lookahead_match = state => {
  switch (lex_fast_forward(state, LPAREN, [])) {
  | exception (Lex_fast_forward_failed(tokens, exn)) =>
    state.queued_tokens = List.rev(tokens);
    state.queued_exn = exn;
    assert(false); // FIXME
  | first_ff_tokens =>
    switch (lex_balanced(~push=DiscoverFunctions, state, RPAREN, [])) {
    | exception (Lex_balanced_failed(tokens, exn)) =>
      state.queued_tokens = List.rev(tokens @ first_ff_tokens);
      state.queued_exn = exn;
      assert(false); // FIXME
    | tokens =>
      switch (lex_fast_forward(state, LBRACE, [])) {
      | exception exn =>
        state.queued_tokens = List.rev(tokens @ first_ff_tokens);
        state.queued_exn = Some(exn);
        assert(false); // FIXME
      | second_ff_tokens =>
        switch (lex_balanced(~push=IgnoreFunctions, state, RBRACE, [])) {
        | exception (Lex_balanced_failed(more_tokens, exn)) =>
          state.queued_tokens =
            List.rev(
              more_tokens @ second_ff_tokens @ tokens @ first_ff_tokens,
            );
          state.queued_exn = exn;
          assert(false); // FIXME
        | more_tokens =>
          state.queued_tokens =
            List.rev(
              more_tokens @ second_ff_tokens @ tokens @ first_ff_tokens,
            )
        }
      }
    }
  };
};

let token = state => {
  let lexbuf = state.lexbuf;
  switch (state.queued_tokens, state.queued_exn) {
  | ([], Some(exn)) =>
    state.queued_exn = None;
    raise(exn);
  | ([(MATCH, _, _) as match], None) =>
    lookahead_match(state);
    match;
  | ([(LPAREN, _, _) as lparen], None) => lookahead_fun(state, lparen)
  | ([], None) =>
    switch (token(state)) {
    | MATCH as tok =>
      lookahead_match(state);
      save_triple(state.lexbuf, tok);
    | LPAREN as tok => lookahead_fun(state, save_triple(state.lexbuf, tok))
    | (ID(_) | UNDERSCORE) as tok =>
      let tok = save_triple(lexbuf, tok);
      switch (token(state)) {
      | exception exn =>
        state.queued_exn = Some(exn);
        tok;
      | tok' =>
        if (is_triggering_token(tok')) {
          state.queued_tokens = [tok, save_triple(lexbuf, tok')];
          fake_triple(FUN, tok);
        } else {
          state.queued_tokens = [save_triple(lexbuf, tok')];
          tok;
        }
      };
    | token => save_triple(lexbuf, token)
    }
  | ([x, ...xs], _) =>
    state.queued_tokens = xs;
    x;
  };
};

let token = state => {
  let (token, _, _) = token(state);
  token;
};
