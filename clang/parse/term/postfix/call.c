fn Term parse_term(PState *s, u32 depth);

fn Term parse_postfix_call(Term f, PState *s, u32 depth, int min_prec) {
  (void)min_prec;
  if (parse_peek(s) != '(') return 0;
  parse_consume(s, "(");
  if (parse_peek(s) == ')') {
    parse_consume(s, ")");
    return f;
  }
  while (1) {
    Term arg = parse_term(s, depth);
    f = term_new_app(f, arg);
    parse_skip(s);
    parse_match(s, ",");  // optional comma
    parse_skip(s);
    if (parse_peek(s) == ')') {
      parse_consume(s, ")");
      break;
    }
  }
  return f;
}
