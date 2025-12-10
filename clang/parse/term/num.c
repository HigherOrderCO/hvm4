fn Term parse_term_num(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!isdigit(parse_peek(s))) return 0;
  parse_skip(s);
  u32 n = 0;
  int has = 0;
  while (isdigit(parse_peek(s))) {
    has = 1;
    n = n * 10 + (u32)(parse_peek(s) - '0');
    parse_advance(s);
  }
  if (!has) {
    parse_error(s, PERR_EXPECTED("number", parse_peek(s)));
  }
  parse_skip(s);
  return term_new_num(n);
}
