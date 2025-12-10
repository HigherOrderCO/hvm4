fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_lst(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  // parse_advance(s);
  if (!parse_match(s, "[")) return 0;
  parse_skip(s);
  if (parse_peek(s) == ']') { parse_advance(s); return term_new_ctr(NAM_NIL, 0, 0); }
  Term es[4096]; u32 n = 0;
  while (parse_peek(s) != ']') {
    es[n++] = parse_term(s, depth);
    parse_skip(s);
    parse_match(s, ",");  // optional comma
    parse_skip(s);
  }
  parse_consume(s, "]");
  Term t = term_new_ctr(NAM_NIL, 0, 0);
  for (int i = n - 1; i >= 0; i--) {
    Term a[2] = {es[i], t};
    t = term_new_ctr(NAM_CON, 2, a);
  }
  return t;
}
