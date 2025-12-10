fn Term parse_term_use(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "λ")) return 0;
  parse_skip(s);
  if (!parse_match(s, "{")) return 0;
  Term fun = parse_term(s, depth);
  parse_skip(s);
  if (!parse_match(s, "}")) return 0;
  return term_new_use(fun);
}
