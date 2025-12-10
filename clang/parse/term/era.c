fn Term parse_term_era(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  parse_skip(s);
  if (parse_match(s, "λ") || parse_match(s, "&")) {
    parse_skip(s);
    if (!parse_match(s, "{")) return 0;
    parse_skip(s);
    if (!parse_match(s, "}")) return 0;

    return term_new_era();
  }
  return 0;
}
