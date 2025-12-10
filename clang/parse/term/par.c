fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_par(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "(")) return 0;
  Term term = parse_term(s, depth);
  parse_consume(s, ")");
  return term;
}
