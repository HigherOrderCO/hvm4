fn Term parse_term(PState *s, u32 depth);

fn Term parse_postfix_red(Term f, PState *s, u32 depth, int min_prec) {
  (void)min_prec;
  if (!parse_match(s, "~>")) return 0;
  Term g = parse_term(s, depth);
  return term_new_red(f, g);
}
