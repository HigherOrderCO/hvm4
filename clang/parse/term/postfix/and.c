fn Term parse_term_atom(PState *s, u32 depth);
fn Term parse_term_app_prec(Term f, PState *s, u32 depth, int min_prec);

fn Term parse_postfix_and(Term f, PState *s, u32 depth, int min_prec) {
  (void)min_prec;
  if (!parse_match(s, ".&.")) return 0;
  Term rhs = parse_term_atom(s, depth);
  rhs = parse_term_app_prec(rhs, s, depth, 2);  // same precedence as &&
  return term_new_and(f, rhs);
}
