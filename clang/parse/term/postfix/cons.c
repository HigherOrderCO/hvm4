fn Term parse_term(PState *s, u32 depth);

fn Term parse_postfix_cons(Term f, PState *s, u32 depth, int min_prec) {
  (void)min_prec;
  if (!parse_match(s, "<>")) return 0;
  Term t = parse_term(s, depth);
  Term a[2] = {f, t};
  return term_new_ctr(NAM_CON, 2, a);
}
