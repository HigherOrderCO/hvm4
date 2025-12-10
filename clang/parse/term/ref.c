fn Term parse_term_ref(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "@")) return 0;
  return term_new_ref(parse_name_ref(s));
}
