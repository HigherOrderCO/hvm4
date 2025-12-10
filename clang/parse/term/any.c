fn Term parse_term_any(PState *s, u32 depth) {
  if (!parse_match(s, "*")) return 0;
  return term_new_any();
}
