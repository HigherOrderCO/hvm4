// Body after & is consumed: expects {}
fn Term parse_term_era_amp(PState *s, u32 depth) {
  parse_skip(s);
  if (!parse_match(s, "{")) return 0;
  parse_skip(s);
  if (!parse_match(s, "}")) return 0;
  return term_new_era();
}

// Body after λ is consumed: expects {}
fn Term parse_term_era_lam(PState *s, u32 depth) {
  parse_skip(s);
  if (!parse_match(s, "{")) return 0;
  parse_skip(s);
  if (!parse_match(s, "}")) return 0;
  return term_new_era();
}
