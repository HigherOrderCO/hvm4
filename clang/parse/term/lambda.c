fn Term parse_term(PState *s, u32 depth);
fn Term parse_term_era_lam(PState *s, u32 depth);
fn Term parse_term_mat_body(PState *s, u32 depth);
fn Term parse_term_lam_body(PState *s, u32 depth);

// Dispatcher for λ-prefixed terms: λ{}, λ{...patterns...}, λx.body
fn Term parse_term_lambda(PState *s, u32 depth) {
  if (!parse_match(s, "λ")) return 0;
  TermParser alts[] = {
    parse_term_era_lam,  // λ{}
    parse_term_mat_body, // λ{#K: ...; ...} or λ{0: ...; ...}
    parse_term_lam_body, // λx.f, λ&x.f, etc.
    NULL
  };
  return parse_choice(s, depth, alts);
}
