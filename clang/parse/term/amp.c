fn Term parse_term(PState *s, u32 depth);
fn Term parse_term_era_amp(PState *s, u32 depth);
fn Term parse_term_fork_body(PState *s, u32 depth);
fn Term parse_term_sup_body(PState *s, u32 depth);

// Dispatcher for &-prefixed terms: &{}, &Lλx{...}, &L{A,B}, &(L){A,B}
fn Term parse_term_amp(PState *s, u32 depth) {
  if (!parse_match(s, "&")) return 0;
  TermParser alts[] = {
    parse_term_era_amp,   // &{}
    parse_term_fork_body, // &Lλx{A;B} or &(L)λx{A;B}
    parse_term_sup_body,  // &L{A,B} or &(L){A,B}
    NULL
  };
  return parse_choice(s, depth, alts);
}
