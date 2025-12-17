fn Term snf(Term term, u32 depth, int quote) {
  term = wnf(term);

  u32 ari = term_arity(term);
  if (ari == 0) {
    return term;
  }
  u64 loc = term_val(term);
  if (term_tag(term) == LAM) {
    Term body = HEAP[loc];
    if (quote) {
      // Convert to quoted lambda: store name in ext field (ext > 0)
      u32 name = depth + 1;
      term = term_new(0, LAM, name, loc);  // ext = name (quoted)
      // Substitute bound var with NAM
      heap_subst_var(loc, term_new_nam(name));
    }
    // else: normal lambda (ext = 0), printer handles naming via body location
    HEAP[loc] = snf(body, depth + 1, quote);
  } else if (term_tag(term) == DRY) {
    HEAP[loc + 0] = snf(HEAP[loc + 0], depth, quote);
    HEAP[loc + 1] = snf(HEAP[loc + 1], depth, quote);
  } else {
    for (u32 i = 0; i < ari; i++) {
      HEAP[loc + i] = snf(HEAP[loc + i], depth, quote);
    }
  }
  return term;
}
