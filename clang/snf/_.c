fn Term snf(Term term, u32 depth, int quote) {
  // Check interaction limit before starting
  if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;

  term = wnf(term);

  // Check again after wnf (an interaction may have occurred)
  if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;

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
    if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;
    HEAP[loc + 1] = snf(HEAP[loc + 1], depth, quote);
  } else {
    for (u32 i = 0; i < ari; i++) {
      if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) break;
      HEAP[loc + i] = snf(HEAP[loc + i], depth, quote);
    }
  }
  return term;
}
