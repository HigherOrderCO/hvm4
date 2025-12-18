fn Term snf(Term term, u32 depth) {
  term = wnf(term);
  u32 ari = term_arity(term);
  if (ari == 0) {
    return term;
  }
  u64 loc = term_val(term);
  if (term_tag(term) == LAM) {
    // Do NOT substitute VAR with NAM - the printer handles naming globally
    Term body = HEAP[loc];
    HEAP[loc] = snf(body, depth + 1);
  } else if (term_tag(term) == DRY) {
    HEAP[loc + 0] = snf(HEAP[loc + 0], depth);
    HEAP[loc + 1] = snf(HEAP[loc + 1], depth);
  } else {
    for (u32 i = 0; i < ari; i++) {
      HEAP[loc + i] = snf(HEAP[loc + i], depth);
    }
  }
  return term;
}
