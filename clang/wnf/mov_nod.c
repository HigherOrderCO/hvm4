// % X = T{a,b,...}
// ----------------- MOV-NOD
// X ← T{a,b,...}
fn Term wnf_mov_nod(u32 loc, Term term) {
  ITRS++;
  u32 ari = term_arity(term);
  if (ari == 0) {
    // Safe to cache arity-0 values (immutable)
    heap_subst_var(loc, term);
    return term;
  }
  // Do not cache nodes with children
  return term;
}
