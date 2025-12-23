fn Copy term_clone_at(u32 loc, u32 lab) {
  return (Copy){ term_new_dp0(lab, loc), term_new_dp1(lab, loc) };
}

fn Copy term_clone(u32 lab, Term val) {
  u64 loc   = heap_alloc(1);
  HEAP[loc] = val;
  return term_clone_at(loc, lab);
}

fn void term_clone_many(u32 lab, Term *src, u32 n, Term *dst0, Term *dst1) {
  for (u32 i = 0; i < n; i++) {
    Copy c  = term_clone(lab, src[i]);
    dst0[i] = c.k0;
    dst1[i] = c.k1;
  }
}
