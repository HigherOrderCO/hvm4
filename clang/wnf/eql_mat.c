// (λ{#K:ah;am} === λ{#K:bh;bm})  (same tag)
// ----------------------------------------- EQL-MAT-MAT
// (ah === bh) & (am === bm)
//
// (λ{#K:...} === λ{#L:...})  (different tag)
// ----------------------------------------- EQL-MAT-MIS
// #0
fn Term wnf_eql_mat(Term a, Term b) {
  ITRS++;
  u32 a_ext = term_ext(a);
  u32 b_ext = term_ext(b);

  // Different match tags -> #0
  if (a_ext != b_ext) {
    return term_new_num(0);
  }

  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);
  Term ah    = heap_get(a_loc + 0);
  Term am    = heap_get(a_loc + 1);
  Term bh    = heap_get(b_loc + 0);
  Term bm    = heap_get(b_loc + 1);

  // (ah === bh) .&. (am === bm)
  Term eq_h = term_new_eql(ah, bh);
  Term eq_m = term_new_eql(am, bm);
  return term_new_and(eq_h, eq_m);
}
