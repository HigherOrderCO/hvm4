// (λ{#K:h; m} #K{a,b})
// -------------------- APP-MAT-CTR-MAT
// (h a b)
//
// (λ{#K:h; m} #L{a,b})
// -------------------- APP-MAT-CTR-MIS
// (m #L{a,b})
fn Term wnf_app_mat_ctr(Term mat, Term ctr) {
  ITRS++;
  u32 ari = term_tag(ctr) - C00;
  if (term_ext(mat) == term_ext(ctr)) {
    Term res = heap_read(term_val(mat));
    for (u32 i = 0; i < ari; i++) {
      res = term_new_app(res, heap_read(term_val(ctr) + i));
    }
    return res;
  } else {
    return term_new_app(heap_read(term_val(mat) + 1), ctr);
  }
}
