// (λ{#K:h; m} #K{a,b})
// -------------------- APP-MAT-CTR-MAT
// (h a b)
//
// (λ{#K:h; m} #L{a,b})
// -------------------- APP-MAT-CTR-MIS
// (m #L{a,b})
fn Term wnf_app_mat_ctr(Term mat, Term ctr) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_MAT_CTR);
  u32 mat_ext = term_ext(mat);
  u32 ctr_ext = term_ext(ctr);
  if (mat_ext != ctr_ext) {
    return term_new_app(heap_read(term_val(mat) + 1), ctr);
  }
  u32 ari = term_tag(ctr) - C00;
  u32 mat_loc = term_val(mat);
  u32 ctr_loc = term_val(ctr);
  Term res = heap_read(mat_loc);
  if (ari == 0) {
    return res;
  }
  u64 apps = heap_alloc(2 * (u64)ari);
  for (u32 i = 0; i < ari; i++) {
    res = term_new_app_at((u32)(apps + 2 * (u64)i), res, heap_read(ctr_loc + i));
  }
  return res;
}
