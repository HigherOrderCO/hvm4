// ((f ~> λ{#K:h; m}) #K{a,b})
// --------------------------- APP-RED-MAT-CTR-MAT
// ((λa.λb.(f #K{a,b}) ~> h) a b)
fn Term wnf_app_red_mat_ctr_match(Term f, Term mat, Term ctr) {
  ITRS++;
  u32  mat_loc = term_val(mat);
  u32  ctr_loc = term_val(ctr);
  u32  ctr_nam = term_ext(ctr);
  u32  ctr_ari = term_tag(ctr) - C00;
  Term h       = heap_get(mat_loc + 0);

  // Build: (λa.λb.(f #K{a,b}) ~> h) applied to ctr args
  u64 lam_locs[16];
  Term vars[16];
  for (u32 i = 0; i < ctr_ari; i++) {
    lam_locs[i] = heap_alloc(1);
    vars[i] = term_new(0, VAR, 0, lam_locs[i]);
  }
  Term inner = term_new_app(f, term_new_ctr(ctr_nam, ctr_ari, vars));

  // Wrap in lambdas from inside out
  Term body = inner;
  for (int32_t i = ctr_ari - 1; i >= 0; i--) {
    heap_set(lam_locs[i], body);
    body = term_new(0, LAM, 0, lam_locs[i]);
  }

  // Create red: body ~> h
  Term red_result = term_new_red(body, h);

  // Apply to original ctr args
  for (u32 i = 0; i < ctr_ari; i++) {
    red_result = term_new_app(red_result, heap_get(ctr_loc + i));
  }

  return red_result;
}

// ((f ~> λ{#K:h; m}) #L{a,b})
// --------------------------- APP-RED-MAT-CTR-MIS
// ((f ~> m) #L{a,b})
fn Term wnf_app_red_mat_ctr_miss(Term f, Term mat, Term ctr) {
  ITRS++;
  u32  mat_loc = term_val(mat);
  Term m       = heap_get(mat_loc + 1);
  return term_new_app(term_new_red(f, m), ctr);
}
