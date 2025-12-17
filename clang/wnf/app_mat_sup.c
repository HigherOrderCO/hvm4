// (λ{#K:h; m} &L{a,b})
// -------------------- app-mat-sup
// ! H &L = h
// ! M &L = m
// &L{(λ{#K:H₀; M₀} a)
//   ,(λ{#K:H₁; M₁} b)}
fn Term wnf_app_mat_sup(Term mat, Term sup) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_app(mat, HEAP[loc + 1]);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_app(mat, HEAP[loc + 0]);
  }
  Copy M   = term_clone(lab, mat);
  Term a   = HEAP[loc + 0];
  Term b   = HEAP[loc + 1];
  return term_new_sup(lab, term_new_app(M.k0, a), term_new_app(M.k1, b));
}
