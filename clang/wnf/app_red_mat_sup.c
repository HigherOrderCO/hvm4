// ((f ~> λ{#K:h; m}) &L{a,b})
// --------------------------- APP-RED-MAT-SUP
// ! F &L = f
// ! H &L = h
// ! M &L = m
// &L{((F₀ ~> λ{#K:H₀; M₀}) a)
//   ,((F₁ ~> λ{#K:H₁; M₁}) b)}
fn Term wnf_app_red_mat_sup(Term f, Term mat, Term sup) {
  ITRS++;
  u32  mat_loc = term_val(mat);
  u32  mat_nam = term_ext(mat);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term h       = heap_get(mat_loc + 0);
  Term m       = heap_get(mat_loc + 1);
  Term a       = heap_get(sup_loc + 0);
  Term b       = heap_get(sup_loc + 1);
  Copy F       = term_clone(lab, f);
  Copy H       = term_clone(lab, h);
  Copy M       = term_clone(lab, m);
  Term mat0    = term_new_mat(mat_nam, H.k0, M.k0);
  Term mat1    = term_new_mat(mat_nam, H.k1, M.k1);
  Term r0      = term_new_app(term_new_red(F.k0, mat0), a);
  Term r1      = term_new_app(term_new_red(F.k1, mat1), b);
  return term_new_sup(lab, r0, r1);
}
