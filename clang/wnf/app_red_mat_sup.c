// ((f ~> λ{#K:h; m}) &L{a,b})
// --------------------------- APP-RED-MAT-SUP
// ! F &L = f
// ! H &L = h
// ! M &L = m
// &L{((F₀ ~> λ{#K:H₀; M₀}) a)
//   ,((F₁ ~> λ{#K:H₁; M₁}) b)}
fn Term wnf_app_red_mat_sup(Term f, Term mat, Term sup) {
  ITRS_INC("APP-RED-MAT-SUP");
  u32  mat_loc = term_val(mat);
  u32  mat_nam = term_ext(mat);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term h       = heap_read(mat_loc + 0);
  Term m       = heap_read(mat_loc + 1);
  Term a       = heap_read(sup_loc + 0);
  Term b       = heap_read(sup_loc + 1);
  u64  base    = heap_alloc(17);
  u32  at      = (u32)base;
  heap_write(at + 0, f);
  heap_write(at + 1, h);
  heap_write(at + 2, m);
  Copy F       = term_clone_at(at + 0, lab);
  Copy H       = term_clone_at(at + 1, lab);
  Copy M       = term_clone_at(at + 2, lab);
  Term mat0    = term_new_mat_at(at + 3, mat_nam, H.k0, M.k0);
  Term mat1    = term_new_mat_at(at + 5, mat_nam, H.k1, M.k1);
  Term red0    = term_new_red_at(at + 7, F.k0, mat0);
  Term red1    = term_new_red_at(at + 9, F.k1, mat1);
  Term app0    = term_new_app_at(at + 11, red0, a);
  Term app1    = term_new_app_at(at + 13, red1, b);
  return term_new_sup_at(at + 15, lab, app0, app1);
}
