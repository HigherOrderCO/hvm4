// ((f ~> &L{x,y}) a)
// ------------------ app-red-sup
// ! F &L = f
// ! A &L = a
// &L{((F₀ ~> x) A₀)
//   ,((F₁ ~> y) A₁)}
fn Term wnf_app_red_sup(Term f, Term sup, Term arg) {
  ITRS++;
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_app(term_new_red(f, HEAP[sup_loc + 1]), arg);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_app(term_new_red(f, HEAP[sup_loc + 0]), arg);
  }
  Term x       = HEAP[sup_loc + 0];
  Term y       = HEAP[sup_loc + 1];
  Copy F       = term_clone(lab, f);
  Copy A       = term_clone(lab, arg);
  Term r0      = term_new_app(term_new_red(F.k0, x), A.k0);
  Term r1      = term_new_app(term_new_red(F.k1, y), A.k1);
  return term_new_sup(lab, r0, r1);
}
