// ((f ~> &L{x,y}) a)
// ------------------ APP-RED-SUP
// ! F &L = f
// ! A &L = a
// &L{((F₀ ~> x) A₀)
//   ,((F₁ ~> y) A₁)}
fn Term wnf_app_red_sup(Term f, Term sup, Term arg) {
  ITRS++;
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term x       = heap_read(sup_loc + 0);
  Term y       = heap_read(sup_loc + 1);
  Copy F       = term_clone(lab, f);
  Copy A       = term_clone(lab, arg);
  Term r0      = term_new_app(term_new_red(F.k0, x), A.k0);
  Term r1      = term_new_app(term_new_red(F.k1, y), A.k1);
  return term_new_sup(lab, r0, r1);
}
