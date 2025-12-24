// (λ{f} &L{a,b})
// ----------------- USE-SUP
// ! F &L = f
// &L{(λ{F₀} a), (λ{F₁} b)}
fn Term wnf_use_sup(Term use, Term sup) {
  ITRS++;
  u32  use_loc = term_val(use);
  Term f       = heap_get(use_loc);
  u32  lab     = term_ext(sup);
  u32  sup_loc = term_val(sup);
  Copy F       = term_clone(lab, f);
  Term use0    = term_new_use(F.k0);
  Term use1    = term_new_use(F.k1);
  Term app0    = term_new_app(use0, heap_get(sup_loc + 0));
  Term app1    = term_new_app(use1, heap_get(sup_loc + 1));
  return term_new_sup(lab, app0, app1);
}
