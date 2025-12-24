// ((f ~> λ{g}) &L{a,b})
// --------------------- APP-RED-USE-SUP
// ! F &L = f
// ! G &L = g
// &L{((F₀ ~> λ{G₀}) a)
//   ,((F₁ ~> λ{G₁}) b)}
fn Term wnf_app_red_use_sup(Term f, Term use, Term sup) {
  ITRS++;
  u32  use_loc = term_val(use);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term g       = heap_read(use_loc);
  Term a       = heap_read(sup_loc + 0);
  Term b       = heap_read(sup_loc + 1);
  Copy F       = term_clone(lab, f);
  Copy G       = term_clone(lab, g);
  Term use0    = term_new_use(G.k0);
  Term use1    = term_new_use(G.k1);
  Term r0      = term_new_app(term_new_red(F.k0, use0), a);
  Term r1      = term_new_app(term_new_red(F.k1, use1), b);
  return term_new_sup(lab, r0, r1);
}
