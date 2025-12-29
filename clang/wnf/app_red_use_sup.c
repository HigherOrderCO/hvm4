// ((f ~> λ{g}) &L{a,b})
// --------------------- APP-RED-USE-SUP
// ! F &L = f
// ! G &L = g
// &L{((F₀ ~> λ{G₀}) a)
//   ,((F₁ ~> λ{G₁}) b)}
fn Term wnf_app_red_use_sup(Term f, Term use, Term sup) {
  ITRS_INC("APP-RED-USE-SUP");
  u32  use_loc = term_val(use);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term g       = heap_read(use_loc);
  Term a       = heap_read(sup_loc + 0);
  Term b       = heap_read(sup_loc + 1);
  u64  base    = heap_alloc(14);
  u32  at      = (u32)base;
  heap_write(at + 0, f);
  heap_write(at + 1, g);
  Copy F       = term_clone_at(at + 0, lab);
  Copy G       = term_clone_at(at + 1, lab);
  Term use0    = term_new_use_at(at + 2, G.k0);
  Term use1    = term_new_use_at(at + 3, G.k1);
  Term red0    = term_new_red_at(at + 4, F.k0, use0);
  Term red1    = term_new_red_at(at + 6, F.k1, use1);
  Term app0    = term_new_app_at(at + 8, red0, a);
  Term app1    = term_new_app_at(at + 10, red1, b);
  return term_new_sup_at(at + 12, lab, app0, app1);
}
