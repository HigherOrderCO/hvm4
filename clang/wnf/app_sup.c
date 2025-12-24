// (&L{f,g} a)
// ----------------- APP-SUP
// ! A &L = a
// &L{(f A₀),(g A₁)}
fn Term wnf_app_sup(Term app, Term sup) {
  ITRS++;
  u32  app_loc = term_val(app);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term arg     = heap_read(app_loc + 1);
  Term tm1     = heap_read(sup_loc + 1);
  u64  loc     = heap_alloc(3);
  heap_set(loc + 2, arg);
  Copy D = term_clone_at(loc + 2, lab);
  heap_set(sup_loc + 1, D.k0);
  Term ap0 = term_new(0, APP, 0, sup_loc);
  Term ap1 = term_new_app_at(loc, tm1, D.k1);
  return term_new_sup_at(app_loc, lab, ap0, ap1);
}
