// (&L{f,g} a)
// ----------------- app-sup
// ! A &L = a
// &L{(f A₀),(g A₁)}
fn Term wnf_app_sup(Term app, Term sup) {
  ITRS++;
  u32  app_loc = term_val(app);
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term arg     = HEAP[app_loc + 1];
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_app(HEAP[sup_loc + 1], arg);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_app(HEAP[sup_loc + 0], arg);
  }
  Term tm1     = HEAP[sup_loc + 1];
  u64  loc     = heap_alloc(3);
  HEAP[loc + 2] = arg;
  Copy D = term_clone_at(loc + 2, lab);
  HEAP[sup_loc + 1] = D.k0;
  Term ap0 = term_new(0, APP, 0, sup_loc);
  Term ap1 = term_new_app_at(loc, tm1, D.k1);
  return term_new_sup_at(app_loc, lab, ap0, ap1);
}
