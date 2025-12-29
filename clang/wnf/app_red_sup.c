// ((f ~> &L{x,y}) a)
// ------------------ APP-RED-SUP
// ! F &L = f
// ! A &L = a
// &L{((F₀ ~> x) A₀)
//   ,((F₁ ~> y) A₁)}
fn Term wnf_app_red_sup(Term f, Term sup, Term arg) {
  ITRS_INC("APP-RED-SUP");
  u32  sup_loc = term_val(sup);
  u32  lab     = term_ext(sup);
  Term x       = heap_read(sup_loc + 0);
  Term y       = heap_read(sup_loc + 1);
  u64  base    = heap_alloc(12);
  u32  at      = (u32)base;
  heap_write(at + 0, f);
  heap_write(at + 1, arg);
  Copy F       = term_clone_at(at + 0, lab);
  Copy A       = term_clone_at(at + 1, lab);
  Term red0    = term_new_red_at(at + 2, F.k0, x);
  Term red1    = term_new_red_at(at + 4, F.k1, y);
  Term app0    = term_new_app_at(at + 6, red0, A.k0);
  Term app1    = term_new_app_at(at + 8, red1, A.k1);
  return term_new_sup_at(at + 10, lab, app0, app1);
}
