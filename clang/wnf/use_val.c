// (λ{f} x)
// --------- USE-VAL
// (f x)
fn Term wnf_use_val(Term use, Term val) {
  ITRS++;
  u32  loc = term_val(use);
  Term f   = heap_read(loc);
  return term_new_app(f, val);
}
