// (λ{...} ↑x)
// ------------ MAT-INC
// ↑(λ{...} x)
fn Term wnf_mat_inc(Term mat, Term inc) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term x       = HEAP[inc_loc];
  Term app     = term_new_app(mat, x);
  HEAP[inc_loc] = app;
  return term_new(0, INC, 0, inc_loc);
}
