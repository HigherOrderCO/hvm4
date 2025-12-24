// (use ↑x)
// --------- USE-INC
// ↑(use x)
fn Term wnf_use_inc(Term use, Term inc) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term x       = heap_get(inc_loc);
  Term app     = term_new_app(use, x);
  heap_set(inc_loc, app);
  return term_new(0, INC, 0, inc_loc);
}
