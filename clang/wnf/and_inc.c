// (↑a & b)
// --------- AND-INC
// ↑(a & b)
fn Term wnf_and_inc(Term inc, Term b) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term a       = heap_read(inc_loc);
  Term and_tm  = term_new_and(a, b);
  heap_set(inc_loc, and_tm);
  return term_new(0, INC, 0, inc_loc);
}
