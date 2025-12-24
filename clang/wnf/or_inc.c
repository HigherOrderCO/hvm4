// (↑a | b)
// --------- OR-INC
// ↑(a | b)
fn Term wnf_or_inc(Term inc, Term b) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term a       = heap_get(inc_loc);
  Term or_tm   = term_new_or(a, b);
  heap_set(inc_loc, or_tm);
  return term_new(0, INC, 0, inc_loc);
}
