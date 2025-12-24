// ! X &(↑x) = v; b
// ---------------- DDU-INC
// ↑(! X &(x) = v; b)
fn Term wnf_ddu_inc(Term inc, Term val, Term bod) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term x       = heap_read(inc_loc);
  Term new_ddu = term_new_ddu(x, val, bod);
  return term_new_inc(new_ddu);
}
