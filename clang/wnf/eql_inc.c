// (↑a === b)
// ----------- EQL-INC-L
// ↑(a === b)
fn Term wnf_eql_inc_l(Term inc, Term b) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term a       = heap_read(inc_loc);
  Term eql     = term_new_eql(a, b);
  heap_set(inc_loc, eql);
  return term_new(0, INC, 0, inc_loc);
}

// (a === ↑b)
// ----------- EQL-INC-R
// ↑(a === b)
fn Term wnf_eql_inc_r(Term a, Term inc) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term b       = heap_read(inc_loc);
  Term eql     = term_new_eql(a, b);
  heap_set(inc_loc, eql);
  return term_new(0, INC, 0, inc_loc);
}
