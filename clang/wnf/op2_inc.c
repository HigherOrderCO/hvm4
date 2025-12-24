// (↑x op y)
// ---------- OP2-INC-X
// ↑(x op y)
fn Term wnf_op2_inc_x(u32 opr, Term inc, Term y) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term x       = heap_read(inc_loc);
  Term op      = term_new_op2(opr, x, y);
  heap_set(inc_loc, op);
  return term_new(0, INC, 0, inc_loc);
}

// (#n op ↑y)
// ---------- OP2-INC-Y
// ↑(#n op y)
fn Term wnf_op2_inc_y(u32 opr, Term x, Term inc) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term y       = heap_read(inc_loc);
  Term op      = term_new_op2(opr, x, y);
  heap_set(inc_loc, op);
  return term_new(0, INC, 0, inc_loc);
}
