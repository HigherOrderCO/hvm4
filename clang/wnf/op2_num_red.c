// (x op (f ~> g))
// ---------------- op2-num-red
// (x op g)
//
// When OP2 with NUM on left receives RED on right, drop f and continue with g.
fn Term wnf_op2_num_red(Term red) {
  u32  red_loc = term_val(red);
  Term g       = HEAP[red_loc + 1];
  return g;
}
