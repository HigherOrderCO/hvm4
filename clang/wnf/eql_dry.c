// (^(af ax) === ^(bf bx))
// ----------------------- EQL-DRY
// (af === bf) & (ax === bx)
fn Term wnf_eql_dry(Term a, Term b) {
  ITRS++;
  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);
  Term af    = HEAP[a_loc + 0];
  Term ax    = HEAP[a_loc + 1];
  Term bf    = HEAP[b_loc + 0];
  Term bx    = HEAP[b_loc + 1];

  // (af === bf) .&. (ax === bx)
  Term eq_f = term_new_eql(af, bf);
  Term eq_x = term_new_eql(ax, bx);
  return term_new_and(eq_f, eq_x);
}
