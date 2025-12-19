// (#a === #b)
// ------------ EQL-NUM
// #(a == b)
fn Term wnf_eql_num(Term a, Term b) {
  ITRS++;
  u32 av = term_val(a);
  u32 bv = term_val(b);
  return term_new_num(av == bv ? 1 : 0);
}
