// (* === b)
// ----------- EQL-ANY-L
// 1
fn Term wnf_eql_any_l(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_EQL_ANY);
  return term_new_num(1);
}

// (a === *)
// ----------- EQL-ANY-R
// 1
fn Term wnf_eql_any_r(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_EQL_ANY);
  return term_new_num(1);
}
