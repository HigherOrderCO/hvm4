// (&{} === b)
// ----------- EQL-ERA-L
// &{}
fn Term wnf_eql_era_l(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_EQL_ERA);
  return term_new_era();
}

// (a === &{})
// ----------- EQL-ERA-R
// &{}
fn Term wnf_eql_era_r(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_EQL_ERA);
  return term_new_era();
}
