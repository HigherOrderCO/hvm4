// (&{} === b)
// ----------- EQL-ERA-L
// &{}
fn Term wnf_eql_era_l(void) {
  ITRS_INC("EQL-ERA-L");
  return term_new_era();
}

// (a === &{})
// ----------- EQL-ERA-R
// &{}
fn Term wnf_eql_era_r(void) {
  ITRS_INC("EQL-ERA-R");
  return term_new_era();
}
