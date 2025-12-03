// (&{} === b)
// ----------- eql-era-l
// &{}
fn Term wnf_eql_era_l(void) {
  ITRS++;
  return term_new_era();
}

// (a === &{})
// ----------- eql-era-r
// &{}
fn Term wnf_eql_era_r(void) {
  ITRS++;
  return term_new_era();
}
