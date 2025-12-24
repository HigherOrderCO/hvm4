// (x op &{}) where x is NUM
// -------------- OP2-NUM-ERA
// &{}
fn Term wnf_op2_num_era() {
  ITRS++;
  ITRS_KIND(WNF_ITRS_OP2_NUM_ERA);
  return term_new_era();
}
