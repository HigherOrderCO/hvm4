// (x op &{}) where x is NUM
// -------------- OP2-NUM-ERA
// &{}
fn Term wnf_op2_num_era() {
  ITRS_INC("OP2-NUM-ERA");
  return term_new_era();
}
