// @@opr(&{}, y)
// ------------- OP2-ERA
// &{}
fn Term wnf_op2_era() {
  ITRS++;
  ITRS_KIND(WNF_ITRS_OP2_ERA);
  return term_new_era();
}
