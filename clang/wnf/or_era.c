// (&{} .|. b)
// ----------- OR-ERA
// &{}
fn Term wnf_or_era(void) {
  ITRS_INC("OR-ERA");
  return term_new_era();
}
