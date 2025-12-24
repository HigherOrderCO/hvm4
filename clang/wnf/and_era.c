// (&{} .&. b)
// ----------- AND-ERA
// &{}
fn Term wnf_and_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_AND_ERA);
  return term_new_era();
}
