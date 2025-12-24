// (&{} .|. b)
// ----------- OR-ERA
// &{}
fn Term wnf_or_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_OR_ERA);
  return term_new_era();
}
