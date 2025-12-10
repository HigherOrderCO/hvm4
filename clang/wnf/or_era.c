// (&{} .|. b)
// ----------- or-era
// &{}
fn Term wnf_or_era(void) {
  ITRS++;
  return term_new_era();
}
