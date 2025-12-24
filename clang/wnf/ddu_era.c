// ! X &(&{}) = v; b
// ----------------- DDU-ERA
// &{}
fn Term wnf_ddu_era() {
  ITRS++;
  ITRS_KIND(WNF_ITRS_DDU_ERA);
  return term_new_era();
}
