// (λ{f} &{})
// ---------- USE-ERA
// &{}
fn Term wnf_use_era() {
  ITRS++;
  ITRS_KIND(WNF_ITRS_USE_ERA);
  return term_new_era();
}
