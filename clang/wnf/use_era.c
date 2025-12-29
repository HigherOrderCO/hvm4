// (λ{f} &{})
// ---------- USE-ERA
// &{}
fn Term wnf_use_era() {
  ITRS_INC("USE-ERA");
  return term_new_era();
}
