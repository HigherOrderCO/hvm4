// (&{} a)
// ------- APP-ERA
// &{}
fn Term wnf_app_era(void) {
  ITRS_INC("APP-ERA");
  return term_new_era();
}
