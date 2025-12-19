// (&{} a)
// ------- APP-ERA
// &{}
fn Term wnf_app_era(void) {
  ITRS++;
  return term_new_era();
}
