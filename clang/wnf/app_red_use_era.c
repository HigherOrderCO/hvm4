// ((f ~> λ{g}) &{})
// ----------------- APP-RED-USE-ERA
// &{}
fn Term wnf_app_red_use_era(void) {
  ITRS++;
  return term_new_era();
}
