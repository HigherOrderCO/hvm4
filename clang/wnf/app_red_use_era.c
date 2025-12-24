// ((f ~> λ{g}) &{})
// ----------------- APP-RED-USE-ERA
// &{}
fn Term wnf_app_red_use_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_USE_ERA);
  return term_new_era();
}
