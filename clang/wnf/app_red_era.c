// ((f ~> &{}) a)
// -------------- APP-RED-ERA
// &{}
fn Term wnf_app_red_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_ERA);
  return term_new_era();
}
