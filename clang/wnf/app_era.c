// (&{} a)
// ------- APP-ERA
// &{}
fn Term wnf_app_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_ERA);
  return term_new_era();
}
