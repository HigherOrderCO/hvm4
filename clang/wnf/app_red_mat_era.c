// ((f ~> λ{#K:h; m}) &{})
// ----------------------- APP-RED-MAT-ERA
// &{}
fn Term wnf_app_red_mat_era(void) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_MAT_ERA);
  return term_new_era();
}
