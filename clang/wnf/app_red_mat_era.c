// ((f ~> λ{#K:h; m}) &{})
// ----------------------- APP-RED-MAT-ERA
// &{}
fn Term wnf_app_red_mat_era(void) {
  ITRS_INC("APP-RED-MAT-ERA");
  return term_new_era();
}
