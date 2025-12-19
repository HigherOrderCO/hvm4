// ((f ~> λ{#K:h; m}) &{})
// ----------------------- APP-RED-MAT-ERA
// &{}
fn Term wnf_app_red_mat_era(void) {
  ITRS++;
  return term_new_era();
}
