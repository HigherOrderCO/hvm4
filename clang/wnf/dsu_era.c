// &(&{}){a, b}
// ------------ DSU-ERA
// &{}
fn Term wnf_dsu_era() {
  ITRS++;
  ITRS_KIND(WNF_ITRS_DSU_ERA);
  return term_new_era();
}
