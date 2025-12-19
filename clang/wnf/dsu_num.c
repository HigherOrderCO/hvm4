// &(#n){a, b}
// ----------- DSU-NUM
// &n{a, b}
fn Term wnf_dsu_num(Term lab_num, Term a, Term b) {
  ITRS++;
  u32 lab = term_val(lab_num);
  return term_new_sup(lab, a, b);
}
