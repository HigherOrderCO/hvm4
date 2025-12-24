// &(↑x){a, b}
// ------------ DSU-INC
// ↑(&(x){a, b})
fn Term wnf_dsu_inc(Term inc, Term a, Term b) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_DSU_INC);
  u32  inc_loc = term_val(inc);
  Term x       = heap_read(inc_loc);
  Term new_dsu = term_new_dsu(x, a, b);
  return term_new_inc(new_dsu);
}
