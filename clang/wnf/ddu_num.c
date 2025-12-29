// ! X &(#n) = v; b
// ---------------- DDU-NUM
// ! X &n = v
// b
fn Term wnf_ddu_num(Term lab_num, Term val, Term bod) {
  ITRS_INC("DDU-NUM");
  u32 lab      = term_val(lab_num);
  u64 dup_loc  = heap_alloc(2);
  Term dp0     = term_new_dp0(lab, dup_loc);
  Term dp1     = term_new_dp1(lab, dup_loc);
  Term app0    = term_new_app(bod, dp0);
  Term app1    = term_new_app(app0, dp1);
  heap_set(dup_loc + 0, val);
  heap_set(dup_loc + 1, app1);
  return term_new(0, DUP, lab, dup_loc);
}
