// ((f ~> mat) ↑x)
// --------------- APP-RED-MAT-INC
// ↑((f ~> mat) x)
fn Term wnf_app_red_mat_inc(Term f, Term mat, Term inc) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term x       = heap_get(inc_loc);
  Term new_app = term_new_app(term_new_red(f, mat), x);
  return term_new_inc(new_app);
}
