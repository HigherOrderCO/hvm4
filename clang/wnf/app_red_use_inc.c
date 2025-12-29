// ((f ~> use) ↑x)
// --------------- APP-RED-USE-INC
// ↑((f ~> use) x)
fn Term wnf_app_red_use_inc(Term f, Term use, Term inc) {
  ITRS_INC("APP-RED-USE-INC");
  u32  inc_loc = term_val(inc);
  Term x       = heap_read(inc_loc);
  Term new_app = term_new_app(term_new_red(f, use), x);
  return term_new_inc(new_app);
}
