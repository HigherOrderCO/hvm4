// ((f ~> use) ↑x)
// --------------- APP-RED-USE-INC
// ↑((f ~> use) x)
fn Term wnf_app_red_use_inc(Term f, Term use, Term inc) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_USE_INC);
  u32  inc_loc = term_val(inc);
  Term x       = heap_read(inc_loc);
  Term new_app = term_new_app(term_new_red(f, use), x);
  return term_new_inc(new_app);
}
