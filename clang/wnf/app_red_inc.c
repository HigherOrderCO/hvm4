// ((f ~> ↑g) x)
// -------------- APP-RED-INC
// ↑((f ~> g) x)
fn Term wnf_app_red_inc(Term f, Term inc, Term arg) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_INC);
  u32  inc_loc = term_val(inc);
  Term g       = heap_read(inc_loc);
  Term new_app = term_new_app(term_new_red(f, g), arg);
  return term_new_inc(new_app);
}
