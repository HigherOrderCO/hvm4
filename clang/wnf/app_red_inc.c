// ((f ~> ↑g) x)
// -------------- APP-RED-INC
// ↑((f ~> g) x)
fn Term wnf_app_red_inc(Term f, Term inc, Term arg) {
  ITRS++;
  u32  inc_loc = term_val(inc);
  Term g       = heap_get(inc_loc);
  Term new_app = term_new_app(term_new_red(f, g), arg);
  return term_new_inc(new_app);
}
