// ((f ~> λ{g}) x)
// --------------- APP-RED-USE-VAL
// (f x) ~> (g x)
fn Term wnf_app_red_use_val(Term f, Term use, Term val) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_USE_VAL);
  u32  use_loc = term_val(use);
  Term g       = heap_read(use_loc);
  return term_new_red(term_new_app(f, val), term_new_app(g, val));
}
