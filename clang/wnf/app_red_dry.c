// ((f ~> ^(g x)) a)
// ----------------- APP-RED-DRY
// ^((f ~> ^(g x)) a)
fn Term wnf_app_red_dry(Term f, Term dry, Term arg) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_DRY);
  return term_new_dry(term_new_red(f, dry), arg);
}
