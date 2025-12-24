// ((f ~> #K{...}) a)
// ------------------ APP-RED-CTR
// ^((f ~> #K{...}) a)
fn Term wnf_app_red_ctr(Term f, Term ctr, Term arg) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_RED_CTR);
  return term_new_dry(term_new_red(f, ctr), arg);
}
