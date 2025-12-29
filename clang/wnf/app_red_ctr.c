// ((f ~> #K{...}) a)
// ------------------ APP-RED-CTR
// ^((f ~> #K{...}) a)
fn Term wnf_app_red_ctr(Term f, Term ctr, Term arg) {
  ITRS_INC("APP-RED-CTR");
  return term_new_dry(term_new_red(f, ctr), arg);
}
