// ((f ~> name) a)
// ---------------- APP-RED-NAM
// ^((f ~> name) a)
fn Term wnf_app_red_nam(Term f, Term nam, Term arg) {
  ITRS_INC("APP-RED-NAM");
  return term_new_dry(term_new_red(f, nam), arg);
}
