// ((f ~> ^(g x)) a)
// ----------------- APP-RED-DRY
// ^((f ~> ^(g x)) a)
fn Term wnf_app_red_dry(Term f, Term dry, Term arg) {
  ITRS++;
  return term_new_dry(term_new_red(f, dry), arg);
}
