// ((f ~> (g ~> h)) x)
// ------------------- APP-RED-RED
// ((f x) ~> ((g ~> h) x))
fn Term wnf_app_red_red(Term f, Term red_inner, Term arg) {
  ITRS++;
  return term_new_red(term_new_app(f, arg), term_new_app(red_inner, arg));
}
