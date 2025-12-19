// (name a)
// --------- APP-NAM
// ^(name a)
fn Term wnf_app_nam(Term nam, Term arg) {
  return term_new_dry(nam, arg);
}
