// (ctr a)
// ----------- app-ctr (stuck)
// ^(ctr a)
fn Term wnf_app_ctr(Term ctr, Term arg) {
  return term_new_dry(ctr, arg);
}
