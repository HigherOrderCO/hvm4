// (^(f x) a)
// ----------- APP-DRY
// ^(^(f x) a)
fn Term wnf_app_dry(Term dry, Term arg) {
  return term_new_dry(dry, arg);
}
