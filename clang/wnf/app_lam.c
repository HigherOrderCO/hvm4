// (λx.f a)
// -------- APP-LAM
// x ← a
// f
fn Term wnf_app_lam(Term lam, Term arg) {
  ITRS++;
  u32  loc  = term_val(lam);
  Term body = HEAP[loc];
  heap_subst_var(loc, arg);
  return body;
}
