// (λx.f a)
// -------- APP-LAM
// x ← a
// f
fn Term wnf_app_lam(Term lam, Term arg) {
  ITRS++;
  u32  loc     = term_val(lam);
  u32  lam_ext = term_ext(lam);
  Term body    = heap_get(loc);
  if (lam_ext & LAM_ERA_MASK) {
    return body;
  }
  heap_subst_var(loc, arg);
  return body;
}
