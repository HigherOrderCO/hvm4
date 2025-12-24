// (λx.f a)
// -------- APP-LAM
// x ← a
// f
fn Term wnf_app_lam(Term lam, Term arg) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_APP_LAM);
  u32  loc     = term_val(lam);
  u32  lam_ext = term_ext(lam);
  Term body    = heap_read(loc);
  if (__builtin_expect(lam_ext & LAM_ERA_MASK, 0)) {
    return body;
  }
  heap_subst_var(loc, arg);
  return body;
}
