// ((f ~> λx.g) a)
// --------------- APP-RED-LAM
// x ← a
// (f x) ~> g
// Note: we substitute x with a, then return (f (Var x)) ~> g
// which effectively becomes (f a) ~> g[x:=a]
fn Term wnf_app_red_lam(Term f, Term lam, Term arg) {
  ITRS++;
  u32  lam_loc = term_val(lam);
  Term g       = heap_get(lam_loc);
  Term var_x   = term_new(0, VAR, 0, lam_loc);
  heap_subst_var(lam_loc, arg);
  return term_new_red(term_new_app(f, var_x), g);
}
