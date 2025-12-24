// (λax.af === λbx.bf)
// ------------------- EQL-LAM
// X := fresh_nam()
// ax ← X
// bx ← X
// af === bf
fn Term wnf_eql_lam(Term a, Term b) {
  ITRS++;
  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);
  Term af    = heap_get(a_loc);
  Term bf    = heap_get(b_loc);
  // Generate fresh name for substitution
  u32 fresh = __atomic_fetch_add(&FRESH, 1, __ATOMIC_RELAXED);
  Term nam = term_new_nam(fresh);
  // Substitute both variable locations with the same name
  heap_subst_var(a_loc, nam);
  heap_subst_var(b_loc, nam);
  return term_new_eql(af, bf);
}
