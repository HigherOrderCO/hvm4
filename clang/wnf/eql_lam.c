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
  Term af    = HEAP[a_loc];
  Term bf    = HEAP[b_loc];
  // Generate fresh name for substitution
  u32 fresh = ALLOC;  // use allocation counter as unique ID
  Term nam = term_new_nam(fresh);
  // Substitute both variable locations with the same name
  heap_subst_var(a_loc, nam);
  heap_subst_var(b_loc, nam);
  return term_new_eql(af, bf);
}
