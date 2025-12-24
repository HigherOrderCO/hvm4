// (λ{af} === λ{bf})
// ----------------- EQL-USE
// af === bf
fn Term wnf_eql_use(Term a, Term b) {
  ITRS++;
  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);
  Term af    = heap_get(a_loc);
  Term bf    = heap_get(b_loc);
  return term_new_eql(af, bf);
}
