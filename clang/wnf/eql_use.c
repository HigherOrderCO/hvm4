// (λ{af} === λ{bf})
// ----------------- EQL-USE
// af === bf
fn Term wnf_eql_use(Term a, Term b) {
  ITRS++;
  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);
  Term af    = heap_read(a_loc);
  Term bf    = heap_read(b_loc);
  return term_new_eql(af, bf);
}
