// (#K{a0,a1...} === #K{b0,b1...})  (same tag)
// --------------------------------------- eql-ctr-match
// (a0 === b0) & (a1 === b1) & ...
//
// (#K{...} === #L{...})  (different tag)
// ------------------------------------- eql-ctr-miss
// #0
fn Term wnf_eql_ctr(Term a, Term b) {
  ITRS++;
  u32 a_tag = term_tag(a);
  u32 b_tag = term_tag(b);
  u32 a_ext = term_ext(a);
  u32 b_ext = term_ext(b);

  // Different constructor tags or names -> #0
  if (a_tag != b_tag || a_ext != b_ext) {
    return term_new_num(0);
  }

  u32 arity = a_tag - C00;

  // Arity 0: equal
  if (arity == 0) {
    return term_new_num(1);
  }

  u32  a_loc = term_val(a);
  u32  b_loc = term_val(b);

  // Build AND chain: (a0 === b0) .&. (a1 === b1) .&. ...
  // Use short-circuit AND for lazy evaluation
  Term result = term_new_eql(HEAP[a_loc], HEAP[b_loc]);
  for (u32 i = 1; i < arity; i++) {
    Term eq_i = term_new_eql(HEAP[a_loc + i], HEAP[b_loc + i]);
    result = term_new_and(result, eq_i);
  }
  return result;
}
