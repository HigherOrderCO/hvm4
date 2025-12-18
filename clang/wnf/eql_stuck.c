// (^n == _)  or  (_ == ^n)  or  ($x == _)  or  (_ == $x)
// ------------------------------------------------------- eql-stuck
// (^n == _)  or  (_ == ^n)  or  ($x == _)  or  (_ == $x)
//
// When NAM or VAR is compared with a non-matching type,
// equality cannot be determined, so the term stays stuck.
fn Term wnf_eql_stuck(u32 loc, Term a, Term b) {
  HEAP[loc + 0] = a;
  HEAP[loc + 1] = b;
  return term_new(0, EQL, 0, loc);
}
