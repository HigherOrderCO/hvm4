// (^n === ^n)  (same name)
// ------------------------ eql-nam
// #1
//
// (^n === ^m)  (different name)
// ----------------------------- eql-nam-miss
// #0
fn Term wnf_eql_nam(Term a, Term b) {
  ITRS++;
  u32 a_ext = term_ext(a);
  u32 b_ext = term_ext(b);
  return term_new_num(a_ext == b_ext ? 1 : 0);
}
