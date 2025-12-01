// @@eq(a, b)
// ---------- prim-eq
// a == b
fn Term prim_eq(Term a, Term b) {
  a = wnf(a);
  b = wnf(b);
  if (term_tag(a) != NUM || term_tag(b) != NUM) {
    fprintf(stderr, "@@eq: expected NUMs\n");
    exit(1);
  }
  return term_new_num(term_val(a) == term_val(b) ? 1 : 0);
}
