// @@mul(a, b)
// ----------- prim-mul
// a * b
fn Term prim_mul(Term a, Term b) {
  a = wnf(a);
  b = wnf(b);
  if (term_tag(a) != NUM || term_tag(b) != NUM) {
    fprintf(stderr, "@@mul: expected NUMs\n");
    exit(1);
  }
  return term_new_num(term_val(a) * term_val(b));
}
