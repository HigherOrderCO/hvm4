// @@mod(a, b)
// ----------- prim-mod
// a % b
fn Term prim_mod(Term a, Term b) {
  a = wnf(a);
  b = wnf(b);
  if (term_tag(a) != NUM || term_tag(b) != NUM) {
    fprintf(stderr, "@@mod: expected NUMs\n");
    exit(1);
  }
  if (term_val(b) == 0) {
    fprintf(stderr, "@@mod: division by zero\n");
    exit(1);
  }
  return term_new_num(term_val(a) % term_val(b));
}
