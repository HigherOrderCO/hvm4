// @@or(a, b)
// ---------- prim-or
// a | b
fn Term prim_or(Term a, Term b) {
  a = wnf(a);
  b = wnf(b);
  if (term_tag(a) != NUM || term_tag(b) != NUM) {
    fprintf(stderr, "@@or: expected NUMs\n");
    exit(1);
  }
  return term_new_num(term_val(a) | term_val(b));
}
