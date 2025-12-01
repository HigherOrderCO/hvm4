// @@ne(a, b)
// ---------- prim-ne
// a != b
fn Term prim_ne(Term a, Term b) {
  a = wnf(a);
  b = wnf(b);
  if (term_tag(a) != NUM || term_tag(b) != NUM) {
    fprintf(stderr, "@@ne: expected NUMs\n");
    exit(1);
  }
  return term_new_num(term_val(a) != term_val(b) ? 1 : 0);
}
