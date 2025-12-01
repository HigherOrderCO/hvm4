// @@not(a)
// -------- prim-not
// ~a
fn Term prim_not(Term a) {
  a = wnf(a);
  if (term_tag(a) != NUM) {
    fprintf(stderr, "@@not: expected NUM\n");
    exit(1);
  }
  return term_new_num(~term_val(a));
}
