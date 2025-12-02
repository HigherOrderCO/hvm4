// @@sup(lab, a, b)
// ---------------- prim-sup
// &lab{a, b}
fn Term prim_sup(Term lab, Term a, Term b) {
  lab = wnf(lab);
  if (term_tag(lab) != NUM) {
    fprintf(stderr, "@@sup: expected NUM for label\n");
    exit(1);
  }
  u32 lab_val = term_val(lab);
  return term_new_sup(lab_val, a, b);
}

