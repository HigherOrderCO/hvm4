// @@dup(lab, val, fun)
// -------------------------- prim-dup
// !X &lab = val; fun(X₀,X₁)
fn Term prim_dup(Term lab, Term val, Term fun) {
  lab = wnf(lab);
  if (term_tag(lab) != NUM) {
    fprintf(stderr, "@@dup: expected NUM for label\n");
    exit(1);
  }
  u32 lab_val = term_val(lab);
  u32 loc = heap_alloc(2);
  Term x0 = term_new_co0(lab_val, loc);
  Term x1 = term_new_co1(lab_val, loc);
  Term bod = term_new_app(term_new_app(fun, x0), x1);
  HEAP[loc + 0] = val;
  HEAP[loc + 1] = bod;
  return term_new(0, DUP, lab_val, loc);
}

