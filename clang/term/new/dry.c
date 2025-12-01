fn Term term_new_dry_at(u32 loc, Term fun, Term arg) {
  return term_new_at(loc, DRY, 0, 2, (Term[]){fun, arg});
}

fn Term term_new_dry(Term fun, Term arg) {
  return term_new_dry_at(heap_alloc(2), fun, arg);
}
