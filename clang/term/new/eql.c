// Eql(a, b): structural equality, strict on a first then b
// Layout: heap_get(loc+0) = a, heap_get(loc+1) = b
// Returns #1 if equal, #0 if not
fn Term term_new_eql(Term a, Term b) {
  u32 loc = heap_alloc(2);
  heap_set(loc + 0, a);
  heap_set(loc + 1, b);
  return term_new(0, EQL, 0, loc);
}
