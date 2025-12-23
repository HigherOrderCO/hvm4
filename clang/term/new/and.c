// And(a, b): short-circuit AND, strict on a only
// Layout: HEAP[loc+0] = a, HEAP[loc+1] = b
// Returns b if a is non-zero, #0 if a is zero
fn Term term_new_and(Term a, Term b) {
  u32 loc = heap_alloc(2);
  HEAP[loc + 0] = a;
  HEAP[loc + 1] = b;
  return term_new(0, AND, 0, loc);
}
