// Or(a, b): short-circuit OR, strict on a only
// Layout: HEAP[loc+0] = a, HEAP[loc+1] = b
// Returns #1 if a is non-zero, b if a is zero
fn Term term_new_or(Term a, Term b) {
  u32 loc = heap_alloc(2);
  HEAP[loc + 0] = a;
  HEAP[loc + 1] = b;
  return term_new(0, OR, 0, loc);
}
