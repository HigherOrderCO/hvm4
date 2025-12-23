// DynSup(lab, a, b): dynamic superposition, strict on lab
// Layout: HEAP[loc+0] = lab, HEAP[loc+1] = a, HEAP[loc+2] = b
fn Term term_new_dsu(Term lab, Term a, Term b) {
  u32 loc = heap_alloc(3);
  HEAP[loc + 0] = lab;
  HEAP[loc + 1] = a;
  HEAP[loc + 2] = b;
  return term_new(0, DSU, 0, loc);
}
