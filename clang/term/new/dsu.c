// DynSup(lab, a, b): dynamic superposition, strict on lab
// Layout: heap_read(loc+0) = lab, heap_read(loc+1) = a, heap_read(loc+2) = b
fn Term term_new_dsu(Term lab, Term a, Term b) {
  u32 loc = heap_alloc(3);
  heap_set(loc + 0, lab);
  heap_set(loc + 1, a);
  heap_set(loc + 2, b);
  return term_new(0, DSU, 0, loc);
}
