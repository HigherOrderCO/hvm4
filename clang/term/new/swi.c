// SWI: λ{num: f; g} - number switch (same as MAT but for parser/printer)
fn Term term_new_swi(u32 num, Term f, Term g) {
  u32 loc = heap_alloc(2);
  HEAP[loc + 0] = f;
  HEAP[loc + 1] = g;
  return term_new(0, SWI, num, loc);
}
