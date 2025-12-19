// DynDup(lab, val, bod): dynamic DUP binder, strict on lab
// Layout: HEAP[loc+0] = lab, HEAP[loc+1] = val, HEAP[loc+2] = bod
fn Term term_new_ddu(Term lab, Term val, Term bod) {
  u32 loc = heap_alloc(3);
  HEAP[loc + 0] = lab;
  HEAP[loc + 1] = val;
  HEAP[loc + 2] = bod;
  return term_new(0, DDU, 0, loc);
}
