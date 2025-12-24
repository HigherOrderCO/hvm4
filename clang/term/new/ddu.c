// DynDup(lab, val, bod): dynamic DUP binder, strict on lab
// Layout: heap_get(loc+0) = lab, heap_get(loc+1) = val, heap_get(loc+2) = bod
fn Term term_new_ddu(Term lab, Term val, Term bod) {
  u32 loc = heap_alloc(3);
  heap_set(loc + 0, lab);
  heap_set(loc + 1, val);
  heap_set(loc + 2, bod);
  return term_new(0, DDU, 0, loc);
}
