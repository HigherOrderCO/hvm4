// UNS: ! ${f, v}; body - unscoped binding
// fields = [body]
fn Term term_new_uns(Term bod) {
  u32 loc = heap_alloc(1);
  HEAP[loc] = bod;
  return term_new(0, UNS, 0, loc);
}

