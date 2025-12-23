// INC: ↑x - priority wrapper for collapse ordering
// fields = [x]
fn Term term_new_inc(Term x) {
  u32 loc = heap_alloc(1);
  HEAP[loc] = x;
  return term_new(0, INC, 0, loc);
}
