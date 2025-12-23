// USE: λ{f} - reduce arg and apply
// fields = [f]
fn Term term_new_use(Term f) {
  u32 loc = heap_alloc(1);
  HEAP[loc] = f;
  return term_new(0, USE, 0, loc);
}
