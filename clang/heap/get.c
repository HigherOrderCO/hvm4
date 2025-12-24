fn Term heap_get_raw(u32 loc) {
  return __atomic_load_n(&HEAP[loc], __ATOMIC_RELAXED);
}

fn Term heap_get(u32 loc) {
  for (;;) {
    Term term = heap_get_raw(loc);
    if (__builtin_expect(term != 0, 1)) {
      return term;
    }
    cpu_relax();
  }
}
