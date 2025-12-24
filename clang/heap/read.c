fn Term heap_read(u32 loc) {
  for (;;) {
    Term term = __atomic_load_n(&HEAP[loc], __ATOMIC_RELAXED);
    if (__builtin_expect(term != 0, 1)) {
      return term;
    }
    cpu_relax();
  }
}
