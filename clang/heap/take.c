fn Term heap_take(u32 loc) {
  if (__builtin_expect(THREAD_COUNT == 1, 1)) {
    Term term = HEAP[loc];
    if (__builtin_expect(term != 0, 1)) {
      return term;
    }
    fprintf(stderr, "ERROR: heap_take saw zero at %u in single-threaded mode\n", loc);
    abort();
  }
  for (;;) {
    Term prev = __atomic_exchange_n(&HEAP[loc], 0, __ATOMIC_RELAXED);
    if (__builtin_expect(prev != 0, 1)) {
      return prev;
    }
    cpu_relax();
  }
}
