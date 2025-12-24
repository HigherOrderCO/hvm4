fn Term heap_peek(u32 loc) {
  for (;;) {
    Term term = heap_read(loc);
    if (__builtin_expect(term != 0, 1)) {
      return term;
    }
    cpu_relax();
  }
}
