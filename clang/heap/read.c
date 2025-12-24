fn Term heap_read(u32 loc) {
  return __atomic_load_n(&HEAP[loc], __ATOMIC_RELAXED);
}
