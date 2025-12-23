fn u64 heap_alloc(u64 size) {
  u64 at = ALLOC;
  ALLOC += size;
  return at;
}
