fn void heap_recompute_banks(void) {
  u32 threads = thread_get_count();
  u64 words = HEAP_CAP;
  u64 bank_sz = words / (u64)threads;
  if (bank_sz == 0) bank_sz = 1;
  for (u32 t = 0; t < threads; ++t) {
    u64 base = (u64)t * bank_sz;
    u64 end  = base + bank_sz;
    if (t == threads - 1) {
      end = words;
    }
    HEAP_BASE[t].v = base;
    HEAP_END[t].v  = end;
    HEAP_NEXT[t].v = (t == 0 && base == 0) ? 1 : base;
  }
}

fn u64 heap_alloc(u64 size) {
  if (size == 0) return 0;
  u64 at = HEAP_NEXT_LOCAL;
  u64 next = at + size;
  if (next > HEAP_END_LOCAL) {
    fprintf(stderr, "heap_alloc: out of memory in bank %u (need %llu words)\n",
            wnf_tid(), (unsigned long long)size);
    exit(1);
  }
  HEAP_NEXT_LOCAL = next;
  return at;
}
