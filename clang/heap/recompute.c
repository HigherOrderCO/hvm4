fn void heap_recompute(void) {
  u32 threads = thread_get_count();
  if (threads == 0) {
    threads = 1;
  }
  if (threads > MAX_THREADS) {
    threads = MAX_THREADS;
  }

  u64 words = HEAP_CAP;
  u64 bank_sz = words / threads;
  u64 at = 0;

  for (u32 t = 0; t < threads; t++) {
    u64 start = at;
    u64 end = (t == threads - 1) ? words : (at + bank_sz);
    if (t == 0 && start == 0) {
      start = 1;
    }
    HEAP_BANKS[t].start = start;
    HEAP_BANKS[t].end   = end;
    HEAP_BANKS[t].next  = start;
    at += bank_sz;
  }

  for (u32 t = threads; t < MAX_THREADS; t++) {
    HEAP_BANKS[t].start = 0;
    HEAP_BANKS[t].end   = 0;
    HEAP_BANKS[t].next  = 0;
  }
}
