fn u64 heap_alloc(u64 size) {
  HeapBank *bank = &HEAP_BANKS[wnf_tid()];
  u64 at = bank->next;
  u64 next = at + size;
  if (next > bank->end || next < at) {
    fprintf(stderr,
            "Out of heap memory in thread bank %u (need %llu words)\n",
            wnf_tid(), size);
    exit(1);
  }
  bank->next = next;
  return at;
}
