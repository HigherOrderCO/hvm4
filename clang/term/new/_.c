fn Term term_new_at(u32 loc, u8 tag, u32 ext, u32 ari, Term *args) {
  for (u32 i = 0; i < ari; i++) {
    HEAP[loc + i] = args[i];
  }
  return term_new(0, tag, ext, loc);
}

fn Term term_new_(u8 tag, u32 ext, u32 ari, Term *args) {
  return term_new_at(heap_alloc(ari), tag, ext, ari, args);
}
