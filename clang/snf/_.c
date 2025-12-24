fn Term snf(Term term, u32 depth, u8 quoted) {
  if (!quoted) {
    return snf_par(term, depth, quoted);
  }
  SnfState st = {0};
  u32_set_init(&st.seen, SNF_SEEN_INIT);
  u32 root_loc = heap_alloc(1);
  heap_set(root_loc, term);
  snf_at(root_loc, depth, quoted, &st);
  u32_set_free(&st.seen);
  return heap_get(root_loc);
}
