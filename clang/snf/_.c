fn Term snf(Term term, u32 depth, u8 quoted) {
  SnfState st = {0};
  u32 root_loc = heap_alloc(1);
  HEAP[root_loc] = term;
  snf_at(root_loc, depth, quoted, &st);
  return HEAP[root_loc];
}
