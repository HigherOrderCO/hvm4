fn void heap_subst_var(u32 loc, Term val) {
  HEAP[loc] = term_sub_set(val, 1);
}
