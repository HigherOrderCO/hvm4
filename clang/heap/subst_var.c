fn void heap_subst_var(u32 loc, Term val) {
  heap_store_shared(loc, term_sub_set(val, 1));
}
