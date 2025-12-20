fn Term heap_subst_cop(u8 side, u32 loc, Term r0, Term r1) {
  heap_store_shared(loc, term_sub_set(side == 0 ? r1 : r0, 1));
  return side == 0 ? r0 : r1;
}
