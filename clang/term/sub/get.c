fn u8 term_sub_get(Term t) {
  return (t >> SUB_SHIFT) & SUB_MASK;
}
