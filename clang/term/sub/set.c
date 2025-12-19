fn Term term_sub_set(Term t, u8 sub) {
  return (t & ~(((u64)SUB_MASK) << SUB_SHIFT)) | (((u64)(sub & SUB_MASK)) << SUB_SHIFT);
}
