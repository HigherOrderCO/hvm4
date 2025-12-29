// (name === name)  (same tag/ext/val)
// -----------------------------------
// #1
//
// (name === other) (different tag/ext/val)
// ----------------------------------------
// #0
fn Term wnf_eql_nam(Term a, Term b) {
  ITRS_INC("-");
  u8  a_tag = term_tag(a);
  u8  b_tag = term_tag(b);
  u32 a_ext = term_ext(a);
  u32 b_ext = term_ext(b);
  u32 a_val = term_val(a);
  u32 b_val = term_val(b);
  return term_new_num((a_tag == b_tag) && (a_ext == b_ext) && (a_val == b_val));
}
