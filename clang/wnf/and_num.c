// (#0 .&. b)
// ---------- AND-ZER
// #0
//
// (#n .&. b)   [n ≠ 0]
// -------------------- AND-ONE
// b
fn Term wnf_and_num(Term num, Term b) {
  u32 val = term_val(num);
  if (val == 0) {
    ITRS_INC("AND-ZER");
    return term_new_num(0);
  } else {
    ITRS_INC("AND-ONE");
    return b;
  }
}
