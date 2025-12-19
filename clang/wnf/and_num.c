// (#0 .&. b)
// ---------- AND-ZER
// #0
//
// (#n .&. b)   [n ≠ 0]
// -------------------- AND-ONE
// b
fn Term wnf_and_num(Term num, Term b) {
  ITRS++;
  u32 val = term_val(num);
  if (val == 0) {
    return term_new_num(0);
  } else {
    return b;
  }
}
