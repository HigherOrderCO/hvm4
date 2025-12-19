// (#0 .|. b)
// ---------- OR-ZER
// b
//
// (#n .|. b)   [n ≠ 0]
// -------------------- OR-ONE
// #1
fn Term wnf_or_num(Term num, Term b) {
  ITRS++;
  u32 val = term_val(num);
  if (val == 0) {
    return b;
  } else {
    return term_new_num(1);
  }
}
