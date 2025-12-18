// (use (g ~> h))
// --------------- use-red
// (use h)
//
// When USE receives a RED, drop the guard g and continue with h.
fn Term wnf_use_red(Term red) {
  u32  red_loc = term_val(red);
  Term h       = HEAP[red_loc + 1];
  return h;
}
