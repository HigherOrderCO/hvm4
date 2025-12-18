// (swi (g ~> h))
// --------------- swi-red
// (swi h)
//
// When SWI receives a RED, drop the guard g and continue with h.
fn Term wnf_swi_red(Term red) {
  u32  red_loc = term_val(red);
  Term h       = HEAP[red_loc + 1];
  return h;
}
