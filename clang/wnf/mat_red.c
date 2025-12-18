// (mat (g ~> h))
// --------------- mat-red
// (mat h)
//
// When MAT receives a RED, drop the guard g and continue with h.
fn Term wnf_mat_red(Term red) {
  u32  red_loc = term_val(red);
  Term h       = HEAP[red_loc + 1];
  return h;
}
