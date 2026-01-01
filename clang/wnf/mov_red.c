// % X = f ~> g
// ------------- MOV-RED
// X ← f ~> g
fn Term wnf_mov_red(u32 loc, Term red) {
  ITRS++;
  return red;
}
