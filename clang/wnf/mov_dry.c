// % X = ^(f x)
// -------------- MOV-DRY
// X ← ^(f x)
fn Term wnf_mov_dry(u32 loc, Term dry) {
  ITRS++;
  return dry;
}
