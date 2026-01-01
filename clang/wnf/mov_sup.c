// % K = &L{x,y}
// ------------- MOV-SUP
// K ← &L{x,y}
// (No caching - allows fresh re-allocation from ALO on subsequent accesses)
fn Term wnf_mov_sup(u32 loc, Term sup) {
  ITRS++;
  // Do not cache or wrap - return the sup as-is.
  return sup;
}
