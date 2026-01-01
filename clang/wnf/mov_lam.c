// % F = λx.f
// ---------- MOV-LAM
// F ← λx.f
// (No caching - allows fresh re-allocation from ALO on subsequent accesses)
fn Term wnf_mov_lam(u32 loc, Term lam) {
  ITRS++;
  // Do not cache or wrap - return the lambda as-is.
  // This allows fresh re-allocation from ALO on subsequent accesses,
  // which is necessary when the lambda body contains free variables
  // that depend on mutable context (e.g., outer lambda parameters).
  return lam;
}
