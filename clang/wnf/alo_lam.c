// @{s} λx.f
// ------------ ALO-LAM
// x' ← fresh
// λx'.@{x',s}f
fn Term wnf_alo_lam(u32 ls_loc, u32 len, u32 lam_ext, u32 book_body_loc) {
  u64 lam_body = heap_alloc(1);
  u64 bind_ent = heap_alloc(1);
  HEAP[bind_ent] = ((u64)(u32)lam_body << 32) | ls_loc;
  u64 alo_loc = heap_alloc(1);
  HEAP[alo_loc] = ((u64)(u32)bind_ent << 32) | book_body_loc;
  HEAP[lam_body] = term_new(0, ALO, len + 1, alo_loc);
  return term_new(0, LAM, lam_ext, lam_body);
}
