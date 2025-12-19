// @{s} ^(f x)
// -------------- ALO-DRY
// ^(@{s}f @{s}x)
fn Term wnf_alo_dry(u32 ls_loc, u32 len, u32 loc) {
  u64 alo_loc0 = heap_alloc(1);
  u64 alo_loc1 = heap_alloc(1);
  HEAP[alo_loc0] = ((u64)ls_loc << 32) | (loc + 0);
  HEAP[alo_loc1] = ((u64)ls_loc << 32) | (loc + 1);
  Term fun = term_new(0, ALO, len, alo_loc0);
  Term arg = term_new(0, ALO, len, alo_loc1);
  return term_new_dry(fun, arg);
}
