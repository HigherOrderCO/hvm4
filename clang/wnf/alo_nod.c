// @{s} T{a,b,...}
// ---------------- ALO-NOD
// T{@{s}a, @{s}b, ...}
fn Term wnf_alo_nod(u32 ls_loc, u32 len, u32 loc, u8 tag, u32 ext, u32 ari) {
  Term args[16];
  for (u32 i = 0; i < ari; i++) {
    u64 alo_loc = heap_alloc(1);
    HEAP[alo_loc] = ((u64)ls_loc << 32) | (loc + i);
    args[i] = term_new(0, ALO, len, alo_loc);
  }
  return term_new_(tag, ext, ari, args);
}
