// % X = f ~> g
// ------------- MOV-RED
// % F = f
// % G = g
// X ← F ~> G
fn Term wnf_mov_red(u32 loc, Term red) {
  ITRS++;
  u32  r_loc = term_val(red);
  u64  base  = heap_alloc(4);
  u32  at    = (u32)base;
  heap_write(at + 0, heap_read(r_loc + 0));
  heap_write(at + 1, heap_read(r_loc + 1));
  Term f     = term_new_got(at + 0);
  Term g     = term_new_got(at + 1);
  Term res   = term_new_red_at(at + 2, f, g);
  if (!SAFE_MOV) {
    heap_subst_var(loc, res);
  }
  return res;
}
