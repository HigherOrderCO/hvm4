// % F = λx.f
// ---------- MOV-LAM
// F ← λx.G
// % G = f
fn Term wnf_mov_lam(u32 loc, Term lam) {
  ITRS++;
  u32  lam_loc = term_val(lam);
  u32  lam_ext = term_ext(lam);
  Term bod     = heap_read(lam_loc);

  u32 g_loc = 0;
  // Reuse existing MOV body slot if this lambda was already expanded once.
  if (term_tag(bod) == VAR) {
    u32  old_x = term_val(bod);
    Term got  = heap_read(old_x);
    if (term_tag(got) == GOT) {
      g_loc = term_val(got);
    }
  }

  u64 base = heap_alloc(2);
  u32 x_loc = (u32)base;
  if (g_loc == 0) {
    u32 new_g = x_loc + 1;
    heap_write(new_g, bod);
    g_loc = new_g;
    heap_subst_var(lam_loc, term_new(0, VAR, 0, x_loc));
  }
  heap_write(x_loc, term_new_got(g_loc));
  Term res     = term_new(0, LAM, lam_ext, x_loc);
  if (!SAFE_MOV || (lam_ext & LAM_ERA_MASK)) {
    heap_subst_var(loc, res);
  }
  return res;
}
