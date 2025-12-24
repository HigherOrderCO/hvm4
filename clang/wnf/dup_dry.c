// ! X &L = ^(f x)
// --------------- DUP-DRY
// ! F &L = f
// ! A &L = x
// X₀ ← ^(F₀ A₀)
// X₁ ← ^(F₁ A₁)
fn Term wnf_dup_dry(u32 lab, u32 loc, u8 side, Term dry) {
  ITRS++;
  u32  d_loc = term_val(dry);
  Copy F     = term_clone(lab, heap_read(d_loc + 0));
  Copy A     = term_clone(lab, heap_read(d_loc + 1));
  Term r0    = term_new_dry(F.k0, A.k0);
  Term r1    = term_new_dry(F.k1, A.k1);
  return heap_subst_cop(side, loc, r0, r1);
}
