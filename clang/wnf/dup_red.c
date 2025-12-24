// ! X &L = f ~> g
// --------------- DUP-RED
// ! F &L = f
// ! G &L = g
// X₀ ← F₀ ~> G₀
// X₁ ← F₁ ~> G₁
fn Term wnf_dup_red(u32 lab, u32 loc, u8 side, Term red) {
  ITRS++;
  u32  r_loc = term_val(red);
  Copy F     = term_clone(lab, heap_read(r_loc + 0));
  Copy G     = term_clone(lab, heap_read(r_loc + 1));
  Term r0    = term_new_red(F.k0, G.k0);
  Term r1    = term_new_red(F.k1, G.k1);
  return heap_subst_cop(side, loc, r0, r1);
}
