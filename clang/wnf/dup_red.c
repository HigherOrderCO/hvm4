// ! X &L = f ~> g
// --------------- dup-red
// ! F &L = f
// ! G &L = g
// X₀ ← F₀ ~> G₀
// X₁ ← F₁ ~> G₁
fn Term wnf_dup_red(u32 lab, u32 loc, u8 side, Term red) {
  ITRS++;
  // UNDUP optimization: skip duplication if one side is unused
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return heap_subst_cop(side, loc, term_new_era(), red);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return heap_subst_cop(side, loc, red, term_new_era());
  }
  u32  r_loc = term_val(red);
  Copy F     = term_clone(lab, HEAP[r_loc + 0]);
  Copy G     = term_clone(lab, HEAP[r_loc + 1]);
  Term r0    = term_new_red(F.k0, G.k0);
  Term r1    = term_new_red(F.k1, G.k1);
  return heap_subst_cop(side, loc, r0, r1);
}
