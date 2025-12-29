// ! X &L = f ~> g
// --------------- DUP-RED
// ! F &L = f
// ! G &L = g
// X₀ ← F₀ ~> G₀
// X₁ ← F₁ ~> G₁
fn Term wnf_dup_red(u32 lab, u32 loc, u8 side, Term red) {
  ITRS_INC("DUP-RED");
  u32  r_loc = term_val(red);
  u64  base  = heap_alloc(6);
  u32  at    = (u32)base;
  heap_write(at + 0, heap_read(r_loc + 0));
  heap_write(at + 1, heap_read(r_loc + 1));
  Copy F     = term_clone_at(at + 0, lab);
  Copy G     = term_clone_at(at + 1, lab);
  Term r0    = term_new_red_at(at + 2, F.k0, G.k0);
  Term r1    = term_new_red_at(at + 4, F.k1, G.k1);
  return heap_subst_cop(side, loc, r0, r1);
}
