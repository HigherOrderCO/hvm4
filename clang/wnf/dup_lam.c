// ! F &L = λx.f
// ---------------- DUP-LAM
// F₀ ← λ$x0.G₀
// F₁ ← λ$x1.G₁
// x  ← &L{$x0,$x1}
// ! G &L = f
fn Term wnf_dup_lam(u32 lab, u32 loc, u8 side, Term lam) {
  ITRS++;
  u32  lam_loc = term_val(lam);
  Term bod     = HEAP[lam_loc];
  u64  a       = heap_alloc(5);
  HEAP[a + 4]  = bod;
  Copy B  = term_clone_at(a + 4, lab);
  Term su = term_new_sup_at(a + 2, lab, term_new_var(a), term_new_var(a + 1));
  Term l0 = term_new_lam_at(a + 0, B.k0);
  Term l1 = term_new_lam_at(a + 1, B.k1);
  heap_subst_var(lam_loc, su);
  return heap_subst_cop(side, loc, l0, l1);
}
