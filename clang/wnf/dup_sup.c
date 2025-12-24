// ! X &L = &R{a,b}
// ---------------- DUP-SUP
// if L == R:
//   X₀ ← a
//   X₁ ← b
// else:
//   ! A &L = a
//   ! B &L = b
//   X₀ ← &R{A₀,B₀}
//   X₁ ← &R{A₁,B₁}
fn Term wnf_dup_sup(u32 lab, u32 loc, u8 side, Term sup) {
  ITRS++;
  u32 sup_loc = term_val(sup);
  u32 sup_lab = term_ext(sup);
  if (lab == sup_lab) {
    Term tm0 = heap_get(sup_loc + 0);
    Term tm1 = heap_get(sup_loc + 1);
    return heap_subst_cop(side, loc, tm0, tm1);
  } else {
    Copy A  = term_clone(lab, heap_get(sup_loc + 0));
    Copy B  = term_clone(lab, heap_get(sup_loc + 1));
    u64  a  = heap_alloc(4);
    Term s0 = term_new_sup_at(a + 0, sup_lab, A.k0, B.k0);
    Term s1 = term_new_sup_at(a + 2, sup_lab, A.k1, B.k1);
    return heap_subst_cop(side, loc, s0, s1);
  }
}
