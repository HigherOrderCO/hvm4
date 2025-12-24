// ! X &L = name
// ------------ DUP-NAM
// X₀ ← name
// X₁ ← name
fn Term wnf_dup_nam(u32 lab, u32 loc, u8 side, Term nam) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_DUP_NAM);
  heap_subst_var(loc, nam);
  return nam;
}
