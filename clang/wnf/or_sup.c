// (&L{a0,a1} .|. b)
// -------------------------- OR-SUP
// ! B &L = b
// &L{(a0 .|. B₀), (a1 .|. B₁)}
fn Term wnf_or_sup(Term sup, Term b) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  Term a0  = heap_read(loc + 0);
  Term a1  = heap_read(loc + 1);
  u64  dup_loc = heap_alloc(2);
  heap_set(dup_loc + 0, b);
  Term b0 = term_new_dp0(lab, dup_loc);
  Term b1 = term_new_dp1(lab, dup_loc);
  Term r0 = term_new_or(a0, b0);
  Term r1 = term_new_or(a1, b1);
  return term_new_sup(lab, r0, r1);
}
