// (&L{a0,a1} === b)
// ---------------------- EQL-SUP-L
// ! B &L = b
// &L{(a0 === B₀), (a1 === B₁)}
fn Term wnf_eql_sup_l(Term sup, Term b) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  Term a0  = heap_get(loc + 0);
  Term a1  = heap_get(loc + 1);
  u64  dup_loc = heap_alloc(2);
  heap_set(dup_loc + 0, b);
  Term b0 = term_new_dp0(lab, dup_loc);
  Term b1 = term_new_dp1(lab, dup_loc);
  Term eq0 = term_new_eql(a0, b0);
  Term eq1 = term_new_eql(a1, b1);
  return term_new_sup(lab, eq0, eq1);
}

// (a === &L{b0,b1})
// ---------------------- EQL-SUP-R
// ! A &L = a
// &L{(A₀ === b0), (A₁ === b1)}
fn Term wnf_eql_sup_r(Term a, Term sup) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  Term b0  = heap_get(loc + 0);
  Term b1  = heap_get(loc + 1);
  u64  dup_loc = heap_alloc(2);
  heap_set(dup_loc + 0, a);
  Term a0 = term_new_dp0(lab, dup_loc);
  Term a1 = term_new_dp1(lab, dup_loc);
  Term eq0 = term_new_eql(a0, b0);
  Term eq1 = term_new_eql(a1, b1);
  return term_new_sup(lab, eq0, eq1);
}
