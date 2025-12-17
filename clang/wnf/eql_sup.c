// (&L{a0,a1} === b)
// ---------------------- eql-sup-l
// ! B &L = b
// &L{(a0 === B₀), (a1 === B₁)}
fn Term wnf_eql_sup_l(Term sup, Term b) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_eql(HEAP[loc + 1], b);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_eql(HEAP[loc + 0], b);
  }
  Term a0  = HEAP[loc + 0];
  Term a1  = HEAP[loc + 1];
  u64  dup_loc = heap_alloc(2);
  HEAP[dup_loc + 0] = b;
  Term b0 = term_new_co0(lab, dup_loc);
  Term b1 = term_new_co1(lab, dup_loc);
  Term eq0 = term_new_eql(a0, b0);
  Term eq1 = term_new_eql(a1, b1);
  return term_new_sup(lab, eq0, eq1);
}

// (a === &L{b0,b1})
// ---------------------- eql-sup-r
// ! A &L = a
// &L{(A₀ === b0), (A₁ === b1)}
fn Term wnf_eql_sup_r(Term a, Term sup) {
  ITRS++;
  u32  lab = term_ext(sup);
  u32  loc = term_val(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_eql(a, HEAP[loc + 1]);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_eql(a, HEAP[loc + 0]);
  }
  Term b0  = HEAP[loc + 0];
  Term b1  = HEAP[loc + 1];
  u64  dup_loc = heap_alloc(2);
  HEAP[dup_loc + 0] = a;
  Term a0 = term_new_co0(lab, dup_loc);
  Term a1 = term_new_co1(lab, dup_loc);
  Term eq0 = term_new_eql(a0, b0);
  Term eq1 = term_new_eql(a1, b1);
  return term_new_sup(lab, eq0, eq1);
}
