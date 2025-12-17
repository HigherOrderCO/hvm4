// (x op &L{a,b}) where x is NUM
// ------------------------- op2-num-sup
// ! X &L = x
// &L{(X₀ op a), (X₁ op b)}
fn Term wnf_op2_num_sup(u32 opr, Term x, Term sup) {
  ITRS++;
  u32  lab     = term_ext(sup);
  u32  sup_loc = term_val(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_op2(opr, x, HEAP[sup_loc + 1]);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_op2(opr, x, HEAP[sup_loc + 0]);
  }
  Copy X       = term_clone(lab, x);
  Term op0     = term_new_op2(opr, X.k0, HEAP[sup_loc + 0]);
  Term op1     = term_new_op2(opr, X.k1, HEAP[sup_loc + 1]);
  return term_new_sup(lab, op0, op1);
}
