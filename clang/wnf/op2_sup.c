// @@opr(&L{a,b}, y)
// ------------------------- op2-sup
// ! Y &L = y
// &L{@@opr(a,Y₀), @@opr(b,Y₁)}
fn Term wnf_op2_sup(u32 opr, Term sup, Term y) {
  ITRS++;
  u32  lab     = term_ext(sup);
  u32  sup_loc = term_val(sup);
  // UNDUP: skip to used branch
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return term_new_op2(opr, HEAP[sup_loc + 1], y);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return term_new_op2(opr, HEAP[sup_loc + 0], y);
  }
  Copy Y       = term_clone(lab, y);
  Term op0     = term_new_op2(opr, HEAP[sup_loc + 0], Y.k0);
  Term op1     = term_new_op2(opr, HEAP[sup_loc + 1], Y.k1);
  return term_new_sup(lab, op0, op1);
}
