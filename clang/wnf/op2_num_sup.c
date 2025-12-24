// (x op &L{a,b}) where x is NUM
// ------------------------- OP2-NUM-SUP
// ! X &L = x
// &L{(X₀ op a), (X₁ op b)}
fn Term wnf_op2_num_sup(u32 opr, Term x, Term sup) {
  ITRS++;
  u32  lab     = term_ext(sup);
  u32  sup_loc = term_val(sup);
  Copy X       = term_clone(lab, x);
  Term op0     = term_new_op2(opr, X.k0, heap_get(sup_loc + 0));
  Term op1     = term_new_op2(opr, X.k1, heap_get(sup_loc + 1));
  return term_new_sup(lab, op0, op1);
}
