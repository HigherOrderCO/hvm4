// @@opr(&L{a,b}, y)
// ------------------------- OP2-SUP
// ! Y &L = y
// &L{@@opr(a,Y₀), @@opr(b,Y₁)}
fn Term wnf_op2_sup(u32 opr, Term sup, Term y) {
  ITRS++;
  u32  lab     = term_ext(sup);
  u32  sup_loc = term_val(sup);
  Copy Y       = term_clone(lab, y);
  Term op0     = term_new_op2(opr, heap_get(sup_loc + 0), Y.k0);
  Term op1     = term_new_op2(opr, heap_get(sup_loc + 1), Y.k1);
  return term_new_sup(lab, op0, op1);
}
