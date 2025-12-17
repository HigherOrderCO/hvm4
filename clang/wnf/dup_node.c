// ! X &L = #K{a,b,...}
// -------------------- dup-ctr/mat/era
// ! A &L = a
// ! B &L = b
// ...
// X₀ ← #K{A₀,B₀,...}
// X₁ ← #K{A₁,B₁,...}
fn Term wnf_dup_node(u32 lab, u32 loc, u8 side, Term term) {
  ITRS++;
  // UNDUP optimization: skip duplication if one side is unused
  if (UNDUP && UNDUP[lab] == UNDUP_0) {
    return heap_subst_cop(side, loc, term_new_era(), term);
  }
  if (UNDUP && UNDUP[lab] == UNDUP_1) {
    return heap_subst_cop(side, loc, term, term_new_era());
  }
  u32 ari = term_arity(term);
  if (ari == 0) {
    heap_subst_var(loc, term);
    return term;
  }
  u32  t_loc = term_val(term);
  u32  t_ext = term_ext(term);
  u8   t_tag = term_tag(term);
  Term args0[16], args1[16];
  for (u32 i = 0; i < ari; i++) {
    Copy A   = term_clone(lab, HEAP[t_loc + i]);
    args0[i] = A.k0;
    args1[i] = A.k1;
  }
  Term r0 = term_new_(t_tag, t_ext, ari, args0);
  Term r1 = term_new_(t_tag, t_ext, ari, args1);
  return heap_subst_cop(side, loc, r0, r1);
}
