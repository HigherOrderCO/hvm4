// ! X &L = T{a,b,...}
// ------------------- DUP-NOD
// ! A &L = a
// ! B &L = b
// ...
// X₀ ← T{A₀,B₀,...}
// X₁ ← T{A₁,B₁,...}
fn Term wnf_dup_nod(u32 lab, u32 loc, u8 side, Term term) {
  ITRS++;
  ITRS_KIND(WNF_ITRS_DUP_NOD);
  u32 ari = term_arity(term);
  if (ari == 0) {
    heap_subst_var(loc, term);
    return term;
  }
  u32  t_loc = term_val(term);
  u32  t_ext = term_ext(term);
  u8   t_tag = term_tag(term);
  u64  vals  = heap_alloc(ari);
  Term args0[16], args1[16];
  for (u32 i = 0; i < ari; i++) {
    heap_set(vals + i, heap_read(t_loc + i));
    Copy A   = term_clone_at(vals + i, lab);
    args0[i] = A.k0;
    args1[i] = A.k1;
  }
  Term r0 = term_new_(t_tag, t_ext, ari, args0);
  Term r1 = term_new_(t_tag, t_ext, ari, args1);
  return heap_subst_cop(side, loc, r0, r1);
}
