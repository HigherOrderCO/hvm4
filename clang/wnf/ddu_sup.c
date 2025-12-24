// ! X &(&L{x,y}) = v; b
// ------------------------------ DDU-SUP
// ! V &L = v
// ! B &L = b
// &L{! X &(x) = V₀; B₀, ! X &(y) = V₁; B₁}
fn Term wnf_ddu_sup(Term lab_sup, Term val, Term bod) {
  ITRS++;
  u32  lab     = term_ext(lab_sup);
  u32  sup_loc = term_val(lab_sup);
  Copy V       = term_clone(lab, val);
  Copy B       = term_clone(lab, bod);
  Term dd0     = term_new_ddu(heap_get(sup_loc + 0), V.k0, B.k0);
  Term dd1     = term_new_ddu(heap_get(sup_loc + 1), V.k1, B.k1);
  return term_new_sup(lab, dd0, dd1);
}
