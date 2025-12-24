// &(&L{x,y}){a, b}
// -------------------------- DSU-SUP
// ! A &L = a
// ! B &L = b
// &L{&(x){A₀,B₀}, &(y){A₁,B₁}}
fn Term wnf_dsu_sup(Term lab_sup, Term a, Term b) {
  ITRS++;
  u32  lab     = term_ext(lab_sup);
  u32  sup_loc = term_val(lab_sup);
  Copy A       = term_clone(lab, a);
  Copy B       = term_clone(lab, b);
  Term ds0     = term_new_dsu(heap_read(sup_loc + 0), A.k0, B.k0);
  Term ds1     = term_new_dsu(heap_read(sup_loc + 1), A.k1, B.k1);
  return term_new_sup(lab, ds0, ds1);
}
