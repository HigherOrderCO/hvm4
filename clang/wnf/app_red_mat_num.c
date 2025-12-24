// ((f ~> λ{n:z; m}) #n)
// --------------------- APP-RED-MAT-NUM-MAT
// (f #n) ~> z
fn Term wnf_app_red_mat_num_match(Term f, Term mat, Term num) {
  ITRS++;
  u32  mat_loc = term_val(mat);
  Term z       = heap_get(mat_loc + 0);
  return term_new_red(term_new_app(f, num), z);
}

// ((f ~> λ{n:z; m}) #k) where k != n
// ---------------------------------- APP-RED-MAT-NUM-MIS
// ((λp.(f p) ~> m) #k)
fn Term wnf_app_red_mat_num_miss(Term f, Term mat, Term num) {
  ITRS++;
  u32  mat_loc = term_val(mat);
  Term m       = heap_get(mat_loc + 1);

  // Build λp.(f p)
  u64 lam_loc   = heap_alloc(1);
  Term var_p    = term_new(0, VAR, 0, lam_loc);
  Term body     = term_new_app(f, var_p);
  heap_set(lam_loc, body);
  Term lam      = term_new(0, LAM, 0, lam_loc);

  // (lam ~> m) #k
  return term_new_app(term_new_red(lam, m), num);
}
