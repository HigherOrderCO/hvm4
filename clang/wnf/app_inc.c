// (↑f x)
// -------- APP-INC
// ↑(f x)
fn Term wnf_app_inc(Term app, Term inc) {
  ITRS++;
  u32  app_loc = term_val(app);
  u32  inc_loc = term_val(inc);
  Term f       = heap_get(inc_loc);
  Term x       = heap_get(app_loc + 1);
  // Reuse inc_loc for the new app, build new inc at app_loc
  heap_set(inc_loc + 0, f);
  // Need to allocate since app has 2 slots, inc has 1
  u64 new_app_loc = heap_alloc(2);
  heap_set(new_app_loc + 0, f);
  heap_set(new_app_loc + 1, x);
  Term new_app = term_new(0, APP, 0, new_app_loc);
  heap_set(app_loc, new_app);
  return term_new(0, INC, 0, app_loc);
}
