// Flatten: lazy collapse + extraction via priority queue traversal.
// INC nodes decrease priority (explored earlier), SUP nodes increase priority.
// Uses collapse_step_opt to handle UNDUP optimization.

fn void collapse_flatten(Term term, int limit, int show_itrs) {
  // Priority queue for collapse ordering
  PQueue pq;
  pqueue_init(&pq);

  // Anchor the root term at a heap location
  u32 root_loc = heap_alloc(1);
  HEAP[root_loc] = term;
  PARENT[root_loc] = 0;  // Root has no parent
  pqueue_push(&pq, (PQItem){.pri = 0, .loc = root_loc});

  int count = 0;
  PQItem it;

  while (pqueue_pop(&pq, &it) && (limit < 0 || count < limit)) {
    u32 loc = it.loc;
    u8  pri = it.pri;

    // Lazy collapse with UNDUP optimization
    Term t = collapse_step_opt(loc);
    HEAP[loc] = t;

    // INC fast-path: peel chain of INC wrappers, decrementing priority
    while (term_tag(t) == INC) {
      u32 inc_loc = term_val(t);
      PARENT[inc_loc] = loc;  // Track parent
      loc = inc_loc;
      t = collapse_step_opt(loc);
      HEAP[loc] = t;
      if (pri > 0) pri--;  // decrement priority, clamped at 0
    }

    if (term_tag(t) == SUP) {
      // SUP at top - enqueue both branches with pri+1
      u32 sup_loc = term_val(t);
      // Set parent pointers for both children
      PARENT[sup_loc + 0] = loc;
      PARENT[sup_loc + 1] = loc;
      pqueue_push(&pq, (PQItem){.pri = (u8)(pri + 1), .loc = sup_loc + 0});
      pqueue_push(&pq, (PQItem){.pri = (u8)(pri + 1), .loc = sup_loc + 1});
    } else if (term_tag(t) != ERA) {
      // Non-SUP, non-ERA result - normalize and print
      t = snf(t, 0);
      print_term(t);
      if (show_itrs) {
        printf(" \033[2m#%llu\033[0m", ITRS);
      }
      printf("\n");
      count++;
    }
  }

  pqueue_free(&pq);
}
