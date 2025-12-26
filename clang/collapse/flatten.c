// Flatten
// =======
//
// Lazy collapse + extraction via priority queue traversal.
// INC nodes decrease priority (explored earlier), SUP nodes increase priority.
// Integrates collapse_step to handle infinite structures without stack overflow.

#ifndef COLL_WS_STEAL_PERIOD
#define COLL_WS_STEAL_PERIOD 32u
#endif
#ifndef COLL_WS_STEAL_BATCH
#define COLL_WS_STEAL_BATCH 8u
#endif
#ifndef COLLAPSE_STACK_SIZE
#define COLLAPSE_STACK_SIZE (64u * 1024u * 1024u)
#endif

typedef struct {
  _Alignas(WSQ_L1) _Atomic u64     printed;
  _Alignas(WSQ_L1) _Atomic int     stop;
  _Alignas(WSQ_L1) _Atomic int64_t pending;
  u64  limit;
  int  silent;
  int  show_itrs;
  CollWs ws;
} CollCtx;

typedef struct {
  CollCtx *ctx;
  u32 tid;
} CollArg;

static inline void coll_process_loc(CollCtx *C, u32 me, u8 pri, u32 loc, int64_t *pend_local) {
  for (;;) {
    if (atomic_load_explicit(&C->stop, memory_order_acquire)) {
      return;
    }

    Term t = collapse_step(heap_take(loc), 0);
    heap_set(loc, t);

    while (term_tag(t) == INC) {
      u32 inc_loc = term_val(t);
      loc = inc_loc;
      t = collapse_step(heap_take(loc), 0);
      heap_set(loc, t);
      if (pri > 0) {
        pri -= 1;
      }
    }

    if (term_tag(t) == SUP) {
      u32 sup_loc = term_val(t);
      u8 npri = (u8)(pri + 1);
      coll_ws_push(&C->ws, me, npri, sup_loc + 0);
      coll_ws_push(&C->ws, me, npri, sup_loc + 1);
      *pend_local += 2;
      return;
    }

    if (term_tag(t) == ERA) {
      return;
    }

    u64 prev = atomic_fetch_add_explicit(&C->printed, 1, memory_order_acq_rel);
    if (prev < C->limit) {
      if (!C->silent) {
        print_term_quoted(t);
        if (C->show_itrs) {
          printf(" \033[2m#%llu\033[0m", wnf_itrs_total());
        }
        printf("\n");
      }
    }

    if (prev + 1u >= C->limit) {
      atomic_store_explicit(&C->stop, 1, memory_order_release);
    }
    return;
  }
}

static void *collapse_flatten_worker(void *arg) {
  CollArg *A = (CollArg *)arg;
  CollCtx *C = A->ctx;
  u32 me = A->tid;

  wnf_set_tid(me);

  u32 iter = 0;
  u32 steal_period = COLL_WS_STEAL_PERIOD;
  u32 steal_batch = COLL_WS_STEAL_BATCH;
  int64_t pend_local = 0;

  for (;;) {
    if (atomic_load_explicit(&C->stop, memory_order_acquire)) {
      break;
    }

    u8 pri = 0;
    u32 loc = 0;
    bool has_local = coll_ws_pop(&C->ws, me, &pri, &loc);
    if (has_local) {
      coll_process_loc(C, me, pri, loc, &pend_local);
      pend_local -= 1;
      iter += 1u;
      if ((iter & (steal_period - 1u)) != 0u) {
        continue;
      }
    } else {
      iter = steal_period;
    }

    if (iter >= steal_period) {
      u32 got = coll_ws_steal_some(&C->ws, me, steal_batch, has_local);
      iter = 0;
      if (got > 0u) {
        continue;
      }
    }

    if (pend_local != 0) {
      atomic_fetch_add_explicit(&C->pending, pend_local, memory_order_release);
      pend_local = 0;
    }

    if (atomic_load_explicit(&C->pending, memory_order_acquire) == 0) {
      break;
    }

    cpu_relax();
  }

  if (pend_local != 0) {
    atomic_fetch_add_explicit(&C->pending, pend_local, memory_order_release);
  }

  wnf_itrs_flush(me);
  return NULL;
}

static inline void collapse_flatten_seq(Term term, int limit, int show_itrs, int silent) {
  CollapseQueue pq;
  collapse_queue_init(&pq);

  u32 root_loc = heap_alloc(1);
  heap_set(root_loc, term);
  collapse_queue_push(&pq, (CollapseQueueItem){.pri = 0, .loc = root_loc});

  int count = 0;
  CollapseQueueItem it;

  while (collapse_queue_pop(&pq, &it) && (limit < 0 || count < limit)) {
    u32 loc = it.loc;
    u8  pri = it.pri;

    Term t = collapse_step(heap_read(loc), 0);
    heap_set(loc, t);

    while (term_tag(t) == INC) {
      u32 inc_loc = term_val(t);
      loc = inc_loc;
      t = collapse_step(heap_read(loc), 0);
      heap_set(loc, t);
      if (pri > 0) pri--;
    }

    if (term_tag(t) == SUP) {
      u32 sup_loc = term_val(t);
      collapse_queue_push(&pq, (CollapseQueueItem){.pri = (u8)(pri + 1), .loc = sup_loc + 0});
      collapse_queue_push(&pq, (CollapseQueueItem){.pri = (u8)(pri + 1), .loc = sup_loc + 1});
    } else if (term_tag(t) != ERA) {
      if (!silent) {
        print_term_quoted(t);
        if (show_itrs) {
          printf(" \033[2m#%llu\033[0m", wnf_itrs_total());
        }
        printf("\n");
      }
      count++;
    }
  }

  collapse_queue_free(&pq);
}

fn void collapse_flatten(Term term, int limit, int show_itrs, int silent) {
  u32 n = thread_get_count();
  if (n == 0) {
    n = 1;
  }
  if (n > MAX_THREADS) {
    n = MAX_THREADS;
  }
  if (n == 1) {
    collapse_flatten_seq(term, limit, show_itrs, silent);
    return;
  }
  if (limit == 0) {
    return;
  }

  u64 max_lines = UINT64_MAX;
  if (limit >= 0) {
    max_lines = (u64)limit;
  }

  u32 root_loc = heap_alloc(1);
  heap_set(root_loc, term);

  CollCtx C;
  atomic_store_explicit(&C.printed, 0, memory_order_relaxed);
  atomic_store_explicit(&C.stop, 0, memory_order_relaxed);
  atomic_store_explicit(&C.pending, 0, memory_order_relaxed);
  C.limit = max_lines;
  C.silent = silent;
  C.show_itrs = show_itrs;
  if (!coll_ws_init(&C.ws, n)) {
    fprintf(stderr, "collapse: queue allocation failed\n");
    exit(1);
  }

  coll_ws_push(&C.ws, 0u, 0u, root_loc);
  atomic_fetch_add_explicit(&C.pending, 1, memory_order_relaxed);

  pthread_t tids[MAX_THREADS];
  CollArg args[MAX_THREADS];
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)COLLAPSE_STACK_SIZE);
  for (u32 i = 1; i < n; ++i) {
    args[i].ctx = &C;
    args[i].tid = i;
    pthread_create(&tids[i], &attr, collapse_flatten_worker, &args[i]);
  }
  pthread_attr_destroy(&attr);

  CollArg arg0 = { .ctx = &C, .tid = 0 };
  collapse_flatten_worker(&arg0);

  for (u32 i = 1; i < n; ++i) {
    pthread_join(tids[i], NULL);
  }

  coll_ws_free(&C.ws);
}
