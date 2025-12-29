// Eval collapse (CNF flattening).
// - Lazy CNF extraction via key queue traversal.
// - Lower numeric keys are popped first.
// - INC decreases key (explored earlier), SUP increases key.
// - Uses cnf to handle infinite structures without stack overflow.

#ifndef EVAL_COLLAPSE_STEAL_PERIOD
#define EVAL_COLLAPSE_STEAL_PERIOD 128u
#endif
#ifndef EVAL_COLLAPSE_STEAL_BATCH
#define EVAL_COLLAPSE_STEAL_BATCH 32u
#endif
#ifndef EVAL_COLLAPSE_STACK_SIZE
#define EVAL_COLLAPSE_STACK_SIZE (64u * 1024u * 1024u)
#endif

typedef struct {
  _Alignas(WSQ_L1) _Atomic u64     printed;
  _Alignas(WSQ_L1) _Atomic int     stop;
  _Alignas(WSQ_L1) _Atomic int64_t pending;
  u64  limit;
  int  silent;
  int  show_itrs;
  Wspq ws;
  CnfPool cnf;
} EvalCollapseCtx;

typedef struct {
  EvalCollapseCtx *ctx;
  u32 tid;
} EvalCollapseArg;

static inline void eval_collapse_process_loc(EvalCollapseCtx *C, u32 me, u8 key, u32 loc, int64_t *pend_local) {
  for (;;) {
    if (atomic_load_explicit(&C->stop, memory_order_acquire)) {
      return;
    }

    Term before = heap_read(loc);
    Term t = cnf(before);
    if (t != before) {
      heap_set(loc, t);
    }

    switch (term_tag(t)) {
      case INC: {
        u32 inc_loc = term_val(t);
        loc = inc_loc;
        Term prev = heap_read(loc);
        t = cnf(prev);
        if (t != prev) {
          heap_set(loc, t);
        }
        if (key > 0) {
          key -= 1;
        }
        continue;
      }
      case SUP: {
        u32 sup_loc = term_val(t);
        u8  nkey = (u8)(key + 1);
        u64 task = ((u64)(sup_loc + 1) << 32) | (u64)(sup_loc + 0);
        wspq_push(&C->ws, me, nkey, task);
        *pend_local += 2;
        return;
      }
      case ERA: {
        return;
      }
      default: {
        u64 prev = atomic_fetch_add_explicit(&C->printed, 1, memory_order_relaxed);
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
  }
}

static void *eval_collapse_worker(void *arg) {
  EvalCollapseArg *A = (EvalCollapseArg *)arg;
  EvalCollapseCtx *C = A->ctx;
  u32 me = A->tid;

  wnf_set_tid(me);

  u32 iter = 0;
  u32 steal_period = EVAL_COLLAPSE_STEAL_PERIOD;
  u32 steal_batch = EVAL_COLLAPSE_STEAL_BATCH;
  u32 steal_cursor = me + 1;
  int64_t pend_local = 0;

  for (;;) {
    if (atomic_load_explicit(&C->stop, memory_order_acquire)) {
      break;
    }

    u8  key = 0;
    u64 task = 0;
    bool has_local = wspq_pop(&C->ws, me, &key, &task);
    if (has_local) {
      u32 loc0 = (u32)task;
      u32 loc1 = (u32)(task >> 32);
      if (loc0 != 0) {
        eval_collapse_process_loc(C, me, key, loc0, &pend_local);
        pend_local -= 1;
        iter += 1u;
      }
      if (loc1 != 0) {
        eval_collapse_process_loc(C, me, key, loc1, &pend_local);
        pend_local -= 1;
        iter += 1u;
      }
      if ((iter & (steal_period - 1u)) != 0u) {
        continue;
      }
    } else {
      iter = steal_period;
    }

    if (iter >= steal_period) {
      u32 got = wspq_steal_some(&C->ws, me, steal_batch, has_local, &steal_cursor);
      iter = 0;
      if (got > 0u) {
        continue;
      }
    }

    if (cnf_pool_try_run()) {
      continue;
    }

    if (pend_local != 0) {
      atomic_fetch_add_explicit(&C->pending, pend_local, memory_order_relaxed);
      pend_local = 0;
    }

    if (atomic_load_explicit(&C->pending, memory_order_relaxed) == 0) {
      if (atomic_load_explicit(&C->cnf.pending, memory_order_relaxed) == 0) {
        break;
      }
    }

    cpu_relax();
  }

  if (pend_local != 0) {
    atomic_fetch_add_explicit(&C->pending, pend_local, memory_order_relaxed);
  }

  wnf_itrs_flush(me);
  return NULL;
}

fn void eval_collapse(Term term, int limit, int show_itrs, int silent) {
  u32 n = thread_get_count();
  if (n == 0) {
    n = 1;
  }
  if (n > MAX_THREADS) {
    n = MAX_THREADS;
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

  EvalCollapseCtx C;
  atomic_store_explicit(&C.printed, 0, memory_order_relaxed);
  atomic_store_explicit(&C.stop, 0, memory_order_relaxed);
  atomic_store_explicit(&C.pending, 0, memory_order_relaxed);
  C.limit = max_lines;
  C.silent = silent;
  C.show_itrs = show_itrs;
  if (!wspq_init(&C.ws, n)) {
    fprintf(stderr, "eval_collapse: queue allocation failed\n");
    exit(1);
  }
  if (!cnf_pool_init(&C.cnf, n)) {
    fprintf(stderr, "eval_collapse: cnf queue allocation failed\n");
    exit(1);
  }
  cnf_pool_set(&C.cnf);

  wspq_push(&C.ws, 0u, 0u, (u64)root_loc);
  atomic_fetch_add_explicit(&C.pending, 1, memory_order_relaxed);

  pthread_t tids[MAX_THREADS];
  EvalCollapseArg args[MAX_THREADS];
  if (n > 1) {
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, (size_t)EVAL_COLLAPSE_STACK_SIZE);
    for (u32 i = 1; i < n; ++i) {
      args[i].ctx = &C;
      args[i].tid = i;
      pthread_create(&tids[i], &attr, eval_collapse_worker, &args[i]);
    }
    pthread_attr_destroy(&attr);
  }

  EvalCollapseArg arg0 = { .ctx = &C, .tid = 0 };
  eval_collapse_worker(&arg0);

  if (n > 1) {
    for (u32 i = 1; i < n; ++i) {
      pthread_join(tids[i], NULL);
    }
  }

  wspq_free(&C.ws);
  cnf_pool_clear();
  cnf_pool_free(&C.cnf);
}
