// collapse/flatten_par.c — Parallel collapse + flatten

typedef struct {
  CollapseQueue q;
  pthread_mutex_t q_mtx;
  pthread_mutex_t out_mtx;
  _Atomic int64_t pending;
  _Atomic u64 printed;
  _Atomic int stop;
  int limit;
  int show_itrs;
} CollParCtx;

typedef struct { CollParCtx* C; u32 tid; } CollParArg;

static inline void coll_par_push(CollParCtx* C, u8 pri, u32 loc) {
  pthread_mutex_lock(&C->q_mtx);
  collapse_queue_push(&C->q, (CollapseQueueItem){.pri = pri, .loc = loc});
  pthread_mutex_unlock(&C->q_mtx);
  atomic_fetch_add_explicit(&C->pending, 1, memory_order_relaxed);
}

static inline u8 coll_par_pop(CollParCtx* C, CollapseQueueItem* out) {
  u8 ok = 0;
  pthread_mutex_lock(&C->q_mtx);
  ok = collapse_queue_pop(&C->q, out);
  pthread_mutex_unlock(&C->q_mtx);
  return ok;
}

static void* collapse_par_worker(void* ap) {
  CollParArg* A = (CollParArg*)ap;
  CollParCtx* C = A->C;
  u32 tid = A->tid;
  thread_set_qos();
  wnf_set_tid(tid);

  for (;;) {
    if (atomic_load_explicit(&C->stop, memory_order_acquire)) {
      break;
    }

    CollapseQueueItem it;
    if (!coll_par_pop(C, &it)) {
      if (atomic_load_explicit(&C->pending, memory_order_acquire) == 0) break;
      sched_yield();
      continue;
    }

    u32 loc = it.loc;
    u8  pri = it.pri;

    Term t = collapse_step(HEAP[loc]);
    HEAP[loc] = t;

    while (term_tag(t) == INC) {
      u32 inc_loc = term_val(t);
      loc = inc_loc;
      t = collapse_step(HEAP[loc]);
      HEAP[loc] = t;
      if (pri > 0) pri--;
    }

    if (term_tag(t) == SUP) {
      u32 sup_loc = term_val(t);
      coll_par_push(C, (u8)(pri + 1), sup_loc + 0);
      coll_par_push(C, (u8)(pri + 1), sup_loc + 1);
      atomic_fetch_sub_explicit(&C->pending, 1, memory_order_release);
      continue;
    }

    if (term_tag(t) == ERA) {
      atomic_fetch_sub_explicit(&C->pending, 1, memory_order_release);
      continue;
    }

    Term nf = snf(t, 0, 1);

    pthread_mutex_lock(&C->out_mtx);
    u64 prev = atomic_load_explicit(&C->printed, memory_order_relaxed);
    if (C->limit < 0 || (int)prev < C->limit) {
      print_term_quoted(nf);
      if (C->show_itrs) {
        printf(" \033[2m#%llu\033[0m", wnf_itrs_total());
      }
      printf("\n");
      atomic_fetch_add_explicit(&C->printed, 1, memory_order_relaxed);
    }
    pthread_mutex_unlock(&C->out_mtx);

    if (C->limit >= 0) {
      u64 done = atomic_load_explicit(&C->printed, memory_order_acquire);
      if ((int)done >= C->limit) {
        atomic_store_explicit(&C->stop, 1, memory_order_release);
      }
    }

    atomic_fetch_sub_explicit(&C->pending, 1, memory_order_release);
  }

  wnf_itrs_flush();
  return NULL;
}

fn void collapse_flatten_par(Term term, int limit, int show_itrs) {
  CollParCtx C;
  collapse_queue_init(&C.q);
  pthread_mutex_init(&C.q_mtx, NULL);
  pthread_mutex_init(&C.out_mtx, NULL);
  atomic_store_explicit(&C.pending, 0, memory_order_relaxed);
  atomic_store_explicit(&C.printed, 0, memory_order_relaxed);
  atomic_store_explicit(&C.stop, 0, memory_order_relaxed);
  C.limit = limit;
  C.show_itrs = show_itrs;

  u32 root_loc = heap_alloc(1);
  HEAP[root_loc] = term;
  coll_par_push(&C, 0, root_loc);

  heap_bank_flush();

  u32 n = thread_get_count();
  if (n == 0) n = 1;
  if (n > MAX_THREADS) n = MAX_THREADS;

  pthread_t tids[MAX_THREADS];
  CollParArg args[MAX_THREADS];
  for (u32 i = 1; i < n; ++i) {
    args[i].C = &C;
    args[i].tid = i;
    pthread_create(&tids[i], NULL, collapse_par_worker, &args[i]);
  }

  args[0].C = &C;
  args[0].tid = 0;
  collapse_par_worker(&args[0]);

  for (u32 i = 1; i < n; ++i) {
    pthread_join(tids[i], NULL);
  }

  collapse_queue_free(&C.q);
  pthread_mutex_destroy(&C.q_mtx);
  pthread_mutex_destroy(&C.out_mtx);
}
