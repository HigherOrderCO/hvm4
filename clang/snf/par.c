// snf/par.c — Parallel normalization (work-stealing)

typedef struct { _Atomic size_t v; char _pad[128 - sizeof(_Atomic size_t)]; } TqIdx;

typedef struct __attribute__((aligned(128))) {
  TqIdx  top;   // steals from top
  TqIdx  bot;   // owner pushes/pops from bottom
  u32*   buf;
  size_t mask;  // cap - 1
  size_t cap;
} TaskQueue;

static inline u32 tq_next_pow2(u32 x) {
  if (x < 2u) return 2u;
  x--; x |= x >> 1; x |= x >> 2; x |= x >> 4; x |= x >> 8; x |= x >> 16; x++;
  return x;
}

static inline void* tq_aligned_alloc(size_t alignment, size_t nbytes) {
  void* p = NULL;
  size_t sz = ((nbytes + alignment - 1) / alignment) * alignment;
  if (posix_memalign(&p, alignment, sz) != 0) {
    return NULL;
  }
  return p;
}

static inline void tq_init(TaskQueue* q, u32 cap_hint) {
  u32 cap = tq_next_pow2(cap_hint);
  q->cap  = (size_t)cap;
  q->mask = (size_t)cap - 1u;
  q->buf  = (u32*)tq_aligned_alloc(128, sizeof(u32) * (size_t)cap);
  if (!q->buf) abort();
  atomic_store_explicit(&q->top.v, 0, memory_order_relaxed);
  atomic_store_explicit(&q->bot.v, 0, memory_order_relaxed);
}

static inline void tq_free(TaskQueue* q) {
  if (q->buf) free(q->buf);
  q->buf = NULL;
  q->cap = q->mask = 0u;
}

static inline u8 tq_push(TaskQueue* q, u32 v) {
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  if (b - t >= q->cap) {
    return 0;
  }
  q->buf[b & q->mask] = v;
  atomic_store_explicit(&q->bot.v, b + 1, memory_order_release);
  return 1;
}

static inline u8 tq_pop(TaskQueue* q, u32* out) {
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_relaxed);
  if (b == 0) return 0;
  size_t b1 = b - 1;
  atomic_store_explicit(&q->bot.v, b1, memory_order_release);
  atomic_thread_fence(memory_order_acq_rel);

  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  if (t <= b1) {
    u32 x = q->buf[b1 & q->mask];
    if (t == b1) {
      size_t expected = t;
      if (!atomic_compare_exchange_strong_explicit(
            &q->top.v, &expected, t + 1,
            memory_order_acq_rel, memory_order_acquire)) {
        atomic_store_explicit(&q->bot.v, t + 1, memory_order_release);
        return 0;
      }
      atomic_store_explicit(&q->bot.v, t + 1, memory_order_release);
    }
    *out = x;
    return 1;
  } else {
    atomic_store_explicit(&q->bot.v, t, memory_order_release);
    return 0;
  }
}

static inline u8 tq_steal(TaskQueue* q, u32* out) {
  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_acquire);
  if (t >= b) {
    return 0;
  }
  u32 x = q->buf[t & q->mask];
  size_t expected = t;
  if (atomic_compare_exchange_strong_explicit(
        &q->top.v, &expected, t + 1,
        memory_order_acq_rel, memory_order_acquire)) {
    *out = x;
    return 1;
  }
  return 0;
}

typedef struct __attribute__((aligned(64))) {
  TaskQueue dq;
} NormalWorker;

typedef struct {
  NormalWorker W[MAX_THREADS];
  u32          n;
  _Atomic u64  pending;
} NormalCtx;

typedef struct { NormalCtx* C; u32 tid; } NormalArg;

static inline void nq_inc(_Atomic u64* p) {
  atomic_fetch_add_explicit(p, 1, memory_order_relaxed);
}

static inline void nq_dec(_Atomic u64* p) {
  atomic_fetch_sub_explicit(p, 1, memory_order_release);
}

static inline void enqueue_front(NormalCtx* C, u32 tid, u32 child_loc) {
  if (tq_push(&C->W[tid].dq, child_loc)) {
    nq_inc(&C->pending);
  }
}

static inline void normal_seq_loc(NormalCtx* C, u32 tid, u32 loc);
static inline void normal_par_at_go(NormalCtx* C, u32 tid, u32 loc);

static inline void normal_par_norm_dup(NormalCtx* C, u32 tid, u32 dup_loc) {
  if (dup_loc == 0) return;
  Term cell = heap_load_shared(dup_loc);
  if (cell == 0 || term_sub_get(cell)) return;
  Term taken = heap_take_shared(dup_loc);
  if (taken == 0) return;
  if (term_sub_get(taken)) {
    heap_store_shared(dup_loc, taken);
    return;
  }
  u32 root = heap_alloc(1);
  HEAP[root] = taken;
  normal_par_at_go(C, tid, root);
  heap_store_shared(dup_loc, HEAP[root]);
}

static inline void normal_seq_loc(NormalCtx* C, u32 tid, u32 loc) {
  for (;;) {
    Term t = wnf(HEAP[loc]);
    HEAP[loc] = t;
    u8 tag = term_tag(t);

    if (tag == VAR) {
      return;
    }
    if (tag == DP0 || tag == DP1) {
      normal_par_norm_dup(C, tid, term_val(t));
      return;
    }
    if (tag == LAM) {
      loc = term_val(t);
      continue;
    }
    u32 ar = term_arity(t);
    if (ar == 0) {
      return;
    }
    u32 base = term_val(t);
    for (u32 i = 1; i < ar; ++i) {
      normal_seq_loc(C, tid, base + i);
    }
    loc = base + 0;
  }
}

static inline void normal_par_at_go(NormalCtx* C, u32 tid, u32 loc) {
  for (;;) {
    Term t = wnf(HEAP[loc]);
    HEAP[loc] = t;
    u8 tag = term_tag(t);

    if (tag == VAR) {
      return;
    }
    if (tag == DP0 || tag == DP1) {
      normal_par_norm_dup(C, tid, term_val(t));
      return;
    }
    if (tag == LAM) {
      loc = term_val(t);
      continue;
    }
    u32 ar = term_arity(t);
    if (ar == 0) {
      return;
    }
    u32 base = term_val(t);
    for (u32 i = ar; i > 1; --i) {
      enqueue_front(C, tid, base + (i - 1));
    }
    loc = base + 0;
  }
}

static inline u32 normal_par_rng_step(u32 x) {
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  return x;
}

static void* normal_par_worker(void* ap) {
  NormalArg* A = (NormalArg*)ap;
  NormalCtx* C = A->C;
  u32 me = A->tid;

  thread_set_qos();
  wnf_set_tid(me);

  u32 r = 0x9E3779B9u ^ me;

  for (;;) {
    u32 loc;
    if (tq_pop(&C->W[me].dq, &loc)) {
      normal_par_at_go(C, me, loc);
      nq_dec(&C->pending);
      continue;
    }

    u8 stolen = 0;
    u32 n = C->n;
    u32 start = (me + 1 + (r & 7u)) % n;
    r = normal_par_rng_step(r);

    for (u32 k = 0; k < n - 1; ++k) {
      u32 vic = (start + k) % n;
      if (vic == me) continue;
      if (tq_steal(&C->W[vic].dq, &loc)) {
        normal_par_at_go(C, me, loc);
        nq_dec(&C->pending);
        stolen = 1;
        break;
      }
    }

    if (stolen) continue;

    if (atomic_load_explicit(&C->pending, memory_order_acquire) == 0) break;

    cpu_relax();
  }

  wnf_itrs_flush();
  return NULL;
}

fn Term snf_par(Term term) {
  u32 root_loc = heap_alloc(1);
  HEAP[root_loc] = term;

  NormalCtx C;
  u32 n = thread_get_count();
  if (n == 0) n = 1;
  if (n > MAX_THREADS) n = MAX_THREADS;

  C.n = n;
  atomic_store_explicit(&C.pending, 0, memory_order_relaxed);
  for (u32 i = 0; i < n; ++i) {
    tq_init(&C.W[i].dq, 1u << 18);
  }

  if (tq_push(&C.W[0].dq, root_loc)) {
    atomic_store_explicit(&C.pending, 1, memory_order_relaxed);
  }

  heap_bank_flush();

  pthread_t tids[MAX_THREADS];
  NormalArg args[MAX_THREADS];
  for (u32 i = 1; i < n; ++i) {
    args[i].C = &C;
    args[i].tid = i;
    pthread_create(&tids[i], NULL, normal_par_worker, &args[i]);
  }

  args[0].C = &C;
  args[0].tid = 0;
  normal_par_worker(&args[0]);

  for (u32 i = 1; i < n; ++i) {
    pthread_join(tids[i], NULL);
  }

  for (u32 i = 0; i < n; ++i) {
    tq_free(&C.W[i].dq);
  }

  return HEAP[root_loc];
}
