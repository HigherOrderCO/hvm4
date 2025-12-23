// Parallel SNF using a Chase-Lev work-stealing deque.
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdbool.h>

#ifndef SNF_WS_L1
#define SNF_WS_L1 128
#endif

#ifndef SNF_WS_CAP_POW2
#define SNF_WS_CAP_POW2 18
#endif

typedef struct { _Atomic size_t v; char _pad[SNF_WS_L1 - sizeof(_Atomic size_t)]; } SnfIdx;

typedef struct __attribute__((aligned(128))) {
  SnfIdx top;
  SnfIdx bot;
  _Alignas(SNF_WS_L1) u64 *buf;
  size_t mask;
  size_t cap;
} SnfDeque;

typedef struct __attribute__((aligned(64))) {
  SnfDeque dq;
  SnfSeen  seen;
} SnfWorker;

typedef struct {
  SnfWorker   W[MAX_THREADS];
  u32         n;
  _Atomic u64 pending;
} SnfCtx;

typedef struct { SnfCtx *C; u32 tid; } SnfArg;

static inline u64 snf_task_pack(u32 loc, u32 depth) {
  return ((u64)depth << 32) | (u64)loc;
}

static inline void snf_task_unpack(u64 t, u32 *loc, u32 *depth) {
  *loc = (u32)(t & 0xFFFFFFFFu);
  *depth = (u32)(t >> 32);
}

static inline void *snf_aligned_alloc(size_t alignment, size_t nbytes) {
  void *p = NULL;
  size_t sz = ((nbytes + alignment - 1) / alignment) * alignment;
  int err = posix_memalign(&p, alignment, sz);
  if (err) {
    return NULL;
  }
  return p;
}

static inline int snf_ws_init(SnfDeque *q, u32 capacity_pow2) {
  size_t cap = (size_t)1 << capacity_pow2;
  q->buf = (u64 *)snf_aligned_alloc(SNF_WS_L1, cap * sizeof(u64));
  if (!q->buf) {
    return 0;
  }
  q->cap  = cap;
  q->mask = cap - 1;
  atomic_store_explicit(&q->top.v, 0, memory_order_relaxed);
  atomic_store_explicit(&q->bot.v, 0, memory_order_relaxed);
  return 1;
}

static inline void snf_ws_destroy(SnfDeque *q) {
  if (q && q->buf) {
    free(q->buf);
    q->buf = NULL;
  }
}

static inline int snf_ws_push(SnfDeque *q, u64 x) {
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  if (b - t >= q->cap) {
    return 0;
  }
  __builtin_prefetch(&q->buf[b & q->mask], 1, 1);
  q->buf[b & q->mask] = x;
  atomic_store_explicit(&q->bot.v, b + 1, memory_order_release);
  return 1;
}

static inline int snf_ws_pop(SnfDeque *q, u64 *out) {
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_relaxed);
  if (b == 0) {
    return 0;
  }
  size_t b1 = b - 1;
  __builtin_prefetch(&q->buf[b1 & q->mask], 0, 1);
  atomic_store_explicit(&q->bot.v, b1, memory_order_release);
  atomic_thread_fence(memory_order_acq_rel);

  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  if (t <= b1) {
    u64 x = q->buf[b1 & q->mask];
    if (t == b1) {
      size_t expected = t;
      bool ok = atomic_compare_exchange_strong_explicit(
        &q->top.v,
        &expected,
        t + 1,
        memory_order_acq_rel,
        memory_order_acquire
      );
      if (!ok) {
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

static inline int snf_ws_steal(SnfDeque *q, u64 *out) {
  size_t t = atomic_load_explicit(&q->top.v, memory_order_acquire);
  size_t b = atomic_load_explicit(&q->bot.v, memory_order_acquire);
  if (t >= b) {
    return 0;
  }
  __builtin_prefetch(&q->buf[t & q->mask], 0, 1);
  u64 x = q->buf[t & q->mask];
  size_t expected = t;
  bool ok = atomic_compare_exchange_strong_explicit(
    &q->top.v,
    &expected,
    t + 1,
    memory_order_acq_rel,
    memory_order_acquire
  );
  if (ok) {
    *out = x;
    return 1;
  }
  return 0;
}

static inline void snf_pending_inc(_Atomic u64 *p) {
  atomic_fetch_add_explicit(p, 1, memory_order_relaxed);
}

static inline void snf_pending_dec(_Atomic u64 *p) {
  atomic_fetch_sub_explicit(p, 1, memory_order_release);
}

static inline void snf_par_go(SnfCtx *C, SnfWorker *W, u32 tid, u32 loc, u32 depth);

static inline void snf_par_enqueue(SnfCtx *C, SnfWorker *W, u32 tid, u32 loc, u32 depth) {
  if (loc == 0) {
    return;
  }
  if (snf_ws_push(&W->dq, snf_task_pack(loc, depth))) {
    snf_pending_inc(&C->pending);
  } else {
    snf_par_go(C, W, tid, loc, depth);
  }
}

static inline void snf_par_go(SnfCtx *C, SnfWorker *W, u32 tid, u32 loc, u32 depth) {
  if (loc == 0) {
    return;
  }
  if (!snf_seen_add(&W->seen, loc)) {
    return;
  }
  for (;;) {
    Term term = wnf_at(loc);
    u8 tag = term_tag(term);
    if (tag == DP0 || tag == DP1) {
      u32 dup_loc = term_val(term);
      if (dup_loc != 0 && !term_sub_get(heap_get_raw(dup_loc))) {
        if (!snf_seen_add(&W->seen, dup_loc)) {
          return;
        }
        loc = dup_loc;
        depth = 0;
        continue;
      }
    }

    u32 ari = term_arity(term);
    if (ari == 0) {
      return;
    }
    u32 tloc = term_val(term);
    if (tag == LAM) {
      if (!snf_seen_add(&W->seen, tloc)) {
        return;
      }
      loc = tloc;
      depth++;
      continue;
    }
    if (tag == DRY) {
      snf_par_enqueue(C, W, tid, tloc + 1, depth);
      if (!snf_seen_add(&W->seen, tloc)) {
        return;
      }
      loc = tloc;
      continue;
    }

    for (u32 i = ari; i > 1; i--) {
      snf_par_enqueue(C, W, tid, tloc + (i - 1), depth);
    }
    if (!snf_seen_add(&W->seen, tloc)) {
      return;
    }
    loc = tloc;
  }
}

static void *snf_par_worker(void *ap) {
  SnfArg *A = (SnfArg *)ap;
  SnfCtx *C = A->C;
  u32 me = A->tid;
  SnfWorker *W = &C->W[me];

  wnf_set_tid(me);

  u32 r = 0x9E3779B9u ^ me;

  for (;;) {
    u64 task;

    if (snf_ws_pop(&W->dq, &task)) {
      u32 loc;
      u32 depth;
      snf_task_unpack(task, &loc, &depth);
      snf_par_go(C, W, me, loc, depth);
      snf_pending_dec(&C->pending);
      continue;
    }

    bool stolen = false;
    u32  n = C->n;
    u32  start = (me + 1 + (r & 7)) % n;
    r ^= r << 13;
    r ^= r >> 17;
    r ^= r << 5;

    for (u32 k = 0; k < n - 1; k++) {
      u32 vic = (start + k) % n;
      if (vic == me) {
        continue;
      }
      if (snf_ws_steal(&C->W[vic].dq, &task)) {
        u32 loc;
        u32 depth;
        snf_task_unpack(task, &loc, &depth);
        snf_par_go(C, W, me, loc, depth);
        snf_pending_dec(&C->pending);
        stolen = true;
        break;
      }
    }

    if (stolen) {
      continue;
    }

    if (atomic_load_explicit(&C->pending, memory_order_acquire) == 0) {
      break;
    }

    sched_yield();
  }

  return NULL;
}

fn Term snf_par(Term term, u32 depth, u8 quoted) {
  (void)quoted;

  wnf_set_tid(0);

  u32 root_loc = heap_alloc(1);
  heap_set(root_loc, term);

  SnfCtx C;

  u32 n = thread_get_count();
  if (n == 0) {
    n = 1;
  }
  if (n > MAX_THREADS) {
    n = MAX_THREADS;
  }
  C.n = n;
  atomic_store_explicit(&C.pending, 0, memory_order_relaxed);
  for (u32 i = 0; i < n; i++) {
    if (!snf_ws_init(&C.W[i].dq, SNF_WS_CAP_POW2)) {
      fprintf(stderr, "snf: queue allocation failed\n");
      exit(1);
    }
    snf_seen_init(&C.W[i].seen, SNF_SEEN_INIT);
  }

  SnfWorker *W0 = &C.W[0];
  if (snf_ws_push(&W0->dq, snf_task_pack(root_loc, depth))) {
    atomic_store_explicit(&C.pending, 1, memory_order_relaxed);
  } else {
    snf_par_go(&C, W0, 0, root_loc, depth);
  }

  pthread_t tids[MAX_THREADS];
  SnfArg args[MAX_THREADS];
  for (u32 i = 1; i < n; i++) {
    args[i].C   = &C;
    args[i].tid = i;
    pthread_create(&tids[i], NULL, snf_par_worker, &args[i]);
  }

  SnfArg arg0 = { .C = &C, .tid = 0 };
  snf_par_worker(&arg0);

  for (u32 i = 1; i < n; i++) {
    pthread_join(tids[i], NULL);
  }

  for (u32 i = 0; i < n; i++) {
    snf_ws_destroy(&C.W[i].dq);
    snf_seen_free(&C.W[i].seen);
  }

  return heap_get(root_loc);
}
