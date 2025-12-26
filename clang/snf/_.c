// Parallel SNF traversal using work-stealing.
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdbool.h>

#ifndef SNF_WS_CAP_POW2
#define SNF_WS_CAP_POW2 21
#endif

#define SNF_SEEN_INIT (1u << 20)

#define SNF_TASK(loc) ((u64)(loc))
#define SNF_TASK_LOC(task) ((u32)(task))

typedef struct __attribute__((aligned(64))) {
  WsDeque dq;
  U32Set  seen;
} SnfWorker;

typedef struct {
  SnfWorker   W[MAX_THREADS];
  u32         n;
  _Atomic u64 pending;
} SnfCtx;

typedef struct {
  SnfCtx *ctx;
  u32 tid;
} SnfArg;

static inline void snf_pending_inc(_Atomic u64 *pending) {
  atomic_fetch_add_explicit(pending, 1, memory_order_relaxed);
}

static inline void snf_pending_dec(_Atomic u64 *pending) {
  atomic_fetch_sub_explicit(pending, 1, memory_order_release);
}

static inline void snf_par_enqueue(SnfCtx *ctx, SnfWorker *worker, u64 task);

static inline void snf_par_go(SnfCtx *ctx, SnfWorker *worker, u64 task) {
  u32 loc = SNF_TASK_LOC(task);
  if (loc == 0) {
    return;
  }
  if (!u32_set_add(&worker->seen, loc)) {
    return;
  }
  bool parallel = ctx->n > 1;
  for (;;) {
    Term term = wnf_at(loc);
    u8 tag = term_tag(term);
    if (tag == DP0 || tag == DP1) {
      u32 dup_loc = term_val(term);
      if (dup_loc != 0 && !term_sub_get(heap_peek(dup_loc))) {
        if (parallel) {
          snf_par_enqueue(ctx, worker, SNF_TASK(dup_loc));
          return;
        } else {
          if (!u32_set_add(&worker->seen, dup_loc)) {
            return;
          }
          loc = dup_loc;
          continue;
        }
      }
    }

    u32 ari = term_arity(term);
    if (ari == 0) {
      return;
    }
    u32 tloc = term_val(term);
    if (parallel) {
      if (tag == DRY) {
        snf_par_enqueue(ctx, worker, SNF_TASK(tloc + 1));
        snf_par_enqueue(ctx, worker, SNF_TASK(tloc));
        return;
      }
      if (tag == LAM) {
        snf_par_enqueue(ctx, worker, SNF_TASK(tloc));
        return;
      }
      for (u32 i = 0; i < ari; i++) {
        snf_par_enqueue(ctx, worker, SNF_TASK(tloc + i));
      }
      return;
    }
    if (tag == LAM) {
      if (!u32_set_add(&worker->seen, tloc)) {
        return;
      }
      loc = tloc;
      continue;
    }
    if (tag == DRY) {
      snf_par_enqueue(ctx, worker, SNF_TASK(tloc + 1));
      if (!u32_set_add(&worker->seen, tloc)) {
        return;
      }
      loc = tloc;
      continue;
    }
    for (u32 i = ari; i > 1; i--) {
      snf_par_enqueue(ctx, worker, SNF_TASK(tloc + (i - 1)));
    }
    if (!u32_set_add(&worker->seen, tloc)) {
      return;
    }
    loc = tloc;
  }
}

static inline void snf_par_enqueue(SnfCtx *ctx, SnfWorker *worker, u64 task) {
  if (SNF_TASK_LOC(task) == 0) {
    return;
  }
  if (wsq_push(&worker->dq, task)) {
    snf_pending_inc(&ctx->pending);
  } else {
    snf_par_go(ctx, worker, task);
  }
}

static void *snf_par_worker(void *arg) {
  SnfArg *A = (SnfArg *)arg;
  SnfCtx *ctx = A->ctx;
  u32 me = A->tid;
  SnfWorker *worker = &ctx->W[me];

  wnf_set_tid(me);

  u32 r = 0x9E3779B9u ^ me;

  u32 idle = 0;
  for (;;) {
    u64 task;

    if (wsq_pop(&worker->dq, &task)) {
      snf_par_go(ctx, worker, task);
      snf_pending_dec(&ctx->pending);
      idle = 0;
      continue;
    }

    bool stolen = false;
    u32 n = ctx->n;
    u32 start = (me + 1 + (r & 7)) % n;
    r ^= r << 13;
    r ^= r >> 17;
    r ^= r << 5;

    for (u32 k = 0; k < n - 1; k++) {
      u32 vic = (start + k) % n;
      if (vic == me) {
        continue;
      }
      if (wsq_steal(&ctx->W[vic].dq, &task)) {
        snf_par_go(ctx, worker, task);
        snf_pending_dec(&ctx->pending);
        stolen = true;
        idle = 0;
        break;
      }
    }

    if (stolen) {
      continue;
    }

    if (atomic_load_explicit(&ctx->pending, memory_order_acquire) == 0) {
      break;
    }

    if (idle < 1024) {
      cpu_relax();
      idle++;
    } else {
      sched_yield();
      idle = 0;
    }
  }

  wnf_itrs_flush(me);
  return NULL;
}

static inline Term snf_par(Term term) {
  wnf_set_tid(0);

  u32 root_loc = (u32)heap_alloc(1);
  heap_set(root_loc, term);

  SnfCtx ctx;

  u32 n = thread_get_count();
  if (n == 0) {
    n = 1;
  }
  if (n > MAX_THREADS) {
    n = MAX_THREADS;
  }
  ctx.n = n;
  atomic_store_explicit(&ctx.pending, 0, memory_order_relaxed);
  for (u32 i = 0; i < n; i++) {
    if (!wsq_init(&ctx.W[i].dq, SNF_WS_CAP_POW2)) {
      fprintf(stderr, "snf: queue allocation failed\n");
      exit(1);
    }
    u32_set_init(&ctx.W[i].seen, SNF_SEEN_INIT);
  }

  SnfWorker *worker0 = &ctx.W[0];
  u64 root_task = SNF_TASK(root_loc);
  if (wsq_push(&worker0->dq, root_task)) {
    atomic_store_explicit(&ctx.pending, 1, memory_order_relaxed);
  } else {
    snf_par_go(&ctx, worker0, root_task);
  }

  pthread_t tids[MAX_THREADS];
  SnfArg args[MAX_THREADS];
  for (u32 i = 1; i < n; i++) {
    args[i].ctx = &ctx;
    args[i].tid = i;
    pthread_create(&tids[i], NULL, snf_par_worker, &args[i]);
  }

  SnfArg arg0 = { .ctx = &ctx, .tid = 0 };
  snf_par_worker(&arg0);
  wnf_itrs_flush(0);

  for (u32 i = 1; i < n; i++) {
    pthread_join(tids[i], NULL);
  }

  for (u32 i = 0; i < n; i++) {
    wsq_free(&ctx.W[i].dq);
    u32_set_free(&ctx.W[i].seen);
  }

  return heap_read(root_loc);
}

fn Term snf(Term term) {
  return snf_par(term);
}
