#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

#ifndef WSQ_L1
#define WSQ_L1 128
#endif

typedef struct {
  _Atomic size_t v;
  char _pad[WSQ_L1 - sizeof(_Atomic size_t)];
} WsqIdx;

typedef struct __attribute__((aligned(128))) {
  WsqIdx top;
  WsqIdx bot;
  _Alignas(WSQ_L1) u64 *buf;
  size_t mask;
  size_t cap;
} WsDeque;

static inline void *wsq_aligned_alloc(size_t alignment, size_t nbytes) {
  void *ptr = NULL;
  size_t size = ((nbytes + alignment - 1) / alignment) * alignment;
  int err = posix_memalign(&ptr, alignment, size);
  if (err) {
    return NULL;
  }
  return ptr;
}

static inline int wsq_init(WsDeque *q, u32 capacity_pow2) {
  size_t cap = (size_t)1 << capacity_pow2;
  q->buf = (u64 *)wsq_aligned_alloc(WSQ_L1, cap * sizeof(u64));
  if (!q->buf) {
    return 0;
  }
  q->cap  = cap;
  q->mask = cap - 1;
  atomic_store_explicit(&q->top.v, 0, memory_order_relaxed);
  atomic_store_explicit(&q->bot.v, 0, memory_order_relaxed);
  return 1;
}

static inline void wsq_free(WsDeque *q) {
  if (q && q->buf) {
    free(q->buf);
    q->buf = NULL;
  }
}

static inline int wsq_push(WsDeque *q, u64 x) {
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

static inline int wsq_pop(WsDeque *q, u64 *out) {
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

static inline int wsq_steal(WsDeque *q, u64 *out) {
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
