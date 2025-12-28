// data/wspq.c - work-stealing key queue built on wsq buckets.
//
// Context
// - Used by eval_collapse for parallel CNF enumeration.
// - Lower numeric keys are popped first.
//
// Design
// - Key "key" is bucketed by (key >> WSPQ_KEY_SHIFT).
// - A per-worker bitmask tracks which buckets are non-empty.
// - Local pop takes the lowest-index non-empty bucket (best key).
// - Single-threaded pop uses FIFO order within a bucket for determinism.
// - Steal prefers lower-key work and can be restricted to shallower buckets.
//
// Notes
// - Tasks are u64 values; key is an 8-bit hint.
// - Not a general multi-producer queue: each worker pushes to its own bank.
// - wsq buffers are fixed size; push spins if a bucket is temporarily full.

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>

// Number of key buckets (must be <= 64 for the bitmask).
#ifndef WSPQ_BRACKETS
#define WSPQ_BRACKETS 64u
#endif

// Key right shift to map key -> bucket index.
#ifndef WSPQ_KEY_SHIFT
#define WSPQ_KEY_SHIFT 0u
#endif

// Per-bucket deque capacity (log2).
#ifndef WSPQ_CAP_POW2
#define WSPQ_CAP_POW2 21u
#endif

// Number of victim attempts per steal call.
#ifndef WSPQ_STEAL_ATTEMPTS
#define WSPQ_STEAL_ATTEMPTS 2u
#endif

// Per-worker bank of key deques plus a non-empty bucket mask.
typedef struct __attribute__((aligned(256))) {
  WsDeque q[WSPQ_BRACKETS];
  _Atomic u64 nonempty;
} WspqBank;

// Work-stealing key queue state for all workers.
typedef struct {
  WspqBank bank[MAX_THREADS];
  u32 n;
} Wspq;

// Return index of least-significant set bit (undefined for m == 0).
static inline u32 wspq_lsb64(u64 m) {
  return (u32)__builtin_ctzll(m);
}

// Mark a bucket as non-empty in the owner's mask.
static inline void wspq_mask_set(Wspq *ws, u32 tid, u32 b) {
  atomic_fetch_or_explicit(&ws->bank[tid].nonempty, (1ull << b), memory_order_relaxed);
}

// Clear a bucket in the owner's mask (used after observing it empty).
static inline void wspq_mask_clear_owner(Wspq *ws, u32 tid, u32 b) {
  atomic_fetch_and_explicit(&ws->bank[tid].nonempty, ~(1ull << b), memory_order_relaxed);
}

// Map a key value to a bucket index.
static inline u8 wspq_key_bucket(u32 key) {
  u32 bucket = key >> WSPQ_KEY_SHIFT;
  if (bucket >= WSPQ_BRACKETS) {
    return (u8)(WSPQ_BRACKETS - 1u);
  }
  return (u8)bucket;
}

// Initialize all per-worker bucket queues.
static inline bool wspq_init(Wspq *ws, u32 nthreads) {
  ws->n = nthreads;

  for (u32 t = 0; t < nthreads; ++t) {
    atomic_store_explicit(&ws->bank[t].nonempty, 0ull, memory_order_relaxed);
    for (u32 b = 0; b < WSPQ_BRACKETS; ++b) {
      if (!wsq_init(&ws->bank[t].q[b], WSPQ_CAP_POW2)) {
        for (u32 t2 = 0; t2 <= t; ++t2) {
          u32 bmax = WSPQ_BRACKETS;
          if (t2 == t) {
            bmax = b;
          }
          for (u32 b2 = 0; b2 < bmax; ++b2) {
            wsq_free(&ws->bank[t2].q[b2]);
          }
        }
        return false;
      }
    }
  }
  return true;
}

// Free all per-worker bucket queues.
static inline void wspq_free(Wspq *ws) {
  for (u32 t = 0; t < ws->n; ++t) {
    for (u32 b = 0; b < WSPQ_BRACKETS; ++b) {
      wsq_free(&ws->bank[t].q[b]);
    }
  }
}

// Push a task into the owner's bucket; spins until the bucket accepts it.
static inline void wspq_push(Wspq *ws, u32 tid, u8 key, u64 task) {
  if (task == 0) {
    return;
  }
  u8 bucket = wspq_key_bucket(key);
  WsDeque *q = &ws->bank[tid].q[bucket];
  while (!wsq_push(q, task)) {
    cpu_relax();
  }
  wspq_mask_set(ws, tid, bucket);
}

// Pop the best-key local task; returns false if none are available.
static inline bool wspq_pop(Wspq *ws, u32 tid, u8 *key, u64 *task) {
  u64 m = atomic_load_explicit(&ws->bank[tid].nonempty, memory_order_relaxed);
  if (m == 0ull) {
    return false;
  }
  bool fifo = (ws->n == 1);
  while (m) {
    u32 b = wspq_lsb64(m);
    u64 x = 0;
    if (fifo ? wsq_steal(&ws->bank[tid].q[b], &x) : wsq_pop(&ws->bank[tid].q[b], &x)) {
      *key = (u8)(b << WSPQ_KEY_SHIFT);
      *task = x;
      return true;
    }
    wspq_mask_clear_owner(ws, tid, b);
    m &= (m - 1ull);
  }
  return false;
}

// Steal up to max_batch tasks from other workers, favoring lower keys.
static inline u32 wspq_steal_some(
  Wspq *ws,
  u32     me,
  u32     max_batch,
  bool    restrict_deeper,
  u32    *cursor
) {
  u32 n = ws->n;
  if (n <= 1) {
    return 0u;
  }

  u64 my_mask = atomic_load_explicit(&ws->bank[me].nonempty, memory_order_relaxed);
  u32 my_min = WSPQ_BRACKETS;
  if (my_mask != 0ull) {
    my_min = wspq_lsb64(my_mask);
  }

  u32 b_limit = WSPQ_BRACKETS;
  if (restrict_deeper && my_min < b_limit) {
    b_limit = my_min;
  }

  u64 allowed_mask = ~0ull;
  if (b_limit < WSPQ_BRACKETS) {
    allowed_mask = (1ull << b_limit) - 1ull;
  }

  u32 start = *cursor;
  for (u32 k = 0; k < WSPQ_STEAL_ATTEMPTS; ++k) {
    u32 v = (start + k) % n;
    if (v == me) {
      continue;
    }
    u64 nm = atomic_load_explicit(&ws->bank[v].nonempty, memory_order_relaxed);
    nm &= allowed_mask;
    if (nm == 0ull) {
      continue;
    }
    u32 b = wspq_lsb64(nm);
    u32 got = 0;
    u64 x = 0;
    if (!wsq_steal(&ws->bank[v].q[b], &x)) {
      continue;
    }
    wspq_push(ws, me, (u8)(b << WSPQ_KEY_SHIFT), x);
    got += 1u;
    for (; got < max_batch; ++got) {
      if (!wsq_steal(&ws->bank[v].q[b], &x)) {
        break;
      }
      wspq_push(ws, me, (u8)(b << WSPQ_KEY_SHIFT), x);
    }
    *cursor = v + 1;
    return got;
  }
  *cursor = start + WSPQ_STEAL_ATTEMPTS;
  return 0u;
}
