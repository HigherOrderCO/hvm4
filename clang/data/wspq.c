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
// - Single-threaded mode uses a 3-bucket queue (bot/mid/top) for legacy order.
// - Steal prefers lower-key work and can be restricted to shallower buckets.
//
// Notes
// - Tasks are u64 values; key is an 8-bit hint.
// - Not a general multi-producer queue: each worker pushes to its own bank.
// - wsq buffers are fixed size; push spins if a bucket is temporarily full.

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

// Sequential ring capacity (log2) used when only one worker is active.
#ifndef WSPQ_SEQ_BUFSIZE_LOG2
#define WSPQ_SEQ_BUFSIZE_LOG2 23u
#endif

// Sequential ring buffer storing key/task pairs.
typedef struct {
  u32  head;
  u32  size;
  u32  cap;
  u32  mask;
  u64 *task;
  u8  *key;
} WspqSeqBuf;

// Sequential 3-bucket queue state (bot/mid/top).
typedef struct {
  WspqSeqBuf top;
  WspqSeqBuf mid;
  WspqSeqBuf bot;
  u8         max_key;
  u8         has_key;
} WspqSeq;

// Initialize a sequential ring buffer with 2^cap_log2 slots.
static inline bool wspq_seq_buf_init(WspqSeqBuf *b, u32 cap_log2) {
  b->head = 0;
  b->size = 0;
  b->cap  = 1u << cap_log2;
  b->mask = b->cap - 1u;
  b->task = (u64 *)malloc((size_t)b->cap * sizeof(u64));
  b->key  = (u8 *)malloc((size_t)b->cap * sizeof(u8));
  if (!b->task || !b->key) {
    free(b->task);
    free(b->key);
    b->task = NULL;
    b->key  = NULL;
    b->cap  = 0;
    b->mask = 0;
    return false;
  }
  return true;
}

// Release the sequential ring buffer storage.
static inline void wspq_seq_buf_free(WspqSeqBuf *b) {
  if (b->task) {
    free(b->task);
    b->task = NULL;
  }
  if (b->key) {
    free(b->key);
    b->key  = NULL;
  }
  b->head = 0;
  b->size = 0;
  b->cap  = 0;
  b->mask = 0;
}

// Reset a sequential ring buffer without freeing.
static inline void wspq_seq_buf_clear(WspqSeqBuf *b) {
  b->head = 0;
  b->size = 0;
}

// Try to push into a sequential ring buffer; returns false on overflow.
static inline bool wspq_seq_buf_try_push(WspqSeqBuf *b, u8 key, u64 task) {
  if (b->size == b->cap) {
    return false;
  }
  u32 tail = (b->head + b->size) & b->mask;
  b->task[tail] = task;
  b->key[tail]  = key;
  b->size += 1;
  return true;
}

// Pop from the head (FIFO); returns false if empty.
static inline bool wspq_seq_buf_pop(WspqSeqBuf *b, u8 *key, u64 *task) {
  if (b->size == 0) {
    return false;
  }
  *task = b->task[b->head & b->mask];
  *key = b->key[b->head & b->mask];
  b->head = (b->head + 1) & b->mask;
  b->size -= 1;
  return true;
}

// Pop from the tail (LIFO); returns false if empty.
static inline bool wspq_seq_buf_pop_back(WspqSeqBuf *b, u8 *key, u64 *task) {
  if (b->size == 0) {
    return false;
  }
  u32 idx = (b->head + b->size - 1) & b->mask;
  *task = b->task[idx];
  *key = b->key[idx];
  b->size -= 1;
  return true;
}

// Copy ring contents from src to dst, preserving order.
static inline void wspq_seq_buf_ring_copy(WspqSeqBuf *dst, u32 dpos, const WspqSeqBuf *src, u32 spos, u32 len) {
  while (len > 0) {
    u32 drem = dst->cap - (dpos & dst->mask);
    u32 srem = src->cap - (spos & src->mask);
    u32 chunk = len;
    if (chunk > drem) {
      chunk = drem;
    }
    if (chunk > srem) {
      chunk = srem;
    }
    memcpy(&dst->task[dpos & dst->mask],
           &src->task[spos & src->mask],
           chunk * sizeof(u64));
    memcpy(&dst->key[dpos & dst->mask],
           &src->key[spos & src->mask],
           chunk * sizeof(u8));
    dpos += chunk;
    spos += chunk;
    len -= chunk;
  }
}

// Append all elements from src to dst (FIFO order), empties src.
static inline void wspq_seq_buf_append_all(WspqSeqBuf *dst, WspqSeqBuf *src) {
  if (src->size == 0) {
    return;
  }
  if (dst->size + src->size > dst->cap) {
    fprintf(stderr, "wspq: overflow in append\n");
    exit(1);
  }
  u32 dst_tail = dst->head + dst->size;
  wspq_seq_buf_ring_copy(dst, dst_tail, src, src->head, src->size);
  dst->size += src->size;
  wspq_seq_buf_clear(src);
}

// Prepend all elements from src to the front of dst, empties src.
static inline void wspq_seq_buf_prepend_all(WspqSeqBuf *dst, WspqSeqBuf *src) {
  if (src->size == 0) {
    return;
  }
  if (dst->size + src->size > dst->cap) {
    fprintf(stderr, "wspq: overflow in prepend\n");
    exit(1);
  }
  u32 new_head = (dst->head - src->size) & dst->mask;
  wspq_seq_buf_ring_copy(dst, new_head, src, src->head, src->size);
  dst->head = new_head;
  dst->size += src->size;
  wspq_seq_buf_clear(src);
}

// Initialize the sequential 3-bucket queue.
static inline bool wspq_seq_init(WspqSeq *q) {
  if (!wspq_seq_buf_init(&q->top, WSPQ_SEQ_BUFSIZE_LOG2)) {
    return false;
  }
  if (!wspq_seq_buf_init(&q->mid, WSPQ_SEQ_BUFSIZE_LOG2)) {
    wspq_seq_buf_free(&q->top);
    return false;
  }
  if (!wspq_seq_buf_init(&q->bot, WSPQ_SEQ_BUFSIZE_LOG2)) {
    wspq_seq_buf_free(&q->top);
    wspq_seq_buf_free(&q->mid);
    return false;
  }
  q->max_key = 0;
  q->has_key = 0;
  return true;
}

// Free the sequential queue buffers.
static inline void wspq_seq_free(WspqSeq *q) {
  wspq_seq_buf_free(&q->top);
  wspq_seq_buf_free(&q->mid);
  wspq_seq_buf_free(&q->bot);
  q->max_key = 0;
  q->has_key = 0;
}

// Slide the sequential window up by one key.
static inline void wspq_seq_slide_up(WspqSeq *q) {
  WspqSeqBuf old_top = q->top;
  WspqSeqBuf old_mid = q->mid;
  WspqSeqBuf old_bot = q->bot;

  if (old_bot.size <= old_mid.size) {
    // Prepend bot into mid: [bot][mid]
    wspq_seq_buf_prepend_all(&old_mid, &old_bot);
    q->top = old_bot;  // empty, becomes new top
    q->mid = old_top;
    q->bot = old_mid;
  } else {
    // Append mid into bot: [bot][mid]
    wspq_seq_buf_append_all(&old_bot, &old_mid);
    q->top = old_mid;  // empty, becomes new top
    q->mid = old_top;
    q->bot = old_bot;
  }
  q->max_key = q->max_key + 1;
}

// Try to push into the sequential queue; returns false on overflow.
static inline bool wspq_seq_try_push(WspqSeq *q, u8 key, u64 task) {
  u8 k = key & 63u;

  if (!q->has_key) {
    q->max_key = k;
    q->has_key = 1;
    return wspq_seq_buf_try_push(&q->top, k, task);
  }

  int d = (int)k - (int)q->max_key;
  if (d <= -2) {
    return wspq_seq_buf_try_push(&q->bot, k, task);
  }
  if (d == -1) {
    return wspq_seq_buf_try_push(&q->mid, k, task);
  }
  if (d == 0) {
    return wspq_seq_buf_try_push(&q->top, k, task);
  }

  for (int i = 0; i < d; i++) {
    wspq_seq_slide_up(q);
  }
  return wspq_seq_buf_try_push(&q->top, k, task);
}

// Push into the sequential queue; aborts on overflow.
static inline void wspq_seq_push(WspqSeq *q, u8 key, u64 task) {
  if (!wspq_seq_try_push(q, key, task)) {
    fprintf(stderr, "wspq: buffer overflow\n");
    exit(1);
  }
}

// Pop the next sequential task by key ordering.
static inline bool wspq_seq_pop(WspqSeq *q, u8 *key, u64 *task) {
  if (q->bot.size > 0) {
    return wspq_seq_buf_pop(&q->bot, key, task);
  }
  if (q->mid.size > 0) {
    return wspq_seq_buf_pop_back(&q->mid, key, task);
  }
  if (q->top.size > 0) {
    return wspq_seq_buf_pop(&q->top, key, task);
  }
  return false;
}

// Per-worker bank of key deques plus a non-empty bucket mask.
typedef struct __attribute__((aligned(256))) {
  WsDeque q[WSPQ_BRACKETS];
  _Atomic u64 nonempty;
} WspqBank;

// Work-stealing key queue state for all workers.
typedef struct {
  WspqBank bank[MAX_THREADS];
  WspqSeq  seq;
  u32      n;
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
  if (nthreads <= 1) {
    return wspq_seq_init(&ws->seq);
  }

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
  if (ws->n <= 1) {
    wspq_seq_free(&ws->seq);
    return;
  }
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
  if (ws->n <= 1) {
    wspq_seq_push(&ws->seq, key, task);
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
  if (ws->n <= 1) {
    return wspq_seq_pop(&ws->seq, key, task);
  }
  u64 m = atomic_load_explicit(&ws->bank[tid].nonempty, memory_order_relaxed);
  if (m == 0ull) {
    return false;
  }
  while (m) {
    u32 b = wspq_lsb64(m);
    u64 x = 0;
    if (wsq_pop(&ws->bank[tid].q[b], &x)) {
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
