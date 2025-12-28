// data/pq.c - sliding 3-bucket key queue (top/mid/bot).
//
// Context
// - Used by eval_collapse to enumerate collapse branches in ascending key order.
// - Lower numeric keys are popped first.
// - INC decreases key (earlier), SUP increases key (later).
//
// Design
// - Three ring buffers partition the key range:
//   top: highest key value observed (numerically largest key)
//   mid: one below top (top - 1)
//   bot: all keys <= top - 2
// - Push slides the window upward when a new higher key arrives.
// - Pop processes lower numeric key first: bot (FIFO), then mid (LIFO),
//   then top (FIFO). This favors deeper branches later while keeping locality.
//
// Notes
// - Key is clamped to 0..63 in pq_try_push.
// - The queue is single-threaded; external synchronization is required.

#include <stdbool.h>

// Default ring capacity (log2) for each bucket buffer.
#define PQ_BUFSIZE_LOG2 23u

// Queue item with a key and a heap location.
typedef struct {
  u8  key;  // 0..63 - lower is popped earlier
  u32 loc;  // heap location
} PqItem;

// Ring buffer storage for a single key bucket.
typedef struct {
  u32    head;  // dequeue cursor (mod cap)
  u32    size;  // current length
  u32    cap;   // ring capacity (pow2)
  u32    mask;  // cap - 1
  PqItem *data;  // ring storage (FIFO)
} PqBuf;

// Three-bucket key queue state.
typedef struct {
  PqBuf top;      // highest key value group
  PqBuf mid;      // (top - 1)
  PqBuf bot;      // (<= top - 2)
  u8    max_key;  // highest key value observed
  u8    has_key;  // whether max_key has been initialized
} Pq;

// Initialize a ring buffer with 2^cap_log2 slots.
fn void pq_buf_init(PqBuf *b, u32 cap_log2) {
  b->head = 0;
  b->size = 0;
  b->cap  = 1u << cap_log2;
  b->mask = b->cap - 1u;
  b->data = (PqItem*)malloc((size_t)b->cap * sizeof(PqItem));
  if (!b->data) {
    fprintf(stderr, "pq: out of memory\n");
    exit(1);
  }
}

// Free ring buffer storage.
fn void pq_buf_free(PqBuf *b) {
  if (b->data) {
    free(b->data);
    b->data = NULL;
  }
  b->head = 0;
  b->size = 0;
  b->cap  = 0;
  b->mask = 0;
}

// Reset ring buffer contents without freeing.
fn void pq_buf_clear(PqBuf *b) {
  b->head = 0;
  b->size = 0;
}

// Try to push into a ring buffer; returns false on overflow.
static inline bool pq_buf_try_push(PqBuf *b, PqItem it) {
  if (b->size == b->cap) {
    return false;
  }
  u32 tail = (b->head + b->size) & b->mask;
  b->data[tail] = it;
  b->size += 1;
  return true;
}

// Pop from head (FIFO); returns 0 if empty.
fn u8 pq_buf_pop(PqBuf *b, PqItem *out) {
  if (b->size == 0) {
    return 0;
  }
  *out = b->data[b->head & b->mask];
  b->head = (b->head + 1) & b->mask;
  b->size -= 1;
  return 1;
}

// Pop from tail (LIFO); used for the mid bucket.
fn u8 pq_buf_pop_back(PqBuf *b, PqItem *out) {
  if (b->size == 0) {
    return 0;
  }
  u32 idx = (b->head + b->size - 1) & b->mask;
  *out = b->data[idx];
  b->size -= 1;
  return 1;
}

// Copy ring buffer elements from src to dst, preserving order.
fn void pq_buf_ring_copy(PqBuf *dst, u32 dpos, const PqBuf *src, u32 spos, u32 len) {
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
    memcpy(&dst->data[dpos & dst->mask],
           &src->data[spos & src->mask],
           chunk * sizeof(PqItem));
    dpos += chunk;
    spos += chunk;
    len -= chunk;
  }
}

// Append all elements from src to dst (FIFO order), empties src.
fn void pq_buf_append_all(PqBuf *dst, PqBuf *src) {
  if (src->size == 0) {
    return;
  }
  if (dst->size + src->size > dst->cap) {
    fprintf(stderr, "pq: overflow in append\n");
    exit(1);
  }
  u32 dst_tail = dst->head + dst->size;
  pq_buf_ring_copy(dst, dst_tail, src, src->head, src->size);
  dst->size += src->size;
  pq_buf_clear(src);
}

// Prepend all elements from src to front of dst, empties src.
fn void pq_buf_prepend_all(PqBuf *dst, PqBuf *src) {
  if (src->size == 0) {
    return;
  }
  if (dst->size + src->size > dst->cap) {
    fprintf(stderr, "pq: overflow in prepend\n");
    exit(1);
  }
  u32 new_head = (dst->head - src->size) & dst->mask;
  pq_buf_ring_copy(dst, new_head, src, src->head, src->size);
  dst->head = new_head;
  dst->size += src->size;
  pq_buf_clear(src);
}

// Initialize the queue with a custom buffer size.
fn void pq_init_cap(Pq *q, u32 cap_log2) {
  pq_buf_init(&q->top, cap_log2);
  pq_buf_init(&q->mid, cap_log2);
  pq_buf_init(&q->bot, cap_log2);
  q->max_key = 0;
  q->has_key = 0;
}

// Initialize the queue with default buffer size.
fn void pq_init(Pq *q) {
  pq_init_cap(q, PQ_BUFSIZE_LOG2);
}

// Free all buckets and reset queue state.
fn void pq_free(Pq *q) {
  pq_buf_free(&q->top);
  pq_buf_free(&q->mid);
  pq_buf_free(&q->bot);
  q->has_key = 0;
}

// Slide the window up by 1 (max_key := max_key + 1).
fn void pq_slide_up(Pq *q) {
  PqBuf old_top = q->top;
  PqBuf old_mid = q->mid;
  PqBuf old_bot = q->bot;

  if (old_bot.size <= old_mid.size) {
    // Prepend bot into mid: [bot][mid]
    pq_buf_prepend_all(&old_mid, &old_bot);
    q->top = old_bot;  // empty, becomes new top
    q->mid = old_top;
    q->bot = old_mid;
  } else {
    // Append mid into bot: [bot][mid]
    pq_buf_append_all(&old_bot, &old_mid);
    q->top = old_mid;  // empty, becomes new top
    q->mid = old_top;
    q->bot = old_bot;
  }
  q->max_key = q->max_key + 1;
}

// Try to push an item; returns false on overflow.
fn bool pq_try_push(Pq *q, PqItem it) {
  u8 k = it.key & 63;  // clamp to 0..63

  if (!q->has_key) {
    q->max_key = k;
    q->has_key = 1;
    return pq_buf_try_push(&q->top, it);
  }

  int d = (int)k - (int)q->max_key;
  if (d <= -2) {
    return pq_buf_try_push(&q->bot, it);
  }
  if (d == -1) {
    return pq_buf_try_push(&q->mid, it);
  }
  if (d == 0) {
    return pq_buf_try_push(&q->top, it);
  }
  // d > 0: slide up until max_key == k
  for (int i = 0; i < d; i++) {
    pq_slide_up(q);
  }
  return pq_buf_try_push(&q->top, it);
}

// Push an item; exit on overflow.
fn void pq_push(Pq *q, PqItem it) {
  if (!pq_try_push(q, it)) {
    fprintf(stderr, "pq: buffer overflow\n");
    exit(1);
  }
}

// Pop the next item by key (bot FIFO, mid LIFO, top FIFO).
fn u8 pq_pop(Pq *q, PqItem *out) {
  if (q->bot.size > 0) {
    return pq_buf_pop(&q->bot, out);
  }
  if (q->mid.size > 0) {
    return pq_buf_pop_back(&q->mid, out);
  }
  if (q->top.size > 0) {
    return pq_buf_pop(&q->top, out);
  }
  return 0;
}

// Return 1 if all buckets are empty.
fn u8 pq_is_empty(Pq *q) {
  return (q->top.size | q->mid.size | q->bot.size) == 0;
}

// Return the total number of queued items.
fn u32 pq_size(const Pq *q) {
  return q->top.size + q->mid.size + q->bot.size;
}
