# Parallelism in hvm4-old (legacy runtime)

This document summarizes how the old HVM4 runtime implements parallel
normalization and collapse. It is written by reading the implementation in
`../hvm4-old` and describes the architecture, data structures, scheduling, and
key operational details.

## High-level overview

The old runtime exposes two parallel modes:

- **Parallel full normalization**: `normal_par(Term)` in
  `../hvm4-old/src/normal/par/_main_.h`.
- **Parallel collapse (PQS readback)**: `print_collapsed_par` in
  `../hvm4-old/src/collapse/par/_main_.h`.

Both modes are **thread-count aware** and rely on **banked, per-thread state**
(heaps, WNF stacks, stats, printing registries, nickname generators) with a
single global arena for heap storage. Each worker thread sets a TLS thread id
and uses only its own banked storage to avoid cross-thread contention and the
need for allocator atomics.

## Entry points and configuration

Key integration points in the old runtime:

- CLI flags are wired in `../hvm4-old/src/main.c`:
  - `-T<N>` sets a requested thread count (clamped to `MAX_THREADS`).
  - `HVM4_THREADS` env var is a fallback if `-T` is absent.
  - `-d` enables debug prints for collapse workers.
- `normal_par_set(N)` in `../hvm4-old/src/normal/par/_main_.h` calls
  `thread_set_count(N)` and `heap_recompute_banks()`.
- The single public wrapper `hvm_set_tc()` in
  `../hvm4-old/src/hvm.h` does the same.
- `wnf_set_tid(tid)` must be called by each worker thread to bind TLS state.

Default behavior in the CLI:

- If thread count is `1`, it uses sequential normalization and collapse.
- If thread count is `> 1`, it uses `normal_par` and `print_collapsed_par`.

## Thread-count and banked state

### Thread count and bounds

- `../hvm4-old/src/thread/_main_.h` provides
  `thread_set_count` / `thread_get_count`.
- `MAX_THREADS` defaults to 64 (compile-time cap for all banks).

### Heap banking

- `../hvm4-old/src/heap/_main_.h` allocates a **single monolithic arena** via
  `mmap` (default 32 GiB), then partitions it into **contiguous per-thread
  banks**.
- Each thread uses a disjoint bank slice with a local bump pointer, so heap
  allocation is lock-free and requires no atomics.
- `heap_recompute_banks()` recomputes the partition; **it must be called after
  updating the thread count** and before allocations.

### WNF, printing, and nickname banks

Banked state is indexed by the TLS thread id (`wnf_tid()`), which is set per
worker using `wnf_set_tid(tid)`.

- WNF:
  - `../hvm4-old/src/wnf/_main_.h` defines `_Thread_local` TLS id and per-thread
    stacks/counters (`WNF_BANKS`, `WNF_ITRS_BANKS`).
  - `wnf_stack_init()` lazily allocates a per-thread WNF stack (2^32 entries,
    `mmap` with `MAP_NORESERVE`, malloc fallback).
- Printing and nicknames:
  - `../hvm4-old/src/print/_main_.h` stores per-thread duplicate registries and
    unique-name tables to make rendering deterministic per thread.
  - `../hvm4-old/src/nick/_main_.h` keeps per-thread nickname generators.

### Atomic heap cell access

- `../hvm4-old/src/term/_main_.h` uses `__atomic_load_n`, `__atomic_store_n`, and
  `__atomic_exchange_n` for `get_at`, `set_at`, and `take_at`.
- `take_at` is an atomic exchange to ensure a single consumer of a heap slot.
  This avoids tearing and reduces races between workers touching the same cell.

## Parallel full normalization (`normal_par`)

### Files and key types

- Implementation: `../hvm4-old/src/normal/par/_main_.h`.
- Worker structure:
  - `NormalCtx` has one `TaskQueue` per worker plus a global atomic `pending`.
  - Each task is a **heap location** (`Val`, stored as `u32`) to normalize.

### Task queue

Each worker owns a private **deque** (`TaskQueue`) implemented with a mutex:

- Fixed-size ring buffer (`cap` = next power-of-two of the hint, default 2^18).
- Single mutex protects `head` and `tail`; both owner and stealers take it.
- API:
  - `tq_push` / `tq_push_front`: owner or anyone can enqueue.
  - `tq_pop`: owner pops from tail.
  - `tq_steal`: thieves steal from head.

This is a **simple locked deque**, not a lock-free Chase-Lev deque.

### Scheduler and termination

- `pending` counts tasks enqueued but not yet popped.
- Every successful enqueue increments `pending`.
- After a worker finishes a task, it decrements `pending`.
- Workers exit when they cannot steal and `pending == 0`.
- When idle but pending > 0, workers call `sched_yield()`.

### Work splitting strategy

The core routine is `normal_par_at_go(C, tid, loc)`:

1. Reduce the term at `loc` to WNF via `wnf_at(loc)`.
2. Inspect the tag and act as follows:

- **VAR / DP0 / DP1**: writes `Era()` to the location and returns.
- **LAM**: creates a substitution marker in the body, anchors the body, and
  continues on that body location (depth-first). Once finished, writes the
  normalized body back into the lam.
- **APP**: **enqueues the child at `val + 0`** and continues on `val + 1`.
  This means the current worker keeps the right child while exposing the left
  child to other workers.
- **All other n-ary nodes**: enqueues children `val + (arity-1)` down to
  `val + 1`, then continues with `val + 0`.

This yields a **depth-first traversal** along one branch while enqueueing
siblings for parallelism. The per-APP asymmetry (enqueue child 0, continue with
child 1) is intentional and encoded directly in the code.

### Work stealing

Worker threads run `normal_par_worker`:

- Pop from own deque (`tq_pop`); if successful, process and decrement `pending`.
- If empty, try to steal from other workers (`tq_steal`).
- Steal order uses a per-worker xorshift RNG to vary the starting victim and
  avoid synchronization hotspots.

## Parallel collapse (`print_collapsed_par`)

Parallel collapse implements a **parallel version of PQS readback**.
It never calls full `normal_par` (even when thread count is 1) to avoid
exploring the entire space before the output limit is reached.

### Files and key types

- Implementation: `../hvm4-old/src/collapse/par/_main_.h`.
- Work queue primitive: `../hvm4-old/src/data/wsq.h` (Chase-Lev WSQ).
- Each thread has a **bank of priority queues** (`COLL_WS_BRACKETS`, default 64).

### Work representation

Tasks are `(priority, loc)` pairs, where:

- `loc` is a heap location to process.
- `priority` is a bracket index; lower is higher priority.
- `INC` nodes reduce priority by 1 per layer.

The goal is to approximate the sequential PQS traversal order while allowing
parallel consumption.

### Data structures

- `CollCtx` holds:
  - `printed`: number of printed leaves (atomic).
  - `stop`: global flag to stop all workers (atomic).
  - `pending`: global task count (atomic, signed).
  - `bank[t]`: per-thread array of WSQ deques, plus a `nonempty` bitmask.
- Each per-thread bank keeps a **64-bit mask** of which priority brackets are
  non-empty; only the owner clears bits to avoid lost updates.

### Work queues and stealing

Each bracket is a **Chase-Lev work-stealing deque** with padded indices:

- Owner pushes/pops at `bot`.
- Thieves steal from `top` using CAS.
- `coll_ws_push`, `coll_ws_pop`, and `coll_ws_steal` are in `wsq.h`.

Stealing strategy (`coll_ws_steal_some`):

- Prefer victims with **lower-priority (smaller) brackets**.
- Optionally restrict stealing to brackets **strictly below** the worker's
  current local minimum bracket if it still has local work.
- Steal in small batches (`COLL_WS_STEAL_BATCH`, default 8).
- Run stealing periodically every `COLL_WS_STEAL_PERIOD` iterations.

### Processing a task

`coll_process_loc` does:

1. If `stop` is set, returns immediately.
2. Peel `INC` wrappers while decreasing priority (clamped at 0).
3. If the term is `SUP` or `BKF`, push both children at priority + 1.
4. Otherwise, **print the leaf** after sequential normalization:
   `fprint_term_ln(out, normal_seq(tm))`.
5. Update `printed` and set `stop` if `max_lines` is reached.

### Termination

- Each worker maintains a local `pend_local` delta to reduce global atomic
  traffic.
- `pending` is updated in batches (release/acquire).
- Workers exit when `pending == 0` or when `stop` is set.

## Work-stealing queues (Chase-Lev WSQ)

The `../hvm4-old/src/data/wsq.h` implementation is a minimal Chase-Lev deque:

- `top` and `bot` are atomic size_t with cache-line padding.
- Ring buffer is power-of-two, aligned to cache-line size.
- Owner operations are mostly relaxed + release stores.
- Thief steals use CAS on `top` with acquire/release semantics.
- Pop/steal indicate whether the deque became empty to help maintain masks.

## Concurrency and correctness notes

- **Per-thread TLS id is mandatory**: every worker must call `wnf_set_tid` to
  select the correct banks (heap, WNF stack, print state, nicknames).
- **Heap partitioning is static**: a single thread can exhaust its bank even if
  total heap has space. This is a known risk in parallel modes; it influenced
  the design choice in `print_collapsed_par` to avoid `normal_par`.
- **Heap cell access is atomic**: `take_at` is an atomic exchange to prevent
  multiple workers from taking the same cell; `set_at` and `get_at` use relaxed
  atomics.
- **Pending is the global termination gate** in both parallel modes; tasks are
  counted when enqueued and decremented after processing.
- **WNF stacks are per-thread** and lazily allocated; the old runtime assumes
  each worker calls `wnf`/`wnf_at`, which invokes `wnf_stack_init` for that
  worker id.

## Why `wnf_at` is thread-safe (proof sketch)

This is the core concurrency story in the old runtime. The heap is shared by
all threads, yet `wnf_at` can run in parallel because reduction is linear,
local, and uses an explicit "dup protocol" to serialize access to the only
shared cells.

### Core invariants

- **Linearity**: a heap cell has at most one incoming pointer, except dup slots,
  which are pointed to by exactly two nodes (`DP0` and `DP1`). See
  `../hvm4-old/docs/linearity.md` and the heap model in
  `../hvm4-old/docs/HVM.md`.
- **Atomic heap access**: `get_at`, `set_at`, and `take_at` are atomic
  operations in `../hvm4-old/src/term/_main_.h`. `take_at` is an atomic exchange
  that transfers ownership of a cell to the caller.
- **Local rewrites**: every WNF rule touches only the redex and a bounded set of
  adjacent cells (the child slots it `take_at`s and the locations it `set_at`s).
  See the interaction implementations under `../hvm4-old/src/wnf/*.h`.
- **Dup protocol**: duplication is explicit and uses the SUB bit. The first
  `DP0/DP1` that enters a dup slot claims it with `take_at`, computes the two
  copies, then writes the twin back as `as_sub(...)` for the other side. This is
  implemented in `../hvm4-old/src/wnf/_main_.h` (enter/apply for DP nodes) and
  `../hvm4-old/src/wnf/dup_*.h`.

### Proof sketch (safety + linearizability)

1. **Ownership transfer**: `wnf_at(loc)` starts by `take_at(loc)`, which
   atomically removes the root term from the heap. From that point on, the
   thread owns that root and any child slots it later `take_at`s.
2. **Disjointness for non-dups**: by linearity, every non-dup child slot is
   referenced by exactly one parent. If one thread has taken the parent, no
   other thread can reach that child through a different path. So concurrent
   `wnf_at` calls on disjoint roots cannot race on non-dup cells.
3. **Dup slots are serialized**: a dup slot is the only shared cell reachable
   from two different roots (via `DP0` and `DP1`). The first DP that reaches it
   executes the linearization point: `take_at(dup_loc)`. It then computes the
   duplication rule and writes the twin back as `as_sub(...)` in that same slot.
   The other DP, when later evaluated, sees the SUB bit and returns the stored
   value without touching the original shared cell. This guarantees that each
   dup slot is consumed exactly once, even with parallel evaluation.
4. **Atomicity + locality imply thread safety**: all heap mutations are atomic
   and each WNF step is local, so any interleaving of two `wnf_at` executions is
   equivalent to some sequential order as long as linearity holds. This is the
   standard interaction-net argument: reductions on disjoint active pairs
   commute, and the only shared case (dups) is serialized by the SUB protocol.

### Important assumption

This safety argument relies on *valid linear terms*: no heap cell is aliased
without an explicit dup. If linearity is violated, `take_at` can observe `0`
and the runtime aborts (`ERROR: TAKE_AT=0`), which is treated as a bug rather
than a recoverable race.

## Summary of key components (old repo)

- Thread count:
  - `../hvm4-old/src/thread/_main_.h`
  - `../hvm4-old/src/hvm.h` (`hvm_set_tc`)
- TLS worker id:
  - `../hvm4-old/src/wnf/_main_.h` (`wnf_set_tid`, `_Thread_local` id)
- Banked heap allocator:
  - `../hvm4-old/src/heap/_main_.h`
- Parallel normalization:
  - `../hvm4-old/src/normal/par/_main_.h`
- Parallel collapse:
  - `../hvm4-old/src/collapse/par/_main_.h`
- Work-stealing deque:
  - `../hvm4-old/src/data/wsq.h`
- CLI integration:
  - `../hvm4-old/src/main.c`
- Threaded example:
  - `../hvm4-old/examples/thread_test.c`
