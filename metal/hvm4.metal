// HVM4 Runtime - Metal GPU Implementation
// =========================================
//
// Multi-threaded GPU evaluator with CUDA-style warp-coalesced memory layout.
//
// Term Pointer Layout (64-bit)
// ----------------------------
// | SUB  (1 bit)   ::= marks heap slot as containing a substitution
// | TAG  (7 bits)  ::= constructor variant (APP, LAM, SUP, etc.)
// | EXT  (16 bits) ::= dup label, ctr name, or ref name
// | VAL  (40 bits) ::= heap address or unboxed value

#include <metal_stdlib>
using namespace metal;

typedef uint64_t Term;

struct Copy { Term k0; Term k1; };

// Tags
constant uint8_t NAM = 0;
constant uint8_t DRY = 1;
constant uint8_t REF = 2;
constant uint8_t ALO = 3;
constant uint8_t ERA = 4;
constant uint8_t CO0 = 5;
constant uint8_t CO1 = 6;
constant uint8_t VAR = 7;
constant uint8_t LAM = 8;
constant uint8_t APP = 9;
constant uint8_t SUP = 10;
constant uint8_t DUP = 11;
constant uint8_t MAT = 12;
constant uint8_t CTR = 13;
constant uint8_t CTR_MAX_ARI = 16;

// Bit Layout
constant uint64_t SUB_SHIFT = 63;
constant uint64_t TAG_SHIFT = 56;
constant uint64_t EXT_SHIFT = 40;
constant uint64_t SUB_MASK = 0x1;
constant uint64_t TAG_MASK = 0x7F;
constant uint64_t EXT_MASK = 0xFFFF;
constant uint64_t VAL_MASK = 0xFFFFFFFFFF;

// Term Helpers
inline Term new_term(uint8_t sub, uint8_t tag, uint32_t ext, uint64_t val) {
  return (uint64_t(sub) << SUB_SHIFT) | (uint64_t(tag & uint8_t(TAG_MASK)) << TAG_SHIFT)
       | (uint64_t(ext & uint32_t(EXT_MASK)) << EXT_SHIFT) | (val & VAL_MASK);
}
inline uint8_t sub_of(Term t) { return uint8_t((t >> SUB_SHIFT) & SUB_MASK); }
inline uint8_t tag(Term t) { return uint8_t((t >> TAG_SHIFT) & TAG_MASK); }
inline uint32_t ext(Term t) { return uint32_t((t >> EXT_SHIFT) & EXT_MASK); }
inline uint64_t val(Term t) { return t & VAL_MASK; }

inline uint32_t arity_of(Term t) {
  uint8_t tg = tag(t);
  if (tg == LAM) return 1;
  if (tg == APP || tg == SUP || tg == DUP || tg == MAT || tg == DRY) return 2;
  if (tg >= CTR && tg <= CTR + CTR_MAX_ARI) return uint32_t(tg - CTR);
  return 0;
}

inline Term mark_sub(Term t) { return t | (uint64_t(1) << SUB_SHIFT); }
inline Term clear_sub(Term t) { return t & ~(SUB_MASK << SUB_SHIFT); }

// Simple Term Constructors
inline Term Var(uint32_t loc) { return new_term(0, VAR, 0, loc); }
inline Term Era() { return new_term(0, ERA, 0, 0); }
inline Term Co0(uint32_t lab, uint32_t loc) { return new_term(0, CO0, lab, loc); }
inline Term Co1(uint32_t lab, uint32_t loc) { return new_term(0, CO1, lab, loc); }
inline Term Nam(uint32_t nam) { return new_term(0, NAM, 0, nam); }
inline Copy clone_at(uint32_t loc, uint32_t lab) { return Copy{ Co0(lab, loc), Co1(lab, loc) }; }

// Heap Accessor
// Terms store physical indices directly. Access is just base[idx].
// Coalesced access comes from allocation: thread N allocates at positions
// that are N mod 32 within each warp's slice.
struct Heap {
  device Term* base;

  inline Term get(uint32_t idx) const {
    return base[idx];
  }

  inline void set(uint32_t idx, Term val) const {
    base[idx] = val;
  }
};

// Runtime State
struct State {
  uint32_t alloc;      // Next logical slot to allocate (0, 1, 2, ...)
  uint64_t itrs;       // Interaction counter
  uint32_t heap_base;  // Physical base: warp_base + lane_id
  uint32_t simd_width; // Warp width (32)
};

// Allocate `size` slots, return physical index of first slot.
// Physical layout for coalesced access:
//   logical slot 0 -> heap_base + 0 * simd_width = heap_base
//   logical slot 1 -> heap_base + 1 * simd_width = heap_base + 32
//   logical slot k -> heap_base + k * simd_width
inline uint32_t heap_alloc(thread State& st, uint32_t size) {
  uint32_t logical = st.alloc;
  st.alloc += size;
  return st.heap_base + logical * st.simd_width;
}

// Substitution Helpers
inline void subst_var(const thread Heap& heap, uint32_t loc, Term v) {
  heap.set(loc, mark_sub(v));
}

inline Term subst_cop(const thread Heap& heap, uint8_t side, uint32_t loc, Term r0, Term r1) {
  heap.set(loc, mark_sub(side == 0 ? r1 : r0));
  return side == 0 ? r0 : r1;
}

// Term Constructors with Heap
// Note: heap_alloc returns physical indices. For multi-slot nodes, consecutive
// logical slots are simd_width apart in physical memory.
inline Term Lam(const thread Heap& heap, thread State& st, Term bod) {
  uint32_t loc = heap_alloc(st, 1);
  heap.set(loc, bod);
  return new_term(0, LAM, 0, loc);
}

inline Term App(const thread Heap& heap, thread State& st, Term fun, Term arg) {
  uint32_t loc = heap_alloc(st, 2);
  heap.set(loc, fun);
  heap.set(loc + st.simd_width, arg);
  return new_term(0, APP, 0, loc);
}

inline Term Sup(const thread Heap& heap, thread State& st, uint32_t lab, Term tm0, Term tm1) {
  uint32_t loc = heap_alloc(st, 2);
  heap.set(loc, tm0);
  heap.set(loc + st.simd_width, tm1);
  return new_term(0, SUP, lab, loc);
}

inline Term Dry(const thread Heap& heap, thread State& st, Term tm0, Term tm1) {
  uint32_t loc = heap_alloc(st, 2);
  heap.set(loc, tm0);
  heap.set(loc + st.simd_width, tm1);
  return new_term(0, DRY, 0, loc);
}

inline Term Dup(const thread Heap& heap, thread State& st, uint32_t lab, Term v, Term bod) {
  uint32_t loc = heap_alloc(st, 2);
  heap.set(loc, v);
  heap.set(loc + st.simd_width, bod);
  return new_term(0, DUP, lab, loc);
}

inline Copy clone(const thread Heap& heap, thread State& st, uint32_t lab, Term v) {
  uint32_t loc = heap_alloc(st, 1);
  heap.set(loc, v);
  return clone_at(loc, lab);
}

// Beta Interactions
inline Term app_era(thread State& st) { st.itrs++; return Era(); }

inline Term app_stuck(const thread Heap& heap, thread State& st, Term fun, Term arg) {
  st.itrs++;
  return Dry(heap, st, fun, arg);
}

inline Term app_lam(const thread Heap& heap, thread State& st, Term lam, Term arg) {
  st.itrs++;
  uint32_t loc = val(lam);
  Term body = heap.get(loc);
  subst_var(heap, loc, arg);
  return body;
}

inline Term app_sup(const thread Heap& heap, thread State& st, Term app, Term sup) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t app_loc = val(app), sup_loc = val(sup), lab = ext(sup);
  Term arg = heap.get(app_loc + sw), tm1 = heap.get(sup_loc + sw);
  uint32_t loc = heap_alloc(st, 3);
  heap.set(loc + 2*sw, arg);
  Copy D = clone_at(loc + 2*sw, lab);
  heap.set(sup_loc + sw, D.k0);
  Term ap0 = new_term(0, APP, 0, sup_loc);
  heap.set(loc, tm1);
  heap.set(loc + sw, D.k1);
  Term ap1 = new_term(0, APP, 0, loc);
  heap.set(app_loc, ap0);
  heap.set(app_loc + sw, ap1);
  return new_term(0, SUP, lab, app_loc);
}

// Match Interactions
inline Term app_mat_sup(const thread Heap& heap, thread State& st, Term mat, Term sup) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t lab = ext(sup);
  Copy M = clone(heap, st, lab, mat);
  uint32_t loc = val(sup);
  Term a = heap.get(loc), b = heap.get(loc + sw);
  return Sup(heap, st, lab, App(heap, st, M.k0, a), App(heap, st, M.k1, b));
}

inline Term app_mat_ctr(const thread Heap& heap, thread State& st, Term mat, Term ctr) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t ari = uint32_t(tag(ctr) - CTR);
  if (ext(mat) == ext(ctr)) {
    Term res = heap.get(val(mat));
    for (uint32_t i = 0; i < ari; i++) res = App(heap, st, res, heap.get(val(ctr) + i * sw));
    return res;
  }
  return App(heap, st, heap.get(val(mat) + sw), ctr);
}

// Dup Interactions
inline Term dup_lam(const thread Heap& heap, thread State& st, uint32_t lab, uint32_t loc, uint8_t side, Term lam) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t lam_loc = val(lam);
  Term bod = heap.get(lam_loc);
  uint32_t a = heap_alloc(st, 5);
  heap.set(a + 4*sw, bod);
  Copy B = clone_at(a + 4*sw, lab);
  heap.set(a + 2*sw, Var(a));
  heap.set(a + 3*sw, Var(a + sw));
  Term su = new_term(0, SUP, lab, a + 2*sw);
  heap.set(a, B.k0);
  heap.set(a + sw, B.k1);
  Term l0 = new_term(0, LAM, 0, a), l1 = new_term(0, LAM, 0, a + sw);
  subst_var(heap, lam_loc, su);
  return subst_cop(heap, side, loc, l0, l1);
}

inline Term dup_sup(const thread Heap& heap, thread State& st, uint32_t lab, uint32_t loc, uint8_t side, Term sup) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t sup_loc = val(sup), sup_lab = ext(sup);
  if (lab == sup_lab) {
    Term tm0 = heap.get(sup_loc), tm1 = heap.get(sup_loc + sw);
    return subst_cop(heap, side, loc, tm0, tm1);
  }
  Copy A = clone_at(sup_loc, lab), B = clone_at(sup_loc + sw, lab);
  uint32_t a = heap_alloc(st, 4);
  heap.set(a, A.k0); heap.set(a + sw, B.k0);
  heap.set(a + 2*sw, A.k1); heap.set(a + 3*sw, B.k1);
  Term s0 = new_term(0, SUP, sup_lab, a), s1 = new_term(0, SUP, sup_lab, a + 2*sw);
  return subst_cop(heap, side, loc, s0, s1);
}

inline Term dup_node(const thread Heap& heap, thread State& st, uint32_t lab, uint32_t loc, uint8_t side, Term term) {
  st.itrs++;
  uint32_t sw = st.simd_width;
  uint32_t ari = arity_of(term);
  if (ari == 0) { subst_var(heap, loc, term); return term; }
  uint32_t t_loc = val(term), t_ext = ext(term);
  uint8_t t_tag = tag(term);

  if (ari == 1) {
    Copy A = clone(heap, st, lab, heap.get(t_loc));
    uint32_t loc0 = heap_alloc(st, 1), loc1 = heap_alloc(st, 1);
    heap.set(loc0, A.k0); heap.set(loc1, A.k1);
    return subst_cop(heap, side, loc, new_term(0, t_tag, t_ext, loc0), new_term(0, t_tag, t_ext, loc1));
  }
  if (ari == 2) {
    Copy A = clone(heap, st, lab, heap.get(t_loc)), B = clone(heap, st, lab, heap.get(t_loc + sw));
    uint32_t loc0 = heap_alloc(st, 2), loc1 = heap_alloc(st, 2);
    heap.set(loc0, A.k0); heap.set(loc0 + sw, B.k0);
    heap.set(loc1, A.k1); heap.set(loc1 + sw, B.k1);
    return subst_cop(heap, side, loc, new_term(0, t_tag, t_ext, loc0), new_term(0, t_tag, t_ext, loc1));
  }
  Copy copies[16];
  for (uint32_t i = 0; i < ari; i++) copies[i] = clone(heap, st, lab, heap.get(t_loc + i * sw));
  uint32_t loc0 = heap_alloc(st, ari), loc1 = heap_alloc(st, ari);
  for (uint32_t i = 0; i < ari; i++) { heap.set(loc0 + i * sw, copies[i].k0); heap.set(loc1 + i * sw, copies[i].k1); }
  return subst_cop(heap, side, loc, new_term(0, t_tag, t_ext, loc0), new_term(0, t_tag, t_ext, loc1));
}

// Alloc Helpers
// Note: bind entries pack two 32-bit values into 64 bits as (loc << 32) | tail
constant uint64_t PAIR_LO_MASK = 0xFFFFFFFF;

inline uint32_t bind_at(const thread Heap& heap, uint32_t ls, uint32_t idx) {
  for (uint32_t i = 0; i < idx && ls != 0; i++) ls = uint32_t(heap.get(ls) & PAIR_LO_MASK);
  return (ls != 0) ? uint32_t(heap.get(ls) >> 32) : 0;
}

inline uint32_t make_bind(const thread Heap& heap, thread State& st, uint32_t tail, uint32_t loc) {
  uint32_t entry = heap_alloc(st, 1);
  heap.set(entry, (uint64_t(loc) << 32) | uint64_t(tail));
  return entry;
}

inline Term make_alo(const thread Heap& heap, thread State& st, uint32_t ls_loc, uint32_t tm_loc) {
  uint32_t loc = heap_alloc(st, 1);
  heap.set(loc, (uint64_t(ls_loc) << 32) | uint64_t(tm_loc));
  return new_term(0, ALO, 0, loc);
}

// Alloc Interactions
inline Term alo_var(const thread Heap& heap, uint32_t ls_loc, uint32_t idx) {
  uint32_t bind = bind_at(heap, ls_loc, idx);
  return bind != 0 ? Var(bind) : new_term(0, VAR, 0, idx);
}

inline Term alo_cop(const thread Heap& heap, uint32_t ls_loc, uint32_t idx, uint32_t lab, uint8_t side) {
  uint32_t bind = bind_at(heap, ls_loc, idx);
  uint8_t tg = side == 0 ? CO0 : CO1;
  return bind != 0 ? new_term(0, tg, lab, bind) : new_term(0, tg, lab, idx);
}

inline Term alo_lam(const thread Heap& heap, thread State& st, uint32_t ls_loc, uint32_t book_body_loc) {
  uint32_t lam_body = heap_alloc(st, 1);
  uint32_t new_bind = make_bind(heap, st, ls_loc, lam_body);
  heap.set(lam_body, make_alo(heap, st, new_bind, book_body_loc));
  return new_term(0, LAM, 0, lam_body);
}

inline Term alo_dup(const thread Heap& heap, thread State& st, uint32_t ls_loc, uint32_t book_loc, uint32_t lab) {
  uint32_t dup_val = heap_alloc(st, 1);
  uint32_t new_bind = make_bind(heap, st, ls_loc, dup_val);
  heap.set(dup_val, make_alo(heap, st, ls_loc, book_loc));
  // book_loc + 1 is in the book (contiguous), so +1 is correct
  return Dup(heap, st, lab, make_alo(heap, st, ls_loc, book_loc), make_alo(heap, st, new_bind, book_loc + 1));
}

inline Term alo_node(const thread Heap& heap, thread State& st, uint32_t ls_loc, uint32_t loc, uint8_t tg, uint32_t ex, uint32_t ari) {
  uint32_t sw = st.simd_width;
  uint32_t new_loc = heap_alloc(st, ari);
  // loc + i is in the book (contiguous), so +i is correct for book access
  for (uint32_t i = 0; i < ari; i++) heap.set(new_loc + i * sw, make_alo(heap, st, ls_loc, loc + i));
  return new_term(0, tg, ex, new_loc);
}

// WNF (Weak Normal Form)
constant uint32_t WNF_LOOP_LIMIT = 500000;

Term wnf(const thread Heap& heap, device Term* wnf_stack, device uint32_t* book, thread State& st, Term term, thread uint32_t& max_wnf, thread uint32_t& wnf_loops) {
  uint32_t s_pos = 0;
  Term next = term;
  bool reducing = true;
  uint32_t sw = st.simd_width;

  while (wnf_loops < WNF_LOOP_LIMIT) {
    wnf_loops++;
    if (reducing) {
      uint8_t tg = tag(next);
      uint32_t vl = val(next);

      if (tg == VAR) {
        Term h = heap.get(vl);
        if (sub_of(h)) { next = clear_sub(h); continue; }
        reducing = false; continue;
      }
      if (tg == CO0 || tg == CO1) {
        Term h = heap.get(vl);
        if (sub_of(h)) { next = clear_sub(h); continue; }
        wnf_stack[s_pos++] = next;
        if (s_pos > max_wnf) max_wnf = s_pos;
        next = h;
        continue;
      }
      if (tg == APP) {
        wnf_stack[s_pos++] = next;
        if (s_pos > max_wnf) max_wnf = s_pos;
        next = heap.get(vl);
        continue;
      }
      if (tg == DUP) {
        next = heap.get(vl + sw);
        continue;
      }
      if (tg == REF) {
        uint32_t book_loc = book[ext(next)];
        if (book_loc != 0) { next = make_alo(heap, st, 0, book_loc); continue; }
        reducing = false; continue;
      }
      if (tg == ALO) {
        uint64_t pair = heap.get(vl);
        uint32_t tm_loc = uint32_t(pair & PAIR_LO_MASK);
        uint32_t ls_loc = uint32_t(pair >> 32);
        Term bk = heap.get(tm_loc);
        uint8_t bt = tag(bk);
        uint32_t bv = val(bk);
        uint32_t be = ext(bk);
        if (bt == VAR) { next = alo_var(heap, ls_loc, bv); continue; }
        if (bt == CO0) { next = alo_cop(heap, ls_loc, bv, be, 0); continue; }
        if (bt == CO1) { next = alo_cop(heap, ls_loc, bv, be, 1); continue; }
        if (bt == LAM) { next = alo_lam(heap, st, ls_loc, bv); continue; }
        if (bt == APP) { next = alo_node(heap, st, ls_loc, bv, APP, be, 2); continue; }
        if (bt == SUP) { next = alo_node(heap, st, ls_loc, bv, SUP, be, 2); continue; }
        if (bt == MAT) { next = alo_node(heap, st, ls_loc, bv, MAT, be, 2); continue; }
        if (bt == DRY) { next = alo_node(heap, st, ls_loc, bv, DRY, be, 2); continue; }
        if (bt == DUP) { next = alo_dup(heap, st, ls_loc, bv, be); continue; }
        if (bt == REF || bt == NAM || bt == ERA) { next = bk; continue; }
        if (bt >= CTR && bt <= CTR + CTR_MAX_ARI) { next = alo_node(heap, st, ls_loc, bv, bt, be, bt - CTR); continue; }
        reducing = false; continue;
      }
      // Default: term is in WHNF
      reducing = false; continue;
    }

    // Unwinding phase
    if (s_pos == 0) return next;

    Term frame = wnf_stack[--s_pos];
    uint8_t ft = tag(frame);
    uint8_t wt = tag(next);

    if (ft == APP) {
      Term arg = heap.get(val(frame) + sw);
      if (wt == ERA) { next = Era(); st.itrs++; continue; }
      if (wt == NAM || wt == DRY) { next = app_stuck(heap, st, next, arg); continue; }
      if (wt == LAM) { next = app_lam(heap, st, next, arg); reducing = true; continue; }
      if (wt == SUP) { next = app_sup(heap, st, frame, next); reducing = true; continue; }
      if (wt == MAT) { wnf_stack[s_pos++] = next; if (s_pos > max_wnf) max_wnf = s_pos; next = arg; reducing = true; continue; }
      next = App(heap, st, next, arg);
      continue;
    }

    if (ft == MAT) {
      if (wt == ERA) { next = Era(); st.itrs++; continue; }
      if (wt == SUP) { next = app_mat_sup(heap, st, frame, next); reducing = true; continue; }
      if (wt >= CTR && wt <= CTR + CTR_MAX_ARI) { next = app_mat_ctr(heap, st, frame, next); reducing = true; continue; }
      next = App(heap, st, frame, next);
      continue;
    }

    // ft == CO0 || ft == CO1
    {
      uint8_t side = (ft == CO0) ? 0 : 1;
      uint32_t loc = val(frame);
      uint32_t lab = ext(frame);
      if (wt == LAM) { next = dup_lam(heap, st, lab, loc, side, next); reducing = true; continue; }
      if (wt == SUP) { next = dup_sup(heap, st, lab, loc, side, next); reducing = true; continue; }
      if (wt == ERA || wt == NAM) { next = dup_node(heap, st, lab, loc, side, next); continue; }
      if (wt == MAT || wt == DRY) { next = dup_node(heap, st, lab, loc, side, next); reducing = true; continue; }
      if (wt >= CTR && wt <= CTR + CTR_MAX_ARI) { next = dup_node(heap, st, lab, loc, side, next); reducing = true; continue; }
      // Stuck: create co-references
      uint32_t new_loc = heap_alloc(st, 1);
      heap.set(new_loc, next);
      subst_var(heap, loc, new_term(0, side == 0 ? CO1 : CO0, lab, new_loc));
      next = new_term(0, side == 0 ? CO0 : CO1, lab, new_loc);
      continue;
    }
  }
  // Loop limit reached - return current term (incomplete reduction)
  return next;
}

// SNF (Strong Normal Form)
struct SNFFrame { Term term; uint32_t write_loc; uint32_t depth; uint8_t phase; };
constant uint32_t SNF_ROOT = 0xFFFFFFFF;

Term snf(const thread Heap& heap, device Term* wnf_stack, device SNFFrame* snf_stack, device uint32_t* book, thread State& st, Term term, thread uint32_t& max_wnf, thread uint32_t& max_snf, thread uint32_t& wnf_loops, thread uint32_t& snf_loops) {
  uint32_t snf_pos = 0;
  snf_stack[snf_pos++] = SNFFrame{term, SNF_ROOT, 0, 0};
  if (snf_pos > max_snf) max_snf = snf_pos;
  Term result = 0;
  uint32_t sw = st.simd_width;

  while (snf_pos > 0) {
    snf_loops++;
    SNFFrame frame = snf_stack[--snf_pos];
    if (frame.phase == 0) {
      Term t = wnf(heap, wnf_stack, book, st, frame.term, max_wnf, wnf_loops);
      uint32_t ari = arity_of(t);
      if (ari == 0) {
        if (frame.write_loc != SNF_ROOT) heap.set(frame.write_loc, t);
        else result = t;
      } else {
        uint32_t loc = val(t);
        snf_stack[snf_pos++] = SNFFrame{t, frame.write_loc, frame.depth, 1};
        if (tag(t) == LAM) {
          Term body = heap.get(loc);
          subst_var(heap, loc, Nam(frame.depth + 1));
          snf_stack[snf_pos++] = SNFFrame{body, loc, frame.depth + 1, 0};
        } else {
          for (int32_t i = int32_t(ari) - 1; i >= 0; i--)
            snf_stack[snf_pos++] = SNFFrame{heap.get(loc + uint32_t(i) * sw), loc + uint32_t(i) * sw, frame.depth, 0};
        }
        if (snf_pos > max_snf) max_snf = snf_pos;
      }
    } else {
      if (frame.write_loc != SNF_ROOT) heap.set(frame.write_loc, frame.term);
      else result = frame.term;
    }
  }
  return result;
}

// GPU Kernel
kernel void hvm_run(
  device Term*     global_heap   [[buffer(0)]],
  device Term*     global_wnf    [[buffer(1)]],
  device SNFFrame* global_snf    [[buffer(2)]],
  device uint32_t* book          [[buffer(3)]],
  device uint64_t* itrs_out      [[buffer(4)]],
  device Term*     outputs       [[buffer(5)]],
  constant uint32_t& book_size   [[buffer(6)]],
  constant uint32_t& main_ref    [[buffer(7)]],
  constant uint32_t& num_threads [[buffer(8)]],
  constant uint64_t& heap_per_thr  [[buffer(9)]],
  constant uint64_t& wnf_per_thr   [[buffer(10)]],
  constant uint64_t& snf_per_thr   [[buffer(11)]],
  constant uint32_t& simd_width    [[buffer(12)]],
  uint tid [[thread_position_in_grid]]
) {
  if (tid >= num_threads) return;

  uint32_t warp_id = tid / simd_width;
  uint32_t lane_id = tid % simd_width;
  uint64_t warp_slice_size = heap_per_thr * simd_width;
  // Physical base for this thread's heap allocation
  // Thread allocates at: heap_base, heap_base + simd_width, heap_base + 2*simd_width, ...
  uint32_t heap_base = book_size + uint32_t(warp_id * warp_slice_size) + lane_id;

  Heap heap;
  heap.base = global_heap;

  device Term* wnf_stack = global_wnf + uint64_t(tid) * wnf_per_thr;
  device SNFFrame* snf_stack = global_snf + uint64_t(tid) * snf_per_thr;

  State st;
  st.alloc = 0;  // Logical allocation counter starts at 0
  st.itrs = 0;
  st.heap_base = heap_base;
  st.simd_width = simd_width;

  uint32_t max_wnf = 0;
  uint32_t max_snf = 0;
  uint32_t wnf_loops = 0;
  uint32_t snf_loops = 0;

  Term main_term = new_term(0, REF, main_ref, 0);
  Term result = snf(heap, wnf_stack, snf_stack, book, st, main_term, max_wnf, max_snf, wnf_loops, snf_loops);

  itrs_out[tid] = st.itrs;
  // Pack loop counts: wnf_loops (32 bits) | snf_loops (32 bits)
  outputs[tid] = uint64_t(wnf_loops) | (uint64_t(snf_loops) << 32);
}
