// Auto-dup: rewrites a cloned binder with N uses into N-1 nested DUP nodes.
// Example: [x,x,x] becomes !d0&=x; !d1&=d0₁; [d0₀,d1₀,d1₁]
//
// The transformation is purely structural and does not evaluate anything.
// It must preserve binding structure and linearity:
// - Every occurrence of the target ref is replaced by exactly one occurrence
//   of either a BJ0 or BJ1 that belongs to the newly created DUP chain.
// - The chain ensures that the two sides of each DUP are consumed exactly once.
//
// The key correctness invariant is that the chain length matches the number
// of target occurrences in the (already desugared) body. We compute that
// count by traversing the term.
//
// We traverse all children and sum uses. This keeps every occurrence unique
// across the whole term, which is required because SNF will traverse every
// branch (including matcher chains).
//
// Works for both BJV refs (let/lambda bindings) and BJ refs (dup bindings).
// - Target is identified by tag + level (and ext for BJ mode).
// - Outer refs (level > base depth) are shifted by n to account for new dup terms.

fn u32 auto_dup_count_go(u64 loc, u32 lvl, u8 tgt, u32 ext);

fn u32 auto_dup_count_term(Term t, u32 lvl, u8 tgt, u32 ext) {
  u8  tg = term_tag(t);
  u32 vl = term_val(t);

  if (tg == tgt && vl == lvl && (tgt == BJV || term_ext(t) == ext)) {
    return 1;
  }

  u32 ari = term_arity(t);
  if (ari == 0) {
    return 0;
  }

  u32 sum = 0;
  for (u32 i = 0; i < ari; i++) {
    sum += auto_dup_count_go(vl + i, lvl, tgt, ext);
  }
  return sum;
}

fn u32 auto_dup_count_go(u64 loc, u32 lvl, u8 tgt, u32 ext) {
  return auto_dup_count_term(HEAP[loc], lvl, tgt, ext);
}

fn void auto_dup_go(u64 loc, u32 lvl, u32 base, u32 *use, u32 n, u32 lab, u8 tgt, u32 ext) {
  Term t = HEAP[loc];
  u8  tg = term_tag(t);
  u32 vl = term_val(t);

  // Replace target ref with BJ0/BJ1 chain
  if (tg == tgt && vl == lvl && (tgt == BJV || term_ext(t) == ext)) {
    u32 i = (*use)++;
    if (i < n) {
      HEAP[loc] = term_new(0, BJ0, lab + i, base + 1 + i);
    } else {
      HEAP[loc] = term_new(0, BJ1, lab + n - 1, base + n);
    }
    return;
  }

  // Shift outer refs
  if ((tg == BJV || tg == BJ0 || tg == BJ1) && vl > base) {
    HEAP[loc] = term_new(0, tg, term_ext(t), vl + n);
    return;
  }

  // Recurse into children
  switch (tg) {
    case LAM: {
      auto_dup_go(vl, lvl, base, use, n, lab, tgt, ext);
      return;
    }
    case DUP: {
      auto_dup_go(vl + 0, lvl, base, use, n, lab, tgt, ext);
      auto_dup_go(vl + 1, lvl, base, use, n, lab, tgt, ext);
      return;
    }
    default: {
      u32 ari = term_arity(t);
      for (u32 i = 0; i < ari; i++) {
        auto_dup_go(vl + i, lvl, base, use, n, lab, tgt, ext);
      }
    }
  }
}

fn Term parse_auto_dup(Term body, u32 lvl, u32 base, u8 tgt, u32 ext) {
  u32 uses = auto_dup_count_term(body, lvl, tgt, ext);
  if (uses <= 1) {
    return body;
  }

  u32 n   = uses - 1;
  u32 lab = PARSE_FRESH_LAB;
  PARSE_FRESH_LAB += n;

  // Walk body's children
  u8  tg  = term_tag(body);
  u32 vl  = term_val(body);
  u32 use = 0;

  switch (tg) {
    case LAM: {
      auto_dup_go(vl, lvl, base, &use, n, lab, tgt, ext);
      break;
    }
    case DUP: {
      auto_dup_go(vl + 0, lvl, base, &use, n, lab, tgt, ext);
      auto_dup_go(vl + 1, lvl, base, &use, n, lab, tgt, ext);
      break;
    }
    default: {
      u32 ari = term_arity(body);
      for (u32 i = 0; i < ari; i++) {
        auto_dup_go(vl + i, lvl, base, &use, n, lab, tgt, ext);
      }
    }
  }

  // Build dup chain: !d0&=x; !d1&=d0₁; ... body
  Term result = body;
  for (int i = n - 1; i >= 0; i--) {
    Term v   = (i == 0) ? term_new(0, tgt, ext, lvl) : term_new(0, BJ1, lab + i - 1, base + i);
    u64  loc = heap_alloc(2);
    HEAP[loc + 0] = v;
    HEAP[loc + 1] = result;
    result = term_new(0, DUP, lab + i, loc);
  }

  return result;
}
