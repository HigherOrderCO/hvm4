// Auto-dup: wraps a term with N uses of a variable in N-1 dups.
// Example: [x,x,x] becomes !d0&=x; !d1&=d0₁; [d0₀,d1₀,d1₁]
//
// The key insight for shifting: when we traverse INTO a LAM, idx increases.
// The difference (idx - initial_idx) is how deep we've gone into the body.
// - If val < (idx - initial_idx): points to a LAM inside the body → don't shift
// - If val >= (idx - initial_idx): points outside the body → shift

fn void parse_auto_dup_go(u64 loc, u32 idx, u32 initial_idx, u32 *use, u32 n, u32 lab) {
  Term t   = HEAP[loc];
  u8  tag  = term_tag(t);
  u32 val  = term_val(t);

  // Replace target VAR with CO0/CO1
  if (tag == VAR && val == idx) {
    u32 i = (*use)++;
    if (i < n) {
      HEAP[loc] = term_new(0, CO0, lab + i, idx + n - 1 - i);
    } else {
      HEAP[loc] = term_new(0, CO1, lab + n - 1, idx);
    }
    return;
  }

  // Shift if pointing outside the traversed body region
  u32 depth = idx - initial_idx;
  if ((tag == VAR || tag == CO0 || tag == CO1) && val >= depth) {
    HEAP[loc] = term_new(0, tag, term_ext(t), val + n);
    return;
  }

  // Recurse into children
  u32 ari = 0, bnd = 0;
  switch (tag) {
    case LAM: ari = 1; bnd = 1; break;
    case USE: ari = 1; break;
    case APP: case SUP: case MAT: case SWI: case DRY: ari = 2; break;
    case DUP: {
      parse_auto_dup_go(val + 0, idx + 0, initial_idx, use, n, lab);
      parse_auto_dup_go(val + 1, idx + 1, initial_idx, use, n, lab);
      return;
    }
    case C00 ... C16: ari = tag - C00; break;
    case OP2: case EQL: ari = 2; break;
    case DSU: case DDU: ari = 3; break;
    default: return;
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_go(val + i, idx + bnd, initial_idx, use, n, lab);
  }
}

fn Term parse_auto_dup(Term body, u32 idx, u32 uses) {
  if (uses <= 1) return body;
  u32 n   = uses - 1;
  u32 lab = PARSE_FRESH_LAB;
  PARSE_FRESH_LAB += n;

  // Walk body's children (initial_idx = idx at start)
  u8  tag = term_tag(body);
  u32 val = term_val(body);
  u32 use = 0, ari = 0, bnd = 0;
  switch (tag) {
    case LAM: ari = 1; bnd = 1; break;
    case USE: ari = 1; break;
    case APP: case SUP: case MAT: case SWI: case DRY: ari = 2; break;
    case DUP: {
      parse_auto_dup_go(val + 0, idx + 0, idx, &use, n, lab);
      parse_auto_dup_go(val + 1, idx + 1, idx, &use, n, lab);
      ari = 0;
      break;
    }
    case C00 ... C16: ari = tag - C00; break;
    case OP2: case EQL: ari = 2; break;
    case DSU: case DDU: ari = 3; break;
    default: break;
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_go(val + i, idx + bnd, idx, &use, n, lab);
  }

  // Build dup chain: !d0&=x; !d1&=d0₁; ... body
  Term result = body;
  for (int i = n - 1; i >= 0; i--) {
    Term v = (i == 0) ? term_new(0, VAR, 0, idx) : term_new(0, CO1, lab + i - 1, 0);
    u64 loc = heap_alloc(2);
    HEAP[loc + 0] = v;
    HEAP[loc + 1] = result;
    result = term_new(0, DUP, lab + i, loc);
  }
  return result;
}

// Auto-dup for CO0/CO1: same logic but targets CO refs instead of VARs
fn void parse_auto_dup_co_go(u64 loc, u32 idx, u32 *use, u32 n, u32 new_lab, u32 orig_lab, u8 co_tag) {
  Term t   = HEAP[loc];
  u8  tag  = term_tag(t);
  u32 val  = term_val(t);
  u32 ext  = term_ext(t);

  // Replace target CO0/CO1 with new CO0/CO1
  if (tag == co_tag && ext == orig_lab && val == idx) {
    u32 i = (*use)++;
    if (i < n) {
      HEAP[loc] = term_new(0, CO0, new_lab + i, idx + n - 1 - i);
    } else {
      HEAP[loc] = term_new(0, CO1, new_lab + n - 1, idx);
    }
    return;
  }

  // Shift outer refs (for static dup, initial_idx=0 so this is val > idx)
  if ((tag == VAR || tag == CO0 || tag == CO1) && val > idx) {
    HEAP[loc] = term_new(0, tag, ext, val + n);
    return;
  }

  // Recurse into children
  u32 ari = 0, bnd = 0;
  switch (tag) {
    case LAM: ari = 1; bnd = 1; break;
    case USE: ari = 1; break;
    case APP: case SUP: case MAT: case SWI: case DRY: ari = 2; break;
    case DUP: {
      parse_auto_dup_co_go(val + 0, idx + 0, use, n, new_lab, orig_lab, co_tag);
      parse_auto_dup_co_go(val + 1, idx + 1, use, n, new_lab, orig_lab, co_tag);
      return;
    }
    case C00 ... C16: ari = tag - C00; break;
    case OP2: case EQL: ari = 2; break;
    case DSU: case DDU: ari = 3; break;
    default: return;
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_co_go(val + i, idx + bnd, use, n, new_lab, orig_lab, co_tag);
  }
}

fn Term parse_auto_dup_co(Term body, u32 idx, u32 uses, u32 orig_lab, u8 co_tag) {
  if (uses <= 1) return body;
  u32 n   = uses - 1;
  u32 new_lab = PARSE_FRESH_LAB;
  PARSE_FRESH_LAB += n;

  // Walk body's children
  u8  tag = term_tag(body);
  u32 val = term_val(body);
  u32 use = 0, ari = 0, bnd = 0;
  switch (tag) {
    case LAM: ari = 1; bnd = 1; break;
    case USE: ari = 1; break;
    case APP: case SUP: case MAT: case SWI: case DRY: ari = 2; break;
    case DUP: {
      parse_auto_dup_co_go(val + 0, idx + 0, &use, n, new_lab, orig_lab, co_tag);
      parse_auto_dup_co_go(val + 1, idx + 1, &use, n, new_lab, orig_lab, co_tag);
      ari = 0;
      break;
    }
    case C00 ... C16: ari = tag - C00; break;
    case OP2: case EQL: ari = 2; break;
    case DSU: case DDU: ari = 3; break;
    default: break;
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_co_go(val + i, idx + bnd, &use, n, new_lab, orig_lab, co_tag);
  }

  // Build dup chain
  Term result = body;
  for (int i = n - 1; i >= 0; i--) {
    Term v = (i == 0) ? term_new(0, co_tag, orig_lab, idx) : term_new(0, CO1, new_lab + i - 1, 0);
    u64 loc = heap_alloc(2);
    HEAP[loc + 0] = v;
    HEAP[loc + 1] = result;
    result = term_new(0, DUP, new_lab + i, loc);
  }
  return result;
}
