// Auto-dup: wraps a term with N uses of a variable in N-1 dups.
// Example: [x,x,x] becomes !d0&=x; !d1&=d0₁; [d0₀,d1₀,d1₁]

fn void parse_auto_dup_go(u64 loc, u32 idx, u32 *use, u32 n, u32 lab) {
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

  // Shift outer VARs/COs by n
  if ((tag == VAR || tag == CO0 || tag == CO1) && val > idx) {
    HEAP[loc] = term_new(0, tag, term_ext(t), val + n);
    return;
  }

  // Recurse into children
  u32 ari = 0;
  u32 bnd = 0;
  switch (tag) {
    case LAM: {
      ari = 1;
      bnd = 1;
      break;
    }
    case USE: {
      ari = 1;
      break;
    }
    case APP:
    case SUP:
    case MAT:
    case SWI:
    case DRY: {
      ari = 2;
      break;
    }
    case DUP: {
      parse_auto_dup_go(val + 0, idx + 0, use, n, lab);
      parse_auto_dup_go(val + 1, idx + 1, use, n, lab);
      return;
    }
    case C00 ... C16: {
      ari = tag - C00;
      break;
    }
    case OP2:
    case EQL: {
      ari = 2;
      break;
    }
    case DSU:
    case DDU: {
      ari = 3;
      break;
    }
    default: {
      return;
    }
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_go(val + i, idx + bnd, use, n, lab);
  }
}

fn Term parse_auto_dup(Term body, u32 idx, u32 uses) {
  if (uses <= 1) {
    return body;
  }
  u32 n   = uses - 1;
  u32 lab = PARSE_FRESH_LAB;
  PARSE_FRESH_LAB += n;

  // Walk body's children
  u8  tag = term_tag(body);
  u32 val = term_val(body);
  u32 use = 0;
  u32 ari = 0;
  u32 bnd = 0;
  switch (tag) {
    case LAM: {
      ari = 1;
      bnd = 1;
      break;
    }
    case USE: {
      ari = 1;
      break;
    }
    case APP:
    case SUP:
    case MAT:
    case SWI:
    case DRY: {
      ari = 2;
      break;
    }
    case DUP: {
      parse_auto_dup_go(val + 0, idx + 0, &use, n, lab);
      parse_auto_dup_go(val + 1, idx + 1, &use, n, lab);
      ari = 0;
      break;
    }
    case C00 ... C16: {
      ari = tag - C00;
      break;
    }
    case OP2:
    case EQL: {
      ari = 2;
      break;
    }
    case DSU:
    case DDU: {
      ari = 3;
      break;
    }
    default: {
      break;
    }
  }
  for (u32 i = 0; i < ari; i++) {
    parse_auto_dup_go(val + i, idx + bnd, &use, n, lab);
  }

  // Build dup chain: !d0&=x; !d1&=d0₁; ... body
  Term result = body;
  for (int i = n - 1; i >= 0; i--) {
    Term v;
    if (i == 0) {
      v = term_new(0, VAR, 0, idx);
    } else {
      v = term_new(0, CO1, lab + i - 1, 0);
    }
    u64 loc = heap_alloc(2);
    HEAP[loc + 0] = v;
    HEAP[loc + 1] = result;
    result = term_new(0, DUP, lab + i, loc);
  }
  return result;
}
