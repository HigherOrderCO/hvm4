// Seen set and depth limit for coprojection traversal
#define SNF_SEEN_CAP 256
#define SNF_COP_LIMIT 64
static __thread u32 snf_seen[SNF_SEEN_CAP];
static __thread u32 snf_seen_len = 0;
static __thread u32 snf_cop_depth = 0;

static inline int snf_seen_has(u32 loc) {
  for (u32 i = 0; i < snf_seen_len; i++) {
    if (snf_seen[i] == loc) return 1;
  }
  return 0;
}

static inline void snf_seen_add(u32 loc) {
  if (snf_seen_len < SNF_SEEN_CAP) {
    snf_seen[snf_seen_len++] = loc;
  }
}

fn Term snf_go(Term term, u32 depth, int quote);

fn Term snf(Term term, u32 depth, int quote) {
  snf_seen_len = 0;
  snf_cop_depth = 0;
  return snf_go(term, depth, quote);
}

fn Term snf_go(Term term, u32 depth, int quote) {
  if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;

  term = wnf(term);

  if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;

  // Handle coprojections: traverse backing value's subterms
  if (term_tag(term) == CO0 || term_tag(term) == CO1) {
    u32 loc = term_val(term);

    // Skip if already seen or too deep
    if (snf_seen_has(loc) || snf_cop_depth >= SNF_COP_LIMIT) return term;
    snf_seen_add(loc);
    snf_cop_depth++;

    Term val = HEAP[loc];
    if (!term_sub(val)) {
      u32 ari = term_arity(val);
      if (ari > 0) {
        u64 val_loc = term_val(val);
        for (u32 i = 0; i < ari; i++) {
          if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) break;
          HEAP[val_loc + i] = snf_go(HEAP[val_loc + i], depth, quote);
        }
      }
    }

    snf_cop_depth--;
    return term;
  }

  u32 ari = term_arity(term);
  if (ari == 0) return term;

  u64 loc = term_val(term);
  if (term_tag(term) == LAM) {
    Term body = HEAP[loc];
    if (quote) {
      u32 name = depth + 1;
      term = term_new(0, LAM, name, loc);
      heap_subst_var(loc, term_new_nam(name));
    }
    HEAP[loc] = snf_go(body, depth + 1, quote);
  } else if (term_tag(term) == DRY) {
    HEAP[loc + 0] = snf_go(HEAP[loc + 0], depth, quote);
    if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) return term;
    HEAP[loc + 1] = snf_go(HEAP[loc + 1], depth, quote);
  } else {
    for (u32 i = 0; i < ari; i++) {
      if (ITRS_LIMIT > 0 && ITRS >= ITRS_LIMIT) break;
      HEAP[loc + i] = snf_go(HEAP[loc + i], depth, quote);
    }
  }
  return term;
}
