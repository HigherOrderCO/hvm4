// Quoted mode converts linked LAM/DUP binders into quoted LAM/DUP binders.
// When `quoted` is set, linked vars (VAR/DP0/DP1) become BJV/BJ0/BJ1 indices
// and the binders store their de Bruijn level in LAM.ext or BJ*. This is used
// by collapse to emit static terms.
#define SNF_SEEN_INIT (1u << 18)

typedef struct {
  U32Set seen;
} SnfState;

fn Term snf_at(u32 loc, u32 depth, u8 quoted, SnfState *st) {
  if (!u32_set_add(&st->seen, loc)) {
    return heap_get(loc);
  }

  Term term = heap_get(loc);
  u8 tag = term_tag(term);
  if (!quoted && (tag == DP0 || tag == DP1)) {
    u32 dup_loc = term_val(term);
    if (dup_loc != 0 && !term_sub_get(heap_get_raw(dup_loc))) {
      if (u32_set_has(&st->seen, dup_loc)) {
        return term;
      }
    }
  }

  term = wnf(term);
  heap_set(loc, term);
  tag = term_tag(term);

  if (!quoted && (tag == DP0 || tag == DP1)) {
    u32 dup_loc = term_val(term);
    if (dup_loc != 0 && !term_sub_get(heap_get_raw(dup_loc))) {
      if (!u32_set_has(&st->seen, dup_loc)) {
        snf_at(dup_loc, 0, quoted, st);
      }
    }
    return term;
  }

  if (quoted && tag == DUP) {
    u32 dup_term_loc = term_val(term);
    u32 lab     = term_ext(term);
    Term val    = heap_get(dup_term_loc + 0);
    Term bod    = heap_get(dup_term_loc + 1);
    u32 level   = depth + 1;
    Term bj0    = term_new(0, BJ0, lab, level);
    Term bj1    = term_new(0, BJ1, lab, level);
    heap_set(dup_term_loc + 0, term_new_sup(lab, bj0, bj1));
    u64 val_loc = heap_alloc(1);
    heap_set(val_loc, val);
    snf_at((u32)val_loc, depth, quoted, st);
    snf_at(dup_term_loc + 1, depth + 1, quoted, st);
    u64 out_loc = heap_alloc(2);
    heap_set(out_loc + 0, heap_get(val_loc));
    heap_set(out_loc + 1, heap_get(dup_term_loc + 1));
    term = term_new(0, DUP, lab, out_loc);
    heap_set(loc, term);
    return term;
  }

  if (quoted) {
    if (tag == BJV || tag == BJ0 || tag == BJ1) {
      return term;
    }
    if (tag == VAR) {
      term = term_new(0, BJV, 0, depth);
      heap_set(loc, term);
      return term;
    }
    if (tag == DP0 || tag == DP1) {
      u8  bj_tag = tag == DP0 ? BJ0 : BJ1;
      u32 lab    = term_ext(term);
      term = term_new(0, bj_tag, lab, depth);
      heap_set(loc, term);
      return term;
    }
  }

  u32 ari = term_arity(term);
  if (ari == 0) {
    return term;
  }
  u32 tloc = term_val(term);
  if (tag == LAM) {
    if (quoted) {
      Term body  = heap_get(tloc);
      u32  level = depth + 1;
      heap_subst_var(tloc, term_new(0, BJV, 0, level));
      u64 tmp_loc = heap_alloc(1);
      heap_set(tmp_loc, body);
      snf_at((u32)tmp_loc, depth + 1, quoted, st);
      heap_set(tloc, heap_get(tmp_loc));
      term = term_new(0, LAM, level, tloc);
      heap_set(loc, term);
    } else {
      snf_at(tloc, depth + 1, quoted, st);
    }
  } else if (tag == DRY) {
    snf_at(tloc + 0, depth, quoted, st);
    snf_at(tloc + 1, depth, quoted, st);
  } else {
    for (u32 i = 0; i < ari; i++) {
      snf_at(tloc + i, depth, quoted, st);
    }
  }
  return term;
}
