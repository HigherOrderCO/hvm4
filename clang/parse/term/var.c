fn Term parse_term_var(PState *s, u32 depth) {
  parse_skip(s);
  u32 nam = parse_name(s);
  parse_skip(s);
  int side = parse_match(s, "₀") ? 0 : parse_match(s, "₁") ? 1 : -1;
  parse_skip(s);
  int lvl;
  u32 lab;
  u32 cloned;
  int skipped;
  parse_bind_lookup(nam, side, &lvl, &lab, &cloned, &skipped);
  // Fork mode: if we skipped a dup binding and no explicit subscript, retry with fork side
  if (lvl < 0 && skipped && side == -1 && PARSE_FORK_SIDE >= 0) {
    side = PARSE_FORK_SIDE;
    parse_bind_lookup(nam, side, &lvl, &lab, &cloned, &skipped);
  }
  // Error if variable is not found in bindings
  if (lvl < 0) {
    if (side == -1 && skipped) {
      parse_error_var(s, "- dup variable '%s' requires subscript ₀ or ₁\n", nam);
    } else if (side != -1 && skipped) {
      parse_error_var(s, "- non-dup variable '%s' must be used without subscript (₀ or ₁)\n", nam);
    } else {
      parse_error_var(s, "- undefined variable '%s'\n", nam);
    }
  }
  // Handle dynamic dup binding (lab=0xFFFFFF marker)
  // For dynamic dup, X₀ and X₁ become BJV references to nested lambdas
  if (lab == 0xFFFFFF) {
    parse_bind_inc_side(nam, side);
    u32 offset = (side == 1) ? 1 : 0;
    return term_new(0, BJV, 0, (u32)lvl + offset);
  }
  // Track per-side uses for dup bindings and check affinity
  if (lab != 0) {
    u32 prev_uses = parse_bind_inc_side(nam, side);
    if (!cloned && prev_uses > 0) {
      parse_error_affine_side(s, nam, side, prev_uses + 1);
    }
  }
  u32 val = (u32)lvl;
  u8  tag = (side == 0) ? BJ0 : (side == 1) ? BJ1 : BJV;
  return term_new(0, tag, lab, val);
}
