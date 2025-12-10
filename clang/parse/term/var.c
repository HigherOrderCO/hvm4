fn Term parse_term_var(PState *s, u32 depth) {
  parse_skip(s);
  u32 nam = parse_name(s);
  int idx;
  u32 lab;
  u32 cloned;
  parse_bind_lookup(nam, depth, &idx, &lab, &cloned);
  parse_skip(s);
  int side = parse_match(s, "₀") ? 0 : parse_match(s, "₁") ? 1 : -1;
  // Fork mode: auto-select side for dup variables
  if (side == -1 && lab != 0 && PARSE_FORK_SIDE >= 0) side = PARSE_FORK_SIDE;
  parse_skip(s);
  // Error if variable is not found in bindings
  if (idx < 0) {
    parse_error(s, PERR_UNDEFINED_VAR(nam));
  }
  // Handle dynamic dup binding (lab=0xFFFFFF marker)
  // For dynamic dup, X₀ and X₁ become VAR references to nested lambdas
  // The binding is at depth D, body is parsed at D+2, so idx = (D+2) - 1 - D = 1 for direct ref
  // Structure: @dup(lab, val, λ_.λ_.body) where:
  //   - outer lambda is at depth D (receives CO0 via @dup)
  //   - inner lambda is at depth D+1 (receives CO1 via @dup)
  // From body: outer = idx, inner = idx - 1
  if (lab == 0xFFFFFF) {
    if (side == 0) {
      u32 prev_uses = parse_bind_inc_side(nam, 0);
      if (!cloned && prev_uses > 0) {
        parse_error(s, PERR_AFFINE_SIDE(nam, prev_uses + 1, side));
      }
      return term_new(0, VAR, 0, (u32)idx);  // X₀ → outer lambda
    } else if (side == 1) {
      u32 prev_uses = parse_bind_inc_side(nam, 1);
      if (!cloned && prev_uses > 0) {
        parse_error(s, PERR_AFFINE_SIDE(nam, prev_uses + 1, side));
      }
      return term_new(0, VAR, 0, (u32)(idx - 1));  // X₁ → inner lambda
    } else {
      parse_error(s, PERR_DYN_DUP_REQUIRES_SUBSCRIPT(nam));
    }
  }
  // If dup-bound variable used without subscript (and not in fork mode),
  // try to find an outer non-dup binding with capacity
  if (lab != 0 && side == -1) {
    if (parse_bind_lookup_skip_dup(nam, depth, &idx, &lab, &cloned)) {
      // Found outer binding with capacity - use it as VAR
      return term_new(0, VAR, lab, (u32)idx);
    } else {
      parse_error(s, PERR_DUP_REQUIRES_SUBSCRIPT(nam));
    }
  }
  // Track per-side uses for dup bindings and check affinity
  if (lab != 0 && side >= 0) {
    u32 prev_uses = parse_bind_inc_side(nam, side);
    if (!cloned && prev_uses > 0) {
      parse_error(s, PERR_AFFINE_SIDE(nam, prev_uses + 1, side));
    }
  }
  u32 val = (u32)idx;
  u8  tag = (side == 0) ? CO0 : (side == 1) ? CO1 : VAR;
  return term_new(0, tag, lab, val);
}
