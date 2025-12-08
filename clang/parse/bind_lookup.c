fn void parse_bind_lookup(u32 name, u32 depth, int *idx, u32 *lab, u32 *cloned) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    if (PARSE_BINDS[i].name == name) {
      *idx = depth - 1 - PARSE_BINDS[i].depth;
      *lab = PARSE_BINDS[i].lab;
      *cloned = PARSE_BINDS[i].cloned;
      PARSE_BINDS[i].uses++;
      return;
    }
  }
  *idx = -1;
  *lab = 0;
  *cloned = 0;
}

// Increment per-side use count and return previous count
fn u32 parse_bind_inc_side(u32 name, int side) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    if (PARSE_BINDS[i].name == name) {
      if (side == 0) {
        return PARSE_BINDS[i].uses0++;
      } else {
        return PARSE_BINDS[i].uses1++;
      }
    }
  }
  return 0;
}

fn u32 parse_bind_get_uses(void) {
  if (PARSE_BINDS_LEN > 0) {
    return PARSE_BINDS[PARSE_BINDS_LEN - 1].uses;
  }
  return 0;
}

fn u32 parse_bind_get_uses0(void) {
  if (PARSE_BINDS_LEN > 0) {
    return PARSE_BINDS[PARSE_BINDS_LEN - 1].uses0;
  }
  return 0;
}

fn u32 parse_bind_get_uses1(void) {
  if (PARSE_BINDS_LEN > 0) {
    return PARSE_BINDS[PARSE_BINDS_LEN - 1].uses1;
  }
  return 0;
}

fn u32 parse_bind_is_cloned(void) {
  if (PARSE_BINDS_LEN > 0) {
    return PARSE_BINDS[PARSE_BINDS_LEN - 1].cloned;
  }
  return 0;
}
