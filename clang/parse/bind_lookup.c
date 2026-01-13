// Lookup binding by name. If side == -1, skip dup bindings (fall through to outer non-dup).
// Returns lvl = -1 if not found, skipped = 1 if found bind with same name but not applicable.
fn void parse_bind_lookup(u32 name, int side, int *lvl, u32 *lab, u32 *cloned, int *skipped) {
  *skipped = 0;
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    PBind *bind = &PARSE_BINDS[i];
    if (bind->name == name) {
      // Skip dup bindings if no subscript and not in fork mode
      if (side == -1 && bind->lab != 0) {
        *skipped = 1;
        continue;
      }
      // Skip non-dup bindings if subscript or fork mode
      if (side != -1 && bind->lab == 0) {
        *skipped = 1;
        continue;
      }
      // Found the appropriate binding
      *lvl = (int)bind->lvl;
      *lab = bind->lab;
      *cloned = bind->cloned;
      bind->uses++;
      return;
    }
  }
  *lvl = -1;
  *lab = 0;
  *cloned = 0;
}

// Increment per-side use count and return previous count
fn u32 parse_bind_inc_side(u32 name, int side) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    PBind *bind = &PARSE_BINDS[i];
    if (bind->name == name) {
      if (side == 0) {
        return bind->uses0++;
      } else {
        return bind->uses1++;
      }
    }
  }
  return 0;
}

fn u32 parse_bind_get_uses(u32 bid) {
  return PARSE_BINDS[bid].uses;
}
