fn PBind* parse_bind_push(u32 name, u32 depth, u32 lab, u32 forked, u32 cloned) {
  PARSE_BINDS[PARSE_BINDS_LEN++] = (PBind){name, depth + 1, lab, forked, cloned, 0, 0, 0};
  return &PARSE_BINDS[PARSE_BINDS_LEN - 1];
}
